#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <wincrypt.h>
#include <cstdint>
#include <vector>
#include <algorithm>
#include <io.h>
#include <cstring>
#include <cstdio>
#include "MinHook.h"

#pragma comment(lib, "Advapi32.lib")

static const BYTE CONST_KEY[32] = {
    'f','i','x','e','d','_','k','e','y','_','f','o','r','_',
    'm','a','s','k','i','n','g','_','s','t','r','i','n','g',
    's','_','k','e'
};

// ===== 전역 =====
static HMODULE g_hDll = nullptr;
static HANDLE  g_hFile = nullptr;
static HANDLE  g_hMap = nullptr;
static void* g_view = nullptr;
static BYTE* g_blob = nullptr;
static SIZE_T  g_blobLen = 0;

#pragma pack(push,1)
struct MTAB_TRAILER { char magic[4]; uint64_t size; };
struct MaskEntry { uint64_t off; uint32_t len; };
#pragma pack(pop)

static const MaskEntry* g_entries = nullptr;
static uint32_t         g_count = 0;
static uint64_t         g_maxMaskEnd = 0;
static HCRYPTPROV g_hProv = 0;
__declspec(thread) static int t_depth = 0;

// ===== 함수 선언 =====
using ReadFile_t = BOOL(WINAPI*)(HANDLE, LPVOID, DWORD, LPDWORD, LPOVERLAPPED);
using MapViewOfFile_t = LPVOID(WINAPI*)(HANDLE, DWORD, DWORD, DWORD, SIZE_T);
using MapViewOfFileEx_t = LPVOID(WINAPI*)(HANDLE, DWORD, DWORD, DWORD, SIZE_T, LPVOID);
using Fread_t = size_t(__cdecl*)(void*, size_t, size_t, FILE*);
using _read_t = int(__cdecl*)(int fd, void* buf, unsigned int count);
using CreateFileMappingA_t = HANDLE(WINAPI*)(HANDLE, LPSECURITY_ATTRIBUTES, DWORD, DWORD, DWORD, LPCSTR);

static ReadFile_t g_orig_ReadFile = nullptr;
static MapViewOfFile_t g_orig_MapViewOfFile = nullptr;
static MapViewOfFileEx_t g_orig_MapViewOfFileEx = nullptr;
static Fread_t g_orig_fread = nullptr;
static _read_t g_orig_read_ucrt = nullptr;
static _read_t g_orig_read_msvc = nullptr;
static _read_t g_orig_read_apis = nullptr;
static CreateFileMappingA_t g_orig_CreateFileMappingA = nullptr;

// ===== Crypto 초기화 및 keystream =====

static bool InitCrypto() {
    if (g_hProv) return true;
    if (!CryptAcquireContextW(&g_hProv, nullptr, nullptr, PROV_RSA_AES, CRYPT_VERIFYCONTEXT)) {
        g_hProv = 0;
        return false;
    }
    return true;
}

static bool DeriveKeystream(uint64_t start, size_t length, BYTE* out) {
    if (length == 0) return true;
    if (!out) return false;
    if (!InitCrypto()) return false;

    BYTE start_bytes[8];
    uint64_t tmp = start;
    for (int i = 7; i >= 0; --i) {
        start_bytes[i] = (BYTE)(tmp & 0xFFu);
        tmp >>= 8;
    }

    DWORD counter = 0;
    size_t produced = 0;

    while (produced < length) {
        HCRYPTHASH hHash = 0;
        if (!CryptCreateHash(g_hProv, CALG_SHA_256, 0, 0, &hHash)) {
            return false;
        }

        if (!CryptHashData(hHash, CONST_KEY, (DWORD)sizeof(CONST_KEY), 0)) {
            CryptDestroyHash(hHash);
            return false;
        }

        if (!CryptHashData(hHash, start_bytes, (DWORD)sizeof(start_bytes), 0)) {
            CryptDestroyHash(hHash);
            return false;
        }

        BYTE ctr_bytes[4];
        ctr_bytes[0] = (BYTE)((counter >> 24) & 0xFF);
        ctr_bytes[1] = (BYTE)((counter >> 16) & 0xFF);
        ctr_bytes[2] = (BYTE)((counter >> 8) & 0xFF);
        ctr_bytes[3] = (BYTE)(counter & 0xFF);
        if (!CryptHashData(hHash, ctr_bytes, 4, 0)) {
            CryptDestroyHash(hHash);
            return false;
        }

        BYTE digest[32];
        DWORD digestLen = sizeof(digest);
        if (!CryptGetHashParam(hHash, HP_HASHVAL, digest, &digestLen, 0)) {
            CryptDestroyHash(hHash);
            return false;
        }
        CryptDestroyHash(hHash);

        size_t remain = length - produced;
        size_t chunk = (digestLen < remain) ? (size_t)digestLen : remain;
        std::memcpy(out + produced, digest, chunk);
        produced += chunk;

        counter += 1;
    }

    return true;
}

static bool EncDecInPlace(uint64_t start, BYTE* data, size_t length) {
    if (!data || length == 0) return true;
    std::vector<BYTE> ks(length);
    if (!DeriveKeystream(start, length, ks.data())) {
        return false;
    }
    for (size_t i = 0; i < length; ++i) {
        data[i] ^= ks[i];
    }
    return true;
}

static inline bool Intersect(uint64_t a0, uint64_t a1, uint64_t b0, uint64_t b1, uint64_t& s, uint64_t& e) {
    s = (a0 > b0) ? a0 : b0;
    e = (a1 < b1) ? a1 : b1;
    return s < e;
}

static void ApplyEncDecForRange(BYTE* baseBuf, uint64_t base_off, SIZE_T len) {
    if (!baseBuf || len == 0 || !g_entries || g_count == 0) return;

    uint64_t range0 = base_off;
    uint64_t range1 = base_off + (uint64_t)len;

    struct Sub { size_t r0; size_t r1; };
    std::vector<Sub> subs;
    subs.reserve(4);

    for (uint32_t i = 0; i < g_count; ++i) {
        uint64_t ent0 = g_entries[i].off;
        uint64_t ent1 = ent0 + (uint64_t)g_entries[i].len;
        uint64_t s0, s1;
        if (Intersect(range0, range1, ent0, ent1, s0, s1)) {
            size_t rel0 = (size_t)(s0 - range0);
            size_t rel1 = (size_t)(s1 - range0);
            if (rel1 > rel0 && rel1 <= len) {
                subs.push_back(Sub{ rel0, rel1 });
            }
        }
    }

    if (subs.empty()) return;

    std::sort(subs.begin(), subs.end(), [](const Sub& a, const Sub& b) { return a.r0 < b.r0; });

    std::vector<Sub> merged;
    merged.push_back(subs[0]);
    for (size_t i = 1; i < subs.size(); ++i) {
        Sub& back = merged.back();
        if (subs[i].r0 <= back.r1) {
            if (subs[i].r1 > back.r1) back.r1 = subs[i].r1;
        }
        else {
            merged.push_back(subs[i]);
        }
    }

    for (const Sub& m : merged) {
        size_t start = m.r0;
        size_t end = m.r1;
        if (end <= start || end > len) continue;
        size_t segLen = end - start;

        BYTE* segPtr = baseBuf + start;
        uint64_t absOff = base_off + (uint64_t)start;
        EncDecInPlace(absOff, segPtr, segLen);
    }
}


static LPVOID WINAPI MapViewOfFileEx_detour(HANDLE hFileMappingObject, DWORD dwDesiredAccess, DWORD dwFileOffsetHigh, DWORD dwFileOffsetLow, SIZE_T dwNumberOfBytesToMap, LPVOID lpBaseAddress) {
    if (g_orig_MapViewOfFileEx) {
        LPVOID v = g_orig_MapViewOfFileEx(hFileMappingObject, dwDesiredAccess, dwFileOffsetHigh, dwFileOffsetLow, dwNumberOfBytesToMap, lpBaseAddress);
        if (v && g_entries && g_count) {
            uint64_t off = ((uint64_t)dwFileOffsetHigh << 32) | (uint64_t)dwFileOffsetLow;
            SIZE_T effectiveLen = dwNumberOfBytesToMap;
            ApplyEncDecForRange((BYTE*)v, off, effectiveLen);
        }
        return v;
    }
    return nullptr;
}


static BOOL WINAPI ReadFile_detour(HANDLE hFile, LPVOID lpBuffer, DWORD nNumberOfBytesToRead, LPDWORD lpNumberOfBytesRead, LPOVERLAPPED lpOverlapped) {
    if (!g_orig_ReadFile) return FALSE;
    LARGE_INTEGER curPos{};
    bool gotPos = !!SetFilePointerEx(hFile, { 0 }, &curPos, FILE_CURRENT);

    BOOL ret = g_orig_ReadFile(hFile, lpBuffer, nNumberOfBytesToRead, lpNumberOfBytesRead, lpOverlapped);
    if (ret && gotPos && lpBuffer && lpNumberOfBytesRead && *lpNumberOfBytesRead > 0) {
        ApplyEncDecForRange((BYTE*)lpBuffer, (uint64_t)curPos.QuadPart, (SIZE_T)*lpNumberOfBytesRead);
    }
    return ret;
}

static LPVOID WINAPI MapViewOfFile_detour(HANDLE hFileMappingObject, DWORD dwDesiredAccess, DWORD dwFileOffsetHigh, DWORD dwFileOffsetLow, SIZE_T dwNumberOfBytesToMap) {
    if (!g_orig_MapViewOfFile) return nullptr;
    LPVOID v = g_orig_MapViewOfFile(hFileMappingObject, dwDesiredAccess, dwFileOffsetHigh, dwFileOffsetLow, dwNumberOfBytesToMap);
    if (v && g_entries && g_count) {
        uint64_t off = ((uint64_t)dwFileOffsetHigh << 32) | (uint64_t)dwFileOffsetLow;
        SIZE_T effectiveLen = dwNumberOfBytesToMap;
        ApplyEncDecForRange((BYTE*)v, off, effectiveLen);
    }
    return v;
}


static size_t __cdecl fread_detour(void* buffer, size_t size, size_t count, FILE* stream) {
    if (!g_orig_fread) return 0;
    long long pos = _ftelli64(stream); // capture start offset
    size_t ret = g_orig_fread(buffer, size, count, stream);
    if (ret > 0 && pos >= 0) {
        ApplyEncDecForRange((BYTE*)buffer, (uint64_t)pos, (SIZE_T)(ret * size));
    }
    return ret;
}


static int __cdecl _read_detour_ucrt(int fd, void* buf, unsigned int count) {
    if (g_orig_read_ucrt) {
        int ret = g_orig_read_ucrt(fd, buf, count);
        if (ret > 0) {
            ApplyEncDecForRange((BYTE*)buf, (uint64_t)_lseeki64(fd, 0, SEEK_CUR), (SIZE_T)ret);
        }
        return ret;
    }
    return -1;
}


static int __cdecl _read_detour_msvc(int fd, void* buf, unsigned int count) {
    if (g_orig_read_msvc) {
        int ret = g_orig_read_msvc(fd, buf, count);
        if (ret > 0) {
            ApplyEncDecForRange((BYTE*)buf, (uint64_t)_lseeki64(fd, 0, SEEK_CUR), (SIZE_T)ret);
        }
        return ret;
    }
    return -1;
}


static int __cdecl _read_detour_apis(int fd, void* buf, unsigned int count) {
    if (g_orig_read_apis) {
        int ret = g_orig_read_apis(fd, buf, count);
        if (ret > 0) {
            ApplyEncDecForRange((BYTE*)buf, (uint64_t)_lseeki64(fd, 0, SEEK_CUR), (SIZE_T)ret);
        }
        return ret;
    }
    return -1;
}


static HANDLE WINAPI CreateFileMappingA_detour(HANDLE hFile, LPSECURITY_ATTRIBUTES lpAttributes, DWORD flProtect, DWORD dwMaximumSizeHigh, DWORD dwMaximumSizeLow, LPCSTR lpName) {
    if (g_orig_CreateFileMappingA) {
        return g_orig_CreateFileMappingA(hFile, lpAttributes, flProtect, dwMaximumSizeHigh, dwMaximumSizeLow, lpName);
    }
    return nullptr;
}


// ===== MapOverlayBlob =====
static bool MapOverlayBlob() {
    wchar_t path[MAX_PATH];
    DWORD n = GetModuleFileNameW(g_hDll, path, MAX_PATH);
    if (!n) return false;

    HANDLE hf = CreateFileW(path, GENERIC_READ,
        FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
        nullptr, OPEN_EXISTING, 0, nullptr);
    if (hf == INVALID_HANDLE_VALUE) return false;

    LARGE_INTEGER li;
    if (!GetFileSizeEx(hf, &li) || (uint64_t)li.QuadPart < sizeof(MTAB_TRAILER)) {
        CloseHandle(hf); return false;
    }

    MTAB_TRAILER tr{};
    LARGE_INTEGER pos; pos.QuadPart = li.QuadPart - (LONGLONG)sizeof(tr);
    if (!SetFilePointerEx(hf, pos, nullptr, FILE_BEGIN)) { CloseHandle(hf); return false; }
    DWORD br = 0; if (!ReadFile(hf, &tr, sizeof(tr), &br, nullptr) || br != sizeof(tr)) { CloseHandle(hf); return false; }
    if (memcmp(tr.magic, "MTAB", 4) != 0 || tr.size == 0) { CloseHandle(hf); return false; }

    uint64_t fsz = (uint64_t)li.QuadPart;
    uint64_t blobStart = fsz - sizeof(MTAB_TRAILER) - tr.size;
    if (blobStart > fsz) { CloseHandle(hf); return false; }

    HANDLE hm = CreateFileMappingW(hf, nullptr, PAGE_READONLY, 0, 0, nullptr);
    if (!hm) { CloseHandle(hf); return false; }

    SYSTEM_INFO si; GetSystemInfo(&si);
    uint64_t gran = si.dwAllocationGranularity ? si.dwAllocationGranularity : 65536;
    uint64_t mapStart = (blobStart / gran) * gran;
    SIZE_T   delta = (SIZE_T)(blobStart - mapStart);
    SIZE_T   need = delta + (SIZE_T)tr.size;

    DWORD offHi = (DWORD)(mapStart >> 32);
    DWORD offLo = (DWORD)(mapStart & 0xFFFFFFFF);

    void* view = MapViewOfFile(hm, FILE_MAP_READ, offHi, offLo, need);
    if (!view) { CloseHandle(hm); CloseHandle(hf); return false; }

    g_hFile = hf; g_hMap = hm; g_view = view;
    g_blob = (BYTE*)view + delta;
    g_blobLen = (SIZE_T)tr.size;
    return true;
}

// ===== ParseTable =====
static bool ParseTable() {
    if (!g_blob || g_blobLen < sizeof(uint32_t)) return false;
    const BYTE* p = g_blob;
    uint32_t cnt = *(const uint32_t*)p;
    p += sizeof(uint32_t);
    SIZE_T need = sizeof(uint32_t) + (SIZE_T)cnt * sizeof(MaskEntry);
    if (g_blobLen < need) return false;
    g_count = cnt;
    g_entries = (const MaskEntry*)p;

    g_maxMaskEnd = 0;
    for (uint32_t i = 0; i < g_count; ++i) {
        uint64_t ent0 = g_entries[i].off;
        uint64_t ent1 = ent0 + (uint64_t)g_entries[i].len;
        if (ent1 > g_maxMaskEnd) g_maxMaskEnd = ent1;
    }

    return true;
}

// ===== UnmapOverlay =====
static void UnmapOverlay() {
    if (g_view) {
        UnmapViewOfFile(g_view);
        g_view = nullptr;
    }
    if (g_hMap) {
        CloseHandle(g_hMap);
        g_hMap = nullptr;
    }
    if (g_hFile) {
        CloseHandle(g_hFile);
        g_hFile = nullptr;
    }
    g_blob = nullptr;
    g_blobLen = 0;
    g_entries = nullptr;
    g_count = 0;
    g_maxMaskEnd = 0;
}

// ===== 후킹 설치 =====
static void InstallHooks() {
    if (MH_Initialize() != MH_OK) return;

    auto hookInModule = [](const wchar_t* modName, const char* name, LPVOID detour, void** pOrig) {
        if (*pOrig) return;
        HMODULE m = GetModuleHandleW(modName);
        if (!m) return;
        FARPROC p = GetProcAddress(m, name);
        if (p && MH_CreateHook((LPVOID)p, detour, pOrig) == MH_OK) {
            MH_EnableHook((LPVOID)p);
        }
        };

    hookInModule(L"kernel32.dll", "ReadFile", (LPVOID)&ReadFile_detour, (void**)&g_orig_ReadFile);
    hookInModule(L"kernel32.dll", "MapViewOfFile", (LPVOID)&MapViewOfFile_detour, (void**)&g_orig_MapViewOfFile);
    hookInModule(L"kernel32.dll", "MapViewOfFileEx", (LPVOID)&MapViewOfFileEx_detour, (void**)&g_orig_MapViewOfFileEx);
    hookInModule(L"kernel32.dll", "CreateFileMappingA", (LPVOID)&CreateFileMappingA_detour, (void**)&g_orig_CreateFileMappingA);

    // stdio: try ucrtbase first, then api-set, then msvcrt
    const wchar_t* freadMods[] = { L"ucrtbase.dll", L"api-ms-win-crt-stdio-l1-1-0.dll", L"msvcrt.dll" };
    for (const auto* m : freadMods) {
        hookInModule(m, "fread", (LPVOID)&fread_detour, (void**)&g_orig_fread);
        if (g_orig_fread) break;
    }

    // low-level _read
    const wchar_t* readMods[] = { L"ucrtbase.dll", L"api-ms-win-crt-io-l1-1-0.dll", L"msvcrt.dll" };
    for (const auto* m : readMods) {
        hookInModule(m, "_read", (LPVOID)&_read_detour_ucrt, (void**)&g_orig_read_ucrt);
        if (g_orig_read_ucrt) break;
    }
}

static void UninstallHooks() {
    MH_DisableHook(MH_ALL_HOOKS);
    MH_Uninitialize();
    if (g_hProv) {
        CryptReleaseContext(g_hProv, 0);
        g_hProv = 0;
    }
}

extern "C" __declspec(dllexport) void __stdcall DummyExport() {}

BOOL APIENTRY DllMain(HMODULE h, DWORD reason, LPVOID) {
    if (reason == DLL_PROCESS_ATTACH) {
        g_hDll = h;
        DisableThreadLibraryCalls(h);

        if (MapOverlayBlob()) {
            ParseTable();
        }
        InstallHooks();
    }
    else if (reason == DLL_PROCESS_DETACH) {
        UninstallHooks();
        UnmapOverlay();
    }
    return TRUE;
}
