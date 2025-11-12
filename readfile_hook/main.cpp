// read_hook.dll
// - overlay mmap + table parse + fread hook
// - partial/edge overlaps handled by merging subranges (XOR once)

#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <cstdint>
#include <cstdio>
#include <vector>
#include <algorithm>

#include "MinHook.h"

// ===== 고정 XOR 키 =====
#define XOR_KEY 0x5A

// ===== 전역 =====
static HMODULE g_hDll = nullptr;

// overlay mmap 상태
static HANDLE  g_hFile = nullptr;
static HANDLE  g_hMap = nullptr;
static void* g_view = nullptr;      // 맵 시작
static BYTE* g_blob = nullptr;      // BLOB 시작
static SIZE_T  g_blobLen = 0;

// 테이블 뷰
#pragma pack(push,1)
struct MTAB_TRAILER { char magic[4]; uint64_t size; };
struct MaskEntry { uint64_t off; uint32_t len; };
#pragma pack(pop)

static const MaskEntry* g_entries = nullptr;
static uint32_t         g_count = 0;

// 재진입 가드
__declspec(thread) static int t_depth = 0;

// fread 원본
using fread_t = size_t(__cdecl*)(void*, size_t, size_t, FILE*);
static fread_t g_orig_fread_ucrt = nullptr;
static fread_t g_orig_fread_msvcrt = nullptr;
static fread_t g_orig_fread_apiset = nullptr;

// ===== 유틸 =====
static void UnmapOverlay() {
    if (g_view) { UnmapViewOfFile(g_view); g_view = nullptr; }
    if (g_hMap) { CloseHandle(g_hMap); g_hMap = nullptr; }
    if (g_hFile) { CloseHandle(g_hFile); g_hFile = nullptr; }
    g_blob = nullptr; g_blobLen = 0; g_entries = nullptr; g_count = 0;
}

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

    // 파일 끝의 트레일러 읽기
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

static bool ParseTable() {
    if (!g_blob || g_blobLen < sizeof(uint32_t)) return false;
    const BYTE* p = g_blob;
    uint32_t cnt = *(const uint32_t*)p; p += sizeof(uint32_t);
    SIZE_T need = sizeof(uint32_t) + (SIZE_T)cnt * sizeof(MaskEntry);
    if (g_blobLen < need) return false;
    g_count = cnt;
    g_entries = (const MaskEntry*)p;
    return true;
}

static inline void XorRange(BYTE* base, size_t n) {
    for (size_t i = 0; i < n; ++i) base[i] ^= XOR_KEY;
}

// [a0,a1)∩[b0,b1) → [s,e) 반환, 없으면 false
static inline bool Intersect(uint64_t a0, uint64_t a1, uint64_t b0, uint64_t b1, uint64_t& s, uint64_t& e) {
    s = (a0 > b0) ? a0 : b0;
    e = (a1 < b1) ? a1 : b1;
    return s < e;
}

// fread 공통 래퍼: 부분/경계 겹침 모두 처리(병합 후 1회 XOR)
static size_t DoFread(fread_t orig, void* ptr, size_t es, size_t cnt, FILE* s) {
    if (!orig) return 0;
    if (++t_depth > 1) { size_t r = orig(ptr, es, cnt, s); --t_depth; return r; }

    long long off_ll = _ftelli64(s);
    size_t ret = orig(ptr, es, cnt, s);
    uint64_t br = (uint64_t)ret * (uint64_t)es;

    if (br && off_ll >= 0 && g_entries && g_count) {
        uint64_t read0 = (uint64_t)off_ll;
        uint64_t read1 = read0 + br;

        // 겹치는 subrange들을 수집(버퍼 상대 오프셋)
        struct Sub { size_t r0; size_t r1; };
        std::vector<Sub> subs; subs.reserve(4);
        for (uint32_t i = 0; i < g_count; ++i) {
            uint64_t ent0 = g_entries[i].off;
            uint64_t ent1 = ent0 + (uint64_t)g_entries[i].len;
            uint64_t s0, s1;
            if (Intersect(read0, read1, ent0, ent1, s0, s1)) {
                size_t rel0 = (size_t)(s0 - read0);
                size_t rel1 = (size_t)(s1 - read0);
                subs.push_back(Sub{ rel0, rel1 });
            }
        }

        if (!subs.empty()) {
            // 정렬 후 병합(중첩/인접 구간 합치기)
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
            // 병합된 각 구간에 대해 XOR 1회 적용
            BYTE* b = (BYTE*)ptr;
            for (const Sub& m : merged) {
                size_t len = m.r1 - m.r0;
                XorRange(b + m.r0, len);
            }
        }
    }

    --t_depth;
    return ret;
}

// detours
static size_t __cdecl fread_detour_ucrt(void* p, size_t es, size_t c, FILE* s) {
    return DoFread(g_orig_fread_ucrt, p, es, c, s);
}
static size_t __cdecl fread_detour_msvcrt(void* p, size_t es, size_t c, FILE* s) {
    return DoFread(g_orig_fread_msvcrt, p, es, c, s);
}
static size_t __cdecl fread_detour_apiset(void* p, size_t es, size_t c, FILE* s) {
    return DoFread(g_orig_fread_apiset, p, es, c, s);
}

// 후킹 설치
static void InstallFreadHooks() {
    if (MH_Initialize() != MH_OK) return;

    auto hookOne = [](HMODULE m, const char* name, LPVOID detour, void** pOrig) {
        if (!m) return;
        FARPROC p = GetProcAddress(m, name);
        if (!p) return;
        if (MH_CreateHook((LPVOID)p, detour, pOrig) == MH_OK) {
            MH_EnableHook((LPVOID)p);
        }
        };

    HMODULE hucrt = GetModuleHandleW(L"ucrtbase.dll");
    HMODULE hmsv = GetModuleHandleW(L"msvcrt.dll");
    HMODULE happi = GetModuleHandleW(L"api-ms-win-crt-stdio-l1-1-0.dll");

    hookOne(hucrt, "fread", (LPVOID)&fread_detour_ucrt, (void**)&g_orig_fread_ucrt);
    hookOne(hmsv, "fread", (LPVOID)&fread_detour_msvcrt, (void**)&g_orig_fread_msvcrt);
    hookOne(happi, "fread", (LPVOID)&fread_detour_apiset, (void**)&g_orig_fread_apiset);
}

static void UninstallHooks() {
    MH_DisableHook(MH_ALL_HOOKS);
    MH_Uninitialize();
}

// Dummy export (withdll.exe 등)
extern "C" __declspec(dllexport) void __stdcall DummyExport() {}

BOOL APIENTRY DllMain(HMODULE h, DWORD reason, LPVOID) {
    if (reason == DLL_PROCESS_ATTACH) {
        g_hDll = h;
        DisableThreadLibraryCalls(h);

        // 1) 오버레이 mmap
        if (MapOverlayBlob()) {
            // 2) 테이블 파싱
            ParseTable();
        }
        // 3) fread 후킹
        InstallFreadHooks();
    }
    else if (reason == DLL_PROCESS_DETACH) {
        UninstallHooks();
        UnmapOverlay();
    }
    return TRUE;
}
