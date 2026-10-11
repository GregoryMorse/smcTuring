#include <cstdint>
#include <cstdio>
#include <cstring>
#include <initializer_list>
#include <limits>

using Word = std::uintptr_t;
extern "C" Word __cdecl NativeLegacy(Word seed, Word pointer);
extern "C" Word __cdecl NativeCorrected(Word seed, Word pointer);
extern "C" void* __cdecl GetLegacyField();
extern "C" void* __cdecl GetCorrectedField();
extern "C" void* __cdecl GetTargetField();

static Word readWord(void* p) {
    Word value;
    std::memcpy(&value, p, sizeof(value));
    return value;
}

static void writeWord(void* p, Word value) {
    std::memcpy(p, &value, sizeof(value));
}

static bool check(Word seed, Word value, bool alias, bool corrected) {
    void* label = corrected ? GetCorrectedField() : GetLegacyField();
    void* target = alias ? label : GetTargetField();
    Word pointer = reinterpret_cast<Word>(target);
    Word expected = alias ? pointer : value;
    if (!alias) writeWord(target, value);
    Word actual = corrected ? NativeCorrected(seed, pointer) : NativeLegacy(seed, pointer);
    return actual == expected && readWord(label) == pointer && readWord(target) == expected;
}

int main() {
    const Word max = std::numeric_limits<Word>::max();
    const Word edge[] = {0, 1, 2, 0x7fffffff, 0x80000000, 0xffffffff,
                         max, max >> 1, (max >> 1) + 1};
    unsigned cases = 0;
    for (Word seed : edge) for (Word value : edge)
        for (bool alias : {false, true}) for (bool corrected : {false, true}) {
            if (!check(seed, value, alias, corrected)) {
                std::puts("DEFADDR edge-case failure");
                return 1;
            }
            ++cases;
        }
    std::uint64_t rng = 0x4d6f7273652018ULL;
    for (unsigned i = 0; i < 5000; ++i) {
        rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
        Word seed = static_cast<Word>(rng);
        rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
        Word value = static_cast<Word>(rng);
        for (bool alias : {false, true}) for (bool corrected : {false, true}) {
            if (!check(seed, value, alias, corrected)) {
                std::puts("DEFADDR randomized failure");
                return 1;
            }
            ++cases;
        }
    }
    std::printf("DEFADDR %u-bit: PASS %u cases (legacy/corrected, separate/self alias)\n",
                static_cast<unsigned>(sizeof(Word) * 8), cases);
    return 0;
}
