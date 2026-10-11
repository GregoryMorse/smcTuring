// Whole printed x86 branch regression. Host setup/observation is outside purity.
#define NOMINMAX
#include <windows.h>
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <stdexcept>
#include <string>
#include <vector>

static_assert(sizeof(void*) == 4, "Listing 10 is an x86 construction");
struct Observation {
    std::uint32_t eax, esp, ebx, ecx, edx, esi, edi, ebp, flags, beforeSP, beforeBP, outcome;
};
static_assert(sizeof(Observation) == 48, "ASM observation offsets");
enum class Relation { lt, le, eq, ne, gt, ge };
using Entry = std::uint32_t (__cdecl *)(std::uint32_t, std::uint32_t);
struct Fixture {
    const char* name;
    Entry entry;
    bool signedComparison;
    Relation relation;
    unsigned char *x, *y, *mask, *delta, *call, *stack, *fall, *taken, *end;
    Observation* observation;
};
#include "branch.hpp"

static void require(bool ok, const std::string& reason) {
    if (!ok) throw std::runtime_error(reason);
}
static std::uint32_t get(const unsigned char* field) {
    std::uint32_t value;
    std::memcpy(&value, field, 4);
    return value;
}
static void put(unsigned char* field, std::uint32_t value) {
    std::memcpy(field, &value, 4);
}
static std::uint32_t address(const void* pointer) {
    return static_cast<std::uint32_t>(reinterpret_cast<std::uintptr_t>(pointer));
}
static std::int64_t signedValue(std::uint32_t value) {
    return value < 0x80000000u ? std::int64_t(value) : std::int64_t(value)-0x100000000LL;
}
static bool expected(const Fixture& f, std::uint32_t x, std::uint32_t y) {
    const std::int64_t left = f.signedComparison ? signedValue(x) : std::int64_t(x);
    const std::int64_t right = f.signedComparison ? signedValue(y) : std::int64_t(y);
    switch (f.relation) {
    case Relation::lt: return left < right;
    case Relation::le: return left <= right;
    case Relation::eq: return left == right;
    case Relation::ne: return left != right;
    case Relation::gt: return left > right;
    case Relation::ge: return left >= right;
    }
    throw std::runtime_error("Unknown relation");
}
static std::uint32_t randomWord(std::uint64_t& state) {
    state ^= state << 13; state ^= state >> 7; state ^= state << 17;
    return static_cast<std::uint32_t>(state);
}

static bool check(const Fixture& f, std::uint32_t x, std::uint32_t y,
                  std::uint32_t seed, std::uint32_t carry, std::uint64_t& rng) {
    put(f.x+6, x); put(f.y+6, y);
    put(f.mask+6, randomWord(rng)); put(f.delta+6, randomWord(rng)); put(f.call+1, randomWord(rng));
    const auto* begin = reinterpret_cast<const unsigned char*>(f.entry);
    const auto size = static_cast<std::size_t>(address(f.end)-address(begin));
    const std::vector<unsigned char> before(begin, begin+size);
    const bool chosen = expected(f, x, y);
    require(FlushInstructionCache(GetCurrentProcess(), begin, size) != 0, "Host instruction-cache flush failed");
    const auto result = f.entry(seed, carry);
    const auto& o = *f.observation;
    const auto prefix = std::string(f.name)+" x="+std::to_string(x)+" y="+std::to_string(y)+
                        " seed="+std::to_string(seed)+" carry="+std::to_string(carry)+": ";
    require(result == std::uint32_t(chosen) && o.outcome == result, prefix+"wrong branch endpoint");
    require(o.eax == seed, prefix+"accumulator not restored");
    require(o.esp == o.beforeSP && o.ebp == o.beforeBP, prefix+"ESP/EBP not restored");
    require(o.ebx == 0x13579bdfu && o.ecx == 0x2468ace0u && o.edx == 0x0badc0deu &&
            o.esi == 0x11223344u && o.edi == 0x55667788u, prefix+"other GPR changed");
    require((o.flags & 1) == 0, prefix+"continuation CF is not zero");
    require(get(f.x+6) == x && get(f.y+6) == y, prefix+"input operand not restored");
    const auto delta = address(f.taken)-address(f.fall);
    const auto selected = chosen ? delta : 0;
    require(get(f.delta+6) == delta && get(f.mask+6) == selected && get(f.call+1) == selected,
            prefix+"scratch/rel32 result disagrees");
    require(get(f.stack+2) == address(f.stack+6) && get(f.stack+6) == address(f.stack+6),
            prefix+"DEFSTACK address/immediate alias not restored");
    for (std::size_t offset=0; offset<size; ++offset) {
        const auto* position = begin+offset;
        const auto within = [position](const unsigned char* field) {
            return address(position) >= address(field) && address(position) < address(field)+4;
        };
        if (within(f.mask+6) || within(f.delta+6) || within(f.call+1)) continue;
        require(position[0] == before[offset], prefix+"code byte changed outside final scratch fields");
    }
    return chosen;
}

int main() {
    try {
        PROCESS_MITIGATION_USER_SHADOW_STACK_POLICY policy{};
        if (GetProcessMitigationPolicy(GetCurrentProcess(), ProcessUserShadowStackPolicy, &policy, sizeof(policy)))
            require(!policy.EnableUserShadowStack, "Fixture requires CET shadow stacks disabled");
        const std::uint32_t edges[] = {0,1,2,3,0x7ffffffeu,0x7fffffffu,0x80000000u,
                                      0x80000001u,0xfffffffeu,0xffffffffu};
        const std::uint32_t seeds[] = {0,1,0x7fffffffu,0x80000000u,0xfffffffeu,0xffffffffu};
        std::uint64_t rng = 0x4d6f7273652018ULL;
        unsigned total=0;
        for (const auto& f : fixtures) {
            unsigned cases=0, taken=0;
            for (auto x : edges) for (auto y : edges) for (auto seed : seeds)
                for (std::uint32_t carry : {0u,1u}) {
                    taken += check(f,x,y,seed,carry,rng); ++cases;
                }
            for (unsigned i=0; i<2500; ++i) {
                const auto x = randomWord(rng);
                const auto y = (i%32 == 0) ? x : ((i%32 == 1) ? x+1 : randomWord(rng));
                const auto seed = randomWord(rng);
                for (std::uint32_t carry : {0u,1u}) {
                    taken += check(f,x,y,seed,carry,rng); ++cases;
                }
            }
            require(cases == 6200 && taken && taken < cases, "Missing case or branch outcome");
            total += cases;
            std::printf("BRANCH %s: PASS %u cases, %u taken, %u fallthrough\n",f.name,cases,taken,cases-taken);
        }
        require(total == 74400, "Unexpected total");
        std::printf("BRANCH x86: PASS %u cases (12 relations, GPR/ESP/CF/word/code frames)\n",total);
        return 0;
    } catch (const std::exception& e) {
        std::fprintf(stderr,"BRANCH FAIL: %s\n",e.what());
        return 1;
    }
}
