// Native differential validation, with host setup/observation outside purity.
#define NOMINMAX
#include <windows.h>
#include <array>
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <stdexcept>
#include <string>
#include <vector>
#include "kernel.hpp"

extern "C" int PureNativeEntry();
extern "C" unsigned char PureRegisters[], PureHeap[], PureLoopTarget[], PureBoundary[];
extern "C" unsigned char PureKernelStart[];
extern "C" unsigned PureFieldCount;
extern "C" uintptr_t PureFieldAddresses[];

struct Word { uint32_t tag, value; };
using Registers = std::array<Word, 13>;
using Memory = std::vector<Word>;

static void require(bool ok, const std::string& reason) {
    if (!ok) throw std::runtime_error(reason);
}
static uint32_t number(std::ifstream& in) {
    uint32_t result = 0;
    in.read(reinterpret_cast<char*>(&result), sizeof(result));
    require(bool(in), "Truncated suite");
    return result;
}
static Word word(std::ifstream& in) {
    Word result{number(in), number(in)};
    require(result.tag <= 1 && (result.tag || result.value <= 1), "Invalid source word");
    return result;
}
static uintptr_t encode(Word w) {
    if (!w.tag) return uintptr_t(w.value) * stride;
    require(w.value < heapCells, "Source address exceeds finite native capacity");
    return reinterpret_cast<uintptr_t>(PureHeap) + uintptr_t(2 * w.value) * stride;
}
static void put(unsigned char* p, uintptr_t value) { std::memcpy(p, &value, sizeof(value)); }
static uintptr_t get(const unsigned char* p) {
    uintptr_t value;
    std::memcpy(&value, p, sizeof(value));
    return value;
}
static void validateLayout() {
    require(PureHeap == PureRegisters + 13*stride, "Register/heap affine layout");
    std::vector<uintptr_t> fields(PureFieldAddresses, PureFieldAddresses+PureFieldCount);
    for (unsigned r=0; r<13; ++r) fields.push_back(reinterpret_cast<uintptr_t>(PureRegisters+r*stride));
    for (unsigned p=0; p<2*heapCells; ++p) fields.push_back(reinterpret_cast<uintptr_t>(PureHeap+p*stride));
    std::sort(fields.begin(), fields.end());
    const unsigned headerSize = sizeof(uintptr_t)==8 ? 2 : 1;
    for (size_t i=0; i<fields.size(); ++i) {
        require(fields[i] % sizeof(uintptr_t) == 0, "Unaligned operand field");
        const auto* field = reinterpret_cast<const unsigned char*>(fields[i]);
        require(field[-1]==0xa3 && (headerSize==1 || field[-2]==0x48), "Field is not an owned MOFFS operand");
        if (i) require(fields[i-1]+sizeof(uintptr_t) <= fields[i]-headerSize, "Overlapping instruction templates");
    }
    PROCESS_MITIGATION_USER_SHADOW_STACK_POLICY policy{};
    if (GetProcessMitigationPolicy(GetCurrentProcess(), ProcessUserShadowStackPolicy, &policy, sizeof(policy)))
        require(!policy.EnableUserShadowStack, "Code-backed CALL construction requires CET shadow stacks disabled");
}
static bool reference(Registers& registers, Memory& memory) {
    for (const auto& instruction : kernel) {
        if (instruction.kind == 0) {
            registers[instruction.a] = {0, uint32_t(instruction.c)};
            continue;
        }
        const int base = instruction.kind == 1 ? instruction.b : instruction.a;
        const int offset = instruction.kind == 1 ? instruction.c : instruction.b;
        Word b = registers[base], o = registers[offset];
        if (!b.tag || o.tag) return true;
        require(b.value < heapCells, "Reference prefix exceeds finite native capacity");
        const size_t address = 2 * size_t(b.value) + o.value;
        if (instruction.kind == 1) registers[instruction.a] = memory[address];
        else memory[address] = registers[instruction.c];
    }
    return false;
}
static void compare(const Registers& registers, const Memory& memory, const std::string& name, unsigned pass) {
    for (unsigned r = 0; r < registers.size(); ++r)
        require(get(PureRegisters + r * stride) == encode(registers[r]),
                name + ": register " + std::to_string(r) + ", pass " + std::to_string(pass));
    for (size_t p = 0; p < memory.size(); ++p)
        require(get(PureHeap + p * stride) == encode(memory[p]),
                name + ": heap word " + std::to_string(p) + ", pass " + std::to_string(pass));
}
int main(int argc, char** argv) {
    try {
        require(argc == 2, "Usage: pure.exe suite.bin");
        MEMORY_BASIC_INFORMATION info{};
        require(VirtualQuery(PureHeap, &info, sizeof(info)) != 0, "VirtualQuery");
        require((info.Protect & 0xff) == PAGE_EXECUTE_READWRITE ||
                (info.Protect & 0xff) == PAGE_EXECUTE_WRITECOPY,
                "Code storage must be executable and writable");
        validateLayout();
        std::ifstream in(argv[1], std::ios::binary);
        char magic[4]{};
        in.read(magic, 4);
        require(std::memcmp(magic, "SMC1", 4) == 0, "Invalid suite magic");
        const unsigned count = number(in);
        unsigned totalPasses = 0, halts = 0, closedLoops = 0;
        for (unsigned test = 0; test < count; ++test) {
            const unsigned length = number(in);
            require(length <= 1000, "Invalid test name");
            std::string name(length, ' ');
            in.read(name.data(), length);
            const unsigned limit = number(in), expectedFault = number(in), expectedHead = number(in);
            Registers registers{};
            for (auto& r : registers) r = word(in);
            Memory memory(2 * heapCells, Word{0, 0});
            const unsigned updates = number(in);
            for (unsigned i = 0; i < updates; ++i) {
                const unsigned p = number(in);
                require(p < memory.size(), "Invalid heap initializer");
                memory[p] = word(in);
            }
            std::vector<std::pair<unsigned, Word>> expectedTape;
            const unsigned expectedCount = number(in);
            for (unsigned i = 0; i < expectedCount; ++i) {
                const unsigned p = number(in);
                expectedTape.emplace_back(p, word(in));
            }
            const Registers initialRegisters = registers;
            const Memory initialMemory = memory;
            for (unsigned r = 0; r < registers.size(); ++r) put(PureRegisters + r * stride, encode(registers[r]));
            for (size_t p = 0; p < memory.size(); ++p) put(PureHeap + p * stride, encode(memory[p]));
            put(PureLoopTarget, reinterpret_cast<uintptr_t>(PureBoundary));
            require(FlushInstructionCache(GetCurrentProcess(), nullptr, 0) != 0, "FlushInstructionCache before pure entry");
            bool stopped = false;
            for (unsigned pass = 0; pass < limit && !stopped; ++pass) {
                const bool sourceFault = reference(registers, memory);
                const int nativeFault = PureNativeEntry();
                require(nativeFault == int(sourceFault), name + ": terminal mismatch");
                compare(registers, memory, name, pass);
                stopped = sourceFault;
                ++totalPasses;
            }
            require(stopped == bool(expectedFault), name + ": expected halt/prefix mismatch");
            if (stopped) ++halts;
            if (expectedHead != UINT32_MAX)
                require(registers[3].tag == 1 && registers[3].value == expectedHead, name + ": TM head mismatch");
            for (const auto& item : expectedTape)
                require(item.first < memory.size() && memory[item.first].tag == item.second.tag &&
                        memory[item.first].value == item.second.value, name + ": TM output mismatch");
            if (stopped) {
                // Repeat the same halting computation with the genuine pure
                // backedge. There are no host observations between passes.
                for (unsigned r=0; r<initialRegisters.size(); ++r)
                    put(PureRegisters+r*stride, encode(initialRegisters[r]));
                for (size_t p=0; p<initialMemory.size(); ++p)
                    put(PureHeap+p*stride, encode(initialMemory[p]));
                put(PureLoopTarget, reinterpret_cast<uintptr_t>(PureKernelStart));
                require(FlushInstructionCache(GetCurrentProcess(), nullptr, 0) != 0, "FlushInstructionCache before closed loop");
                require(PureNativeEntry()==1, name+": closed loop did not terminate through the guard");
                compare(registers, memory, name+": closed loop", 0);
                ++closedLoops;
            }
        }
        std::printf("Pure SMC %u-bit: PASS %u cases, %u kernel passes, %u terminal cases, %u closed loops\n",
                    unsigned(8 * sizeof(uintptr_t)), count, totalPasses, halts, closedLoops);
        return 0;
    } catch (const std::exception& error) {
        std::fprintf(stderr, "FAIL: %s\n", error.what());
        return 1;
    }
}
