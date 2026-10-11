// The host loads, invokes and observes; only the ten-byte marker is pure.
#define NOMINMAX
#include <windows.h>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <stdexcept>
#include <string>
#include <vector>
#include "terminal.hpp"

static void require(bool value,const char* message) { if(!value) throw std::runtime_error(message); }
static std::uint64_t randomWord(std::uint64_t& state) { state^=state<<13;state^=state>>7;state^=state<<17;return state; }
int main() {
    try {
        std::vector<Word> seeds={0,1,2,3,Word(-1),Word(1)<<(sizeof(Word)*8-1),(Word(1)<<(sizeof(Word)*8-1))-1,Word(0x0123456789abcdefULL & std::uint64_t(Word(-1)))};
        std::uint64_t random=0x12345678abdc9876ULL;
        for(unsigned i=0;i<1024;++i) seeds.push_back(Word(randomWord(random)));
        FILE* packets=nullptr;require(fopen_s(&packets,"terminal-packets.json","w")==0,"cannot write packets");
        std::fprintf(packets,"[");
        const std::array<unsigned char*,2> markers={LiteralMarker,CorrectedMarker};
        for(unsigned mode=0;mode<2;++mode) {
            if(mode) std::fprintf(packets,",");
            std::fprintf(packets,"{\"mode\":%u,\"pc\":%llu,\"bytes\":[",mode,static_cast<unsigned long long>(reinterpret_cast<std::uintptr_t>(markers[mode])));
            for(unsigned i=0;i<10;++i)std::fprintf(packets,i?",%u":"%u",unsigned(markers[mode][i]));
            std::fprintf(packets,"]}");
        }
        std::fprintf(packets,"]\n");std::fclose(packets);
        unsigned literal=0,corrected=0;
        for(unsigned mode=0;mode<2;++mode) {
            auto* marker=mode?CorrectedMarker:LiteralMarker;
            auto* end=mode?CorrectedMarkerEnd:LiteralMarkerEnd;
            auto entry=mode?TerminalCorrected:TerminalLiteral;
            require(end-marker==10,"marker is not ten bytes");
            require(marker[0]==0xc7&&marker[1]==5,"wrong DWORD MOV header");
            std::array<unsigned char,10> original{};std::memcpy(original.data(),marker,10);
            // Snapshot both adjacent host code and the pure packet.
            constexpr unsigned Radius=24;
            for(auto seed:seeds) for(unsigned cf=0;cf<2;++cf) for(unsigned reuse=0;reuse<2;++reuse) {
                // Literal baseline needs restoration after its header self-write.
                if(!mode)std::memcpy(marker,original.data(),10);
                std::array<unsigned char,10+2*Radius> before{};std::memcpy(before.data(),marker-Radius,before.size());
                require(FlushInstructionCache(GetCurrentProcess(),marker-Radius,before.size())!=0,"instruction-cache flush failed");
                entry(seed,cf);
                auto* observed=TerminalObservation;
                require(observed[0]==seed,"accumulator changed");
                require(observed[1]==observed[RegisterCount],"stack changed");
                for(unsigned i=2;i<RegisterCount;++i) require(observed[i]==ExpectedRegisters[i],"other GPR changed");
                require((observed[RegisterCount+1]&1)==cf,"entry carry mismatch");
                require((observed[RegisterCount+2]&0xcd5)==(observed[RegisterCount+1]&0xcd5),"status flags changed");
                require(observed[RegisterCount+3]==reinterpret_cast<std::uintptr_t>(end),"wrong observed endpoint");
                for(unsigned i=0;i<before.size();++i) {
                    const bool overwritten=!mode&&i>=Radius&&i<Radius+4;
                    require((marker-Radius)[i]==(overwritten?0:before[i]),"unexpected code-byte change");
                }
                if(mode) ++corrected;else ++literal;
            }
            if(!mode)std::memcpy(marker,original.data(),10);
        }
        require(literal==4128&&corrected==4128,"unexpected case count");
        std::printf("TERMINAL %u-bit: PASS 4128 typed-original and 4128 corrected cases; GPR/SP/flags/endpoint/code-frame/reuse\n",unsigned(sizeof(Word)*8));
        return 0;
    } catch(const std::exception& e) {std::fprintf(stderr,"%s\n",e.what());return 1;}
}
