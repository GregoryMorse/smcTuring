// Positive current-operand DEFDATA32 execution and unchanged whole code image.
#define NOMINMAX
#include <windows.h>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <stdexcept>
#include <vector>
#include "owner.hpp"
static void require(bool v,const char* s){if(!v)throw std::runtime_error(s);}
static std::uint32_t get(const void* p){std::uint32_t v;std::memcpy(&v,p,4);return v;}
static void put(void* p,std::uint32_t v){std::memcpy(p,&v,4);}
static std::uint64_t randomWord(std::uint64_t& s){s^=s<<13;s^=s>>7;s^=s<<17;return s;}
static void packet(FILE* out,std::uint32_t value){std::fprintf(out,"{\"value\":%u,\"bytes\":[",value);
 for(unsigned i=0;i<10;++i)std::fprintf(out,i?",%u":"%u",unsigned(OwnerMarker[i]));std::fprintf(out,"]}");}
int main(){try{
 require(OwnerMarkerEnd-OwnerMarker==10,"complete instruction length");require(get(OwnerMarker+6)==0,"zero initializer");
 std::vector<Word> seeds={0,1,2,3,Word(-1),Word(1)<<(sizeof(Word)*8-1),(Word(1)<<(sizeof(Word)*8-1))-1,Word(0x0123456789abcdefULL & std::uint64_t(Word(-1)))};
 std::vector<std::uint32_t> values={0,1,2,3,0xffffffffU,0x80000000U,0x7fffffffU,0xabcdef01U};
 std::uint64_t random=0x12345678abcdef01ULL;for(unsigned i=0;i<32;++i){seeds.push_back(Word(randomWord(random)));values.push_back(std::uint32_t(randomWord(random)));}
 FILE* out=nullptr;require(fopen_s(&out,"owner-packets.json","w")==0,"packet file");
 std::fprintf(out,"{\"pc\":%llu,\"endpoint\":%llu,\"initial\":",static_cast<unsigned long long>(reinterpret_cast<std::uintptr_t>(OwnerMarker)),static_cast<unsigned long long>(reinterpret_cast<std::uintptr_t>(OwnerMarkerEnd)));
 packet(out,0);std::fprintf(out,",\"live\":[");
 for(unsigned i=0;i<values.size();++i){put(OwnerMarker+6,values[i]);if(i)std::fprintf(out,",");packet(out,values[i]);}std::fprintf(out,"]}\n");std::fclose(out);
 unsigned cases=0;
 for(Word seed:seeds)for(auto value:values)for(unsigned cf=0;cf<2;++cf){put(OwnerMarker+6,value);
  for(unsigned reuse=0;reuse<2;++reuse){std::array<unsigned char,10> before{};std::memcpy(before.data(),OwnerMarker,10);
   require(FlushInstructionCache(GetCurrentProcess(),OwnerMarker,10)!=0,"flush");OwnerEntry(seed,cf);
   const auto* o=OwnerObservation;require(o[0]==seed,"full AX changed");require(o[1]==o[RegisterCount],"SP changed");
   for(unsigned i=2;i<RegisterCount;++i)require(o[i]==ExpectedRegisters[i],"GPR changed");
   require((o[RegisterCount+1]&1)==cf,"entry CF");require((o[RegisterCount+1]&0xcd5)==(o[RegisterCount+2]&0xcd5),"status flags changed");
   require(o[RegisterCount+3]==reinterpret_cast<std::uintptr_t>(OwnerMarkerEnd),"endpoint");
   require(get(OwnerMarker+6)==value,"live scalar reset");require(std::memcmp(before.data(),OwnerMarker,10)==0,"code memory changed");++cases;}}
 require(cases==6400,"case count");std::printf("DWORD OWNER %u-bit: PASS 6400 cases; live symbol/full AX/GPR/SP/flags/endpoint/whole packet/reuse\n",unsigned(sizeof(Word)*8));return 0;
}catch(const std::exception& e){std::fprintf(stderr,"%s\n",e.what());return 1;}}
