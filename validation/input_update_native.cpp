// Host capture is outside the exact five-instruction pure input update.
#define NOMINMAX
#include <windows.h>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <stdexcept>
#include <vector>
#include "update.hpp"
static void require(bool v,const char* s){if(!v)throw std::runtime_error(s);}
template<class T> static T get(const void* p){T v;std::memcpy(&v,p,sizeof(v));return v;}
template<class T> static void put(void* p,T v){std::memcpy(p,&v,sizeof(v));}
static std::uint64_t randomWord(std::uint64_t& s){s^=s<<13;s^=s>>7;s^=s<<17;return s;}
static unsigned status(std::uint32_t v){
 unsigned low=v&255U,count=0;for(unsigned i=0;i<8;++i)count+=(low>>i)&1U;
 return (count%2==0?4U:0U)|(v==0?64U:0U)|(v>>31?128U:0U);
}
static void bytes(FILE* out,const unsigned char* p,unsigned size){
 std::fprintf(out,"[");for(unsigned i=0;i<size;++i)std::fprintf(out,i?",%u":"%u",unsigned(p[i]));std::fprintf(out,"]");
}
int main(){try{
 const unsigned span=sizeof(Word)==8?41U:39U;
 require(UpdateMarkerEnd-UpdateMarker==span,"five-instruction length");
 require(UpdateXor-UpdateMarker==(sizeof(Word)==8?27:26),"middle instruction position");
 require(UpdateOwnerEnd-UpdateOwner==sizeof(Word)+(sizeof(Word)==8?2:1),"MOFFS owner length");
 require(UpdatePointer-UpdateOwner==(sizeof(Word)==8?2:1),"full-width owned operand");
 require(UpdateTapeEnd-UpdateTape==10,"DWORD owner length");
 auto address=[](const void* p){return static_cast<unsigned long long>(reinterpret_cast<std::uintptr_t>(p));};
 const Word head=Word(reinterpret_cast<std::uintptr_t>(UpdateTape));
 std::vector<Word> seeds={0,1,2,3,Word(-1),Word(1)<<(sizeof(Word)*8-1),(Word(1)<<(sizeof(Word)*8-1))-1,Word(0x0123456789abcdefULL & std::uint64_t(Word(-1)))};
 std::vector<std::uint32_t> symbols={0,1,2,3,0xffffffffU,0x80000000U,0x7fffffffU,0xabcdef01U};
 std::uint64_t random=0x12345678abcdef01ULL;
 for(unsigned i=0;i<32;++i){symbols.push_back(std::uint32_t(randomWord(random)));if(i<8)seeds.push_back(Word(randomWord(random)));}
 FILE* out=nullptr;require(fopen_s(&out,"input-update-packets.json","w")==0,"packet file");
 std::fprintf(out,"{\"pc\":%llu,\"cursor\":%llu,\"head\":%llu,\"endpoint\":%llu,\"initial\":",
  address(UpdateMarker),address(UpdatePointer),address(UpdateTape),address(UpdateMarkerEnd));
 put<std::uint32_t>(UpdateMask+6,0U);
 bytes(out,UpdateMarker,span);std::fprintf(out,",\"object\":");put<std::uint32_t>(UpdateMask+6,0x80000000U);
 bytes(out,UpdateMarker,span);std::fprintf(out,",\"owners\":[");bytes(out,UpdateOwner,unsigned(UpdateOwnerEnd-UpdateOwner));
 std::fprintf(out,",");bytes(out,UpdateTape,10);std::fprintf(out,"],\"live\":[");
 for(unsigned i=0;i<symbols.size();++i){
  const auto fresh=symbols[(i+13)%symbols.size()];const bool chosen=i%2!=0;
  put<std::uint32_t>(UpdateXor+3,symbols[i]);put<std::uint32_t>(UpdateNew+6,fresh);put<std::uint32_t>(UpdateMask+6,chosen?0xffffffffU:0U);
  if(i)std::fprintf(out,",");
  std::fprintf(out,"{\"old\":%u,\"fresh\":%u,\"chosen\":%s,\"bytes\":",symbols[i],fresh,chosen?"true":"false");
  bytes(out,UpdateMarker,span);std::fprintf(out,"}");
 }
 std::fprintf(out,"]}\n");std::fclose(out);
 unsigned cases=0;
 const auto size=static_cast<std::size_t>(UpdateTapeEnd-UpdateMarker);
 for(Word seed:seeds)for(auto old:symbols)for(auto fresh:symbols)for(unsigned chosen=0;chosen<2;++chosen)for(unsigned cf=0;cf<2;++cf){
  put<Word>(UpdatePointer,head);put<std::uint32_t>(UpdateTape+6,old);
  put<std::uint32_t>(UpdateNew+6,fresh);put<std::uint32_t>(UpdateMask+6,chosen?0xffffffffU:0U);
  for(unsigned reuse=0;reuse<2;++reuse){
   const auto entrySymbol=get<std::uint32_t>(UpdateTape+6);
   const std::uint32_t change=chosen?(entrySymbol^fresh):0U;
   // The proved M13 caller reinitializes this live operand from the current tape.
   put<std::uint32_t>(UpdateXor+3,entrySymbol);
   const std::uint32_t expected=chosen?fresh:old;
   std::vector<unsigned char> before(UpdateMarker,UpdateMarker+size);
   require(FlushInstructionCache(GetCurrentProcess(),UpdateMarker,size)!=0,"flush");
   UpdateEntry(seed,cf);
   const auto* o=UpdateObservation;
   require(o[0]==seed,"full accumulator not restored");require(o[1]==o[RegisterCount],"SP changed");
   for(unsigned i=2;i<RegisterCount;++i)require(o[i]==ExpectedRegisters[i],"GPR changed");
   require((o[RegisterCount+1]&1)==cf,"entry CF");
   require((o[RegisterCount+2]&0x8c5)==status(expected),"defined XOR status flags");
   require((o[RegisterCount+2]&0x400)==(o[RegisterCount+1]&0x400),"direction flag changed");
   require(o[RegisterCount+3]==reinterpret_cast<std::uintptr_t>(UpdateMarkerEnd),"endpoint");
   require(get<Word>(UpdatePointer)==head,"full cursor not restored");
   require(get<std::uint32_t>(UpdateTape+6)==expected,"conditional tape symbol");
   require(get<std::uint32_t>(UpdateXor+3)==change,"actual XOR/AND patched operand");
   for(std::size_t i=0;i<size;++i){
    const auto* p=UpdateMarker+i;if((p>=UpdateTape+6&&p<UpdateTape+10)||(p>=UpdateXor+3&&p<UpdateXor+7))continue;
    require(*p==before[i],"exterior code byte changed");
   }
   ++cases;
  }
 }
 require(cases==204800,"case count");
 std::printf("INPUT UPDATE %u-bit: PASS 204800 cases; full AX/cursor/GPR/SP/defined flags/endpoint/tape/code frame/source-copy reinitialized reuse\n",unsigned(sizeof(Word)*8));
 return 0;
}catch(const std::exception& e){std::fprintf(stderr,"%s\n",e.what());return 1;}}
