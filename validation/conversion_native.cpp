#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>
#include <algorithm>
extern "C" unsigned char ConversionBegin[],ConversionEnd[],ConversionData[];
extern "C" std::uintptr_t ConversionObservation[18];
extern "C" void ConversionInvoke(void*,std::uintptr_t,std::uintptr_t);
extern "C" unsigned char ConversionRun0[],ConversionStop0[],ConversionSource0[];
extern "C" unsigned char ConversionRun1[],ConversionStop1[],ConversionSource1[];
extern "C" unsigned char ConversionRun2[],ConversionStop2[],ConversionDestination2[];
extern "C" unsigned char ConversionRun3[],ConversionStop3[],ConversionDestination3[];
extern "C" unsigned char ConversionRun4[],ConversionStop4[],ConversionSource4[],ConversionDestination4[];
extern "C" unsigned char ConversionRun5[],ConversionStop5[],ConversionSource5[],ConversionDestination5[];

struct Fixture {const char* name;unsigned char* start;unsigned char* stop;unsigned char* source;unsigned char* destination;};
static const Fixture fixtures[]={
 {"export_before",ConversionRun0,ConversionStop0,ConversionSource0,ConversionData},
 {"export_after",ConversionRun1,ConversionStop1,ConversionSource1,ConversionData},
 {"import_before",ConversionRun2,ConversionStop2,ConversionData,ConversionDestination2},
 {"import_after",ConversionRun3,ConversionStop3,ConversionData,ConversionDestination3},
 {"copy_before_after",ConversionRun4,ConversionStop4,ConversionSource4,ConversionDestination4},
 {"copy_after_before",ConversionRun5,ConversionStop5,ConversionSource5,ConversionDestination5}};
static std::uintptr_t address(const unsigned char* p){return reinterpret_cast<std::uintptr_t>(p);}
static std::uintptr_t read(const unsigned char* p){std::uintptr_t v;std::memcpy(&v,p,sizeof(v));return v;}
static void write(unsigned char* p,std::uintptr_t v){std::memcpy(p,&v,sizeof(v));}
static std::uint64_t random(std::uint64_t& v){v^=v<<13;v^=v>>7;v^=v<<17;return v;}
static constexpr std::uintptr_t expected[]={0x13579bdf,0x2468ace0,0x0badc0de,0x11223344,0x55667788,0x76543210,0x10203040,0x50607080,0x90a0b0c0,0xd0e0f001,0x23456789,0xabcdef01,0x31415926,0x27182818};
int main(){
 FILE* f=nullptr;if(fopen_s(&f,"conversion-packets.json","w")||!f)return 2;
 std::fputs("[",f);unsigned fi=0;
 for(const auto& fixture:fixtures){
  const auto size=address(fixture.stop)-address(fixture.start);
  std::fprintf(f,"%s{\"name\":\"%s\",\"start\":%llu,\"end\":%llu,\"source\":%llu,\"destination\":%llu,\"bytes\":[",fi++?",":"",fixture.name,
   static_cast<unsigned long long>(address(fixture.start)),static_cast<unsigned long long>(address(fixture.stop)),
   static_cast<unsigned long long>(address(fixture.source)),static_cast<unsigned long long>(address(fixture.destination)));
  for(std::uintptr_t i=0;i<size;++i)std::fprintf(f,"%s%u",i?",":"",fixture.start[i]);std::fputs("],\"owners\":[",f);
  unsigned owners=0;const unsigned offset=sizeof(void*)==8?2:1;
  for(auto field:{fixture.source,fixture.destination})if(field!=ConversionData){
   std::fprintf(f,"%s{\"field\":%llu,\"pc\":%llu,\"bytes\":[",owners++?",":"",static_cast<unsigned long long>(address(field)),static_cast<unsigned long long>(address(field)-offset));
   for(unsigned i=0;i<offset+sizeof(void*);++i)std::fprintf(f,"%s%u",i?",":"",(field-offset)[i]);std::fputs("]}",f);
  }
  std::fputs("]}",f);
 }
 std::fputs("]\n",f);std::fclose(f);
 std::vector<std::uintptr_t> words={0,1,2,0x7f,0x80,0xff,0x100,0x7fffffff,0x80000000u,~std::uintptr_t(0),0xaaaaaaaa,0x55555555};
 for(unsigned bit=0;bit<sizeof(void*)*8;++bit){words.push_back(std::uintptr_t(1)<<bit);words.push_back(~(std::uintptr_t(1)<<bit));}
 std::uint64_t rng=0x862974efa831502dULL;for(unsigned i=0;i<384;++i)words.push_back(static_cast<std::uintptr_t>(random(rng)));
 std::sort(words.begin(),words.end());words.erase(std::unique(words.begin(),words.end()),words.end());
 const auto textSize=address(ConversionEnd)-address(ConversionBegin);std::vector<unsigned char> snapshot(textSize);
 unsigned cases=0;
 for(const auto& fixture:fixtures)for(auto value:words)for(unsigned cf=0;cf<2;++cf)for(unsigned rep=0;rep<2;++rep){
  auto seed=static_cast<std::uintptr_t>(random(rng));write(fixture.source,value);write(fixture.destination,static_cast<std::uintptr_t>(random(rng)));
  std::memcpy(snapshot.data(),ConversionBegin,textSize);const auto data=read(ConversionData);
  FlushInstructionCache(GetCurrentProcess(),ConversionBegin,textSize); // Host initialization only.
  for(unsigned call=0;call<2;++call){
   ConversionInvoke(fixture.start,seed,cf);
   if(read(fixture.source)!=value||read(fixture.destination)!=value||ConversionObservation[0]!=seed||ConversionObservation[1]!=ConversionObservation[17]||(ConversionObservation[16]&1)!=cf)return 3;
   const unsigned registers=sizeof(void*)==8?14:6;for(unsigned i=0;i<registers;++i)if(ConversionObservation[i+2]!=expected[i])return 4;
   for(std::uintptr_t i=0;i<textSize;++i){auto p=address(ConversionBegin)+i;if((p<address(fixture.destination)||p>=address(fixture.destination)+sizeof(void*))&&ConversionBegin[i]!=snapshot[i])return 5;}
   if(fixture.destination!=ConversionData&&read(ConversionData)!=data)return 6;
   const unsigned offset=sizeof(void*)==8?2:1;
   for(auto field:{fixture.source,fixture.destination})if(field!=ConversionData){
    if(field[-1]!=0xa3||(offset==2&&field[-2]!=0x48))return 7;
   }
   ++cases;
  }
 }
 std::printf("Conversion %u-bit: PASS %u executions; %zu live words; 6 layouts (source/destination, all GPRs/SP/CF, exact code/data frame, repeated calls)\n",unsigned(sizeof(void*)*8),cases,words.size());
 return 0;
}
