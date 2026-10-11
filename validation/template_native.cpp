#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>
extern "C" std::uintptr_t TemplateRecords[][12],TransferObservation[18],TransferIndexSeeds[2];
extern "C" void TransferInvoke(void*,std::uintptr_t,std::uintptr_t);
static unsigned char* pointer(std::uintptr_t p){return reinterpret_cast<unsigned char*>(p);}
static std::uintptr_t read(std::uintptr_t p){std::uintptr_t v;std::memcpy(&v,pointer(p),sizeof(v));return v;}
static std::uint64_t next(std::uint64_t& v){v^=v<<13;v^=v>>7;v^=v<<17;return v;}
static constexpr std::uintptr_t expected[]={0x13579bdf,0x2468ace0,0x0badc0de,0x11223344,0x55667788,0x76543210,0x10203040,0x50607080,0x90a0b0c0,0xd0e0f001,0x23456789,0xabcdef01,0x31415926,0x27182818};
int main(){
 FILE* f=nullptr;if(fopen_s(&f,"template-packets.json","w")||!f)return 2;
 std::fputs("[",f);unsigned executions=0;std::uint64_t rng=0xc16347a539102b7ULL;
 for(unsigned fixture=0;fixture<4;++fixture){
  const auto& row=TemplateRecords[fixture];const auto start=row[1],end=row[2],source=row[3],destination=row[4],size=row[5];
  if(size<32||size>200||end<=start)return 3;
  std::vector<unsigned char> code(pointer(start),pointer(end)),blueprint(pointer(source),pointer(source+size));
  std::fprintf(f,"%s{\"layout\":%u,\"start\":%llu,\"end\":%llu,\"source\":%llu,\"destination\":%llu,\"size\":%llu,\"sourceField\":%llu,\"destinationField\":%llu,\"externalPC\":%llu,\"externalField\":%llu,\"body\":%llu,\"bodyEnd\":%llu,\"blueprint\":[",fixture?",":"",fixture,
    static_cast<unsigned long long>(start),static_cast<unsigned long long>(end),static_cast<unsigned long long>(source),static_cast<unsigned long long>(destination),static_cast<unsigned long long>(size),
    static_cast<unsigned long long>(row[6]),static_cast<unsigned long long>(row[7]),static_cast<unsigned long long>(row[8]),static_cast<unsigned long long>(row[9]),static_cast<unsigned long long>(row[10]),static_cast<unsigned long long>(row[11]));
  for(std::uintptr_t i=0;i<size;++i)std::fprintf(f,"%s%u",i?",":"",blueprint[i]);
  std::fputs("],\"macroBytes\":[",f);for(std::uintptr_t i=0;i<code.size();++i)std::fprintf(f,"%s%u",i?",":"",code[i]);
  std::fputs("]",f);
  for(unsigned cf=0;cf<2;++cf)for(unsigned trial=0;trial<48;++trial){
   for(unsigned i=0;i<256;++i)pointer(destination)[i]=static_cast<unsigned char>(next(rng));
   std::vector<unsigned char> before(pointer(destination),pointer(destination+256));
   const auto external=read(row[9]);
   TransferIndexSeeds[0]=static_cast<std::uintptr_t>(next(rng));TransferIndexSeeds[1]=static_cast<std::uintptr_t>(next(rng));
   const auto seed=static_cast<std::uintptr_t>(next(rng));
   FlushInstructionCache(GetCurrentProcess(),pointer(start),end-start);
   for(unsigned repeated=0;repeated<2;++repeated){
    const auto ax=sizeof(void*)==8?read(destination):seed;
    TransferInvoke(pointer(start),seed,cf);
    if(TransferObservation[0]!=ax||TransferObservation[1]!=TransferObservation[17]||(TransferObservation[16]&1)!=0)return 4;
    for(unsigned r=0;r<(sizeof(void*)==8?14u:6u);++r){
     const auto value=r==3?TransferIndexSeeds[0]:r==4?TransferIndexSeeds[1]:expected[r];
     if(TransferObservation[r+2]!=value)return 5;
    }
    if(std::memcmp(pointer(source),blueprint.data(),size)||std::memcmp(pointer(start),code.data(),code.size()))return 6;
    if(std::memcmp(pointer(destination),blueprint.data(),size)||std::memcmp(pointer(destination+size),before.data()+size,256-size))return 7;
    if(read(row[6])!=source||read(row[7])!=destination||read(row[9])!=external)return 8;
    ++executions;
   }
  }
  std::fputs(",\"copied\":[",f);
  for(std::uintptr_t i=0;i<size;++i)std::fprintf(f,"%s%u",i?",":"",pointer(destination)[i]);
  std::fputs("]}",f);
 }
 std::fputs("]\n",f);std::fclose(f);
 std::printf("Template %u-bit: PASS %u executions; 4 forward/backward layouts; complete compiled destination operands/source/destination/code/cursor/GPR/SP/CF/reuse\n",unsigned(sizeof(void*)*8),executions);
 return 0;
}
