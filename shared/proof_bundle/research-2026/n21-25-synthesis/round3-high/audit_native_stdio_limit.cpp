// Diagnose the static toolchain's FILE-stream quota without editing any proof.
#include <cerrno>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <memory>
#include <string>
#include <vector>
int main(int argc,char** argv){
 if(argc!=2)return 2;
 int maximum=_getmaxstdio();
 std::vector<std::unique_ptr<std::ofstream>> opened;
 int failure_errno=0;
 for(int i=0;i<maximum+16;i++){
  errno=0;
  auto file=std::make_unique<std::ofstream>(
      std::string(argv[1])+"/stream-"+std::to_string(i)+".fixture",std::ios::binary);
  if(!*file){failure_errno=errno;break;}
  opened.push_back(std::move(file));
 }
 std::cout<<"{\"maxstdio\":"<<maximum<<",\"opened_before_failure\":"<<opened.size()
          <<",\"failure_errno\":"<<failure_errno<<",\"EMFILE\":"<<EMFILE
          <<",\"file_stream_quota_reproduced\":"
          <<((failure_errno==EMFILE&&opened.size()<size_t(maximum))?"true":"false")<<"}\n";
 return failure_errno==EMFILE?0:1;
}
