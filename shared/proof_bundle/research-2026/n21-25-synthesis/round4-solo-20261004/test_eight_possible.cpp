// Read-only diagnostic gate; does not enumerate or certify a whole family.
#include "eight_collar_probe_body.inc"

int main(int argc,char**argv){try{
 if(argc!=4)throw runtime_error("usage: test-eight requests output cap8");
 cap8=stoll(argv[3]);scale=10000000;
 caps[0]=768677;caps[1]=1587443;caps[2]=2546859;screen=true;
 if(cap8<=caps[2]||cap8>=scale/2)throw runtime_error("bad cap8");
 ifstream input(argv[1]);if(!input)throw runtime_error("request open");
 string line;vector<array<int,5>> results;
 while(getline(input,line)){
  istringstream row(line);int index,F;
  if(!(row>>index>>n>>b>>F)||index!=(int)results.size()||b<3||n<b||n>MAXN||F<0||F>MAXF)
   throw runtime_error("request bounds");
  State state;state.next=n;
  for(int i=0;i<b;i++){
   int j=(i+1)%b;
   state.adjacency[i]|=uint32_t(1)<<j;
   state.adjacency[j]|=uint32_t(1)<<i;
  }
  uint32_t previous=0;
  for(int f=0;f<F;f++){
   uint64_t value;
   if(!(row>>value)||value>=(uint64_t(1)<<n)||pop(uint32_t(value))!=3||
      uint32_t(value)<=previous)throw runtime_error("bad request face");
   previous=value;state.faces[state.count++]=value;
   for(int v=0;v<n;v++)if(value>>v&1)
    state.adjacency[v]|=uint32_t(value)^(uint32_t(1)<<v);
  }
  string extra;if(row>>extra)throw runtime_error("extra request column");
  audit_order=false;
  bool old_fast=frozen_three_cap_possible(state),new_fast=possible(state);
  audit_order=true;
  bool old_audit=frozen_three_cap_possible(state),new_audit=possible(state);
  results.push_back({index,old_fast,old_audit,new_fast,new_audit});
 }
 if(!input.eof())throw runtime_error("request read");
 ofstream out(argv[2]);if(!out)throw runtime_error("output open");
 out<<"{\"scope\":\"per-graph necessary-angle diagnostics\",\"results\":[";
 for(size_t i=0;i<results.size();i++){
  if(i)out<<",";auto const&r=results[i];
  out<<"{\"request\":"<<r[0]<<",\"old_fast\":"<<r[1]<<",\"old_audit\":"<<r[2]
     <<",\"eight_fast\":"<<r[3]<<",\"eight_audit\":"<<r[4]<<"}";
 }
 out<<"]}\n";out.close();if(!out)throw runtime_error("output write");
 return 0;
}catch(exception const&e){cerr<<"REJECTED "<<e.what()<<"\n";return 1;}}
