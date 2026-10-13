// Read-only origin guard diagnostic; requests are not complete enumerations.
#include "origin_collar_probe_body.inc"

int main(int argc,char**argv){try{
 if(argc!=3)throw runtime_error("usage: test-cover-origin requests output");
 ifstream input(argv[1]);if(!input)throw runtime_error("origin request open");
 vector<array<uint64_t,5>> answers;
 string line;
 while(getline(input,line)){
  istringstream row(line);int index,F;string flag;
  if(!(row>>index>>n>>b>>flag>>F)||index!=(int)answers.size()||
     n>MAXN||n<b||b<3||F<0||F>MAXF)throw runtime_error("origin request bounds");
  initialize_cover_origin(flag);origin_cover_prunes=0;origin_cover_samples.clear();
  State state;state.next=n;
  for(int i=0;i<b;i++){
   int j=(i+1)%b;state.adjacency[i]|=uint32_t(1)<<j;state.adjacency[j]|=uint32_t(1)<<i;
  }
  uint32_t previous=0;
  for(int f=0;f<F;f++){
   uint64_t face;
   if(!(row>>face)||face<=previous||face>=(uint64_t(1)<<n)||pop(uint32_t(face))!=3)
    throw runtime_error("origin request face");
   previous=face;state.faces[state.count++]=face;
   for(int v=0;v<n;v++)if(face>>v&1)state.adjacency[v]|=uint32_t(face)^(uint32_t(1)<<v);
  }
  string extra;if(row>>extra)throw runtime_error("extra origin request token");
  uint32_t exposed=(uint32_t(1)<<b)-1;
  for(int v=0;v<b;v++)exposed|=state.adjacency[v];
  bool paid=already_cover_origin_paid(state);
  answers.push_back({uint64_t(index),exposed,paid,origin_cover_prunes,origin_cover_samples.size()});
 }
 if(!input.eof())throw runtime_error("origin request read");
 ofstream output(argv[2]);if(!output)throw runtime_error("origin answer open");
 output<<"{\"scope\":\"per-graph actual-cover origin necessity only\",\"answers\":[";
 for(size_t i=0;i<answers.size();i++){
  if(i)output<<",";auto const&a=answers[i];
  output<<"{\"request\":"<<a[0]<<",\"exposed_mask\":"<<a[1]<<",\"cover_obstruction\":"<<a[2]
        <<",\"prune_count\":"<<a[3]<<",\"samples\":"<<a[4]<<"}";
 }
 output<<"]}\n";output.close();if(!output)throw runtime_error("origin answer write");
 return 0;
}catch(exception const&e){cerr<<"REJECTED "<<e.what()<<"\n";return 1;}}
