// Functional control only; arbitrary states are not triangulation theorems.
#include "pending_degree_probe_body.inc"

int main(int argc,char**argv){try{
 if(argc!=4)throw runtime_error("usage: pending-degree-probe input output flag");
 ifstream input(argv[1]);if(!input)throw runtime_error("probe input open");
 initialize_pending_degree_upper(argv[3]);
 int count;if(!(input>>count)||count<1||count>2000)throw runtime_error("probe count");
 vector<bool> answers;
 for(int index=0;index<count;index++){
  int identity,regions;
  if(!(input>>identity>>n>>b>>regions)||identity!=index||n<3||n>MAXN||
     b<3||b>n||regions<0||regions>MAXN)throw runtime_error("probe header");
  State state;
  for(int v=0;v<n;v++){
   uint64_t adjacency;
   if(!(input>>adjacency)||adjacency>=(uint64_t(1)<<n)||
      (adjacency>>v&1))throw runtime_error("probe adjacency");
   state.adjacency[v]=uint32_t(adjacency);
  }
  for(int v=0;v<n;v++)for(int w=0;w<n;w++)
   if(bool(state.adjacency[v]>>w&1)!=bool(state.adjacency[w]>>v&1))
    throw runtime_error("probe asymmetric adjacency");
  vector<Region> pending;
  for(int j=0;j<regions;j++){
   int inside,length;
   if(!(input>>inside>>length)||inside<0||inside>n||length<2||length>n)
    throw runtime_error("probe region");
   vector<int> boundary;
   for(int k=0;k<length;k++){
    int vertex;if(!(input>>vertex)||vertex<0||vertex>=n)throw runtime_error("probe vertex");
    boundary.push_back(vertex);
   }
   if(set<int>(boundary.begin(),boundary.end()).size()!=boundary.size())
    throw runtime_error("probe repeated region vertex");
   pending.push_back({boundary,inside});
  }
  answers.push_back(pending_degree_upper_impossible(state,pending));
 }
 string extra;if(input>>extra||!input.eof())throw runtime_error("probe extra input");
 ofstream out(argv[2]);if(!out)throw runtime_error("probe output open");
 out<<"{\"functional_control_only\":true,\"answers\":[";
 for(size_t j=0;j<answers.size();j++){if(j)out<<",";out<<(answers[j]?"true":"false");}
 out<<"]";write_pending_degree_upper_summary(out);out<<"}\n";out.close();
 if(!out)throw runtime_error("probe output write");
 return 0;
}catch(exception const&e){cerr<<"REJECTED "<<e.what()<<"\n";return 1;}}
