// A bounded, explicitly incomplete discovery export. No proof-completion claim.
#include "collar_discovery_body.inc"

int main(int argc,char**argv){try{
 if(argc!=12||stoull(argv[8])==0)
  throw runtime_error("discovery requires a positive finite node limit");
 string base=argv[3],snapshot=base+".discovery.json";
 if(ifstream(base)||ifstream(snapshot))
  throw runtime_error("refuse to overwrite any prior output");
 int code=bounded_production_entry(argc,argv);
 if(code==0)throw runtime_error("discovery unexpectedly exhausted; use production validation separately");
 // Export only when the unchanged production path stopped at our node budget.
 // Other failures (bad input, memory guard, malformed graph) are not accepted.
 if(calls!=limit||!limit)
  throw runtime_error("not a node-budget discovery stop");
 ofstream out(snapshot);
 if(!out)throw runtime_error("discovery snapshot open failed");
 out<<"{\"schema\":\"incomplete-collar-discovery-v1\""
    <<",\"complete_necessary_outer_search\":false"
    <<",\"complete_full_triangulations\":false"
    <<",\"global_optimality_proved\":false"
    <<",\"N\":"<<n<<",\"B\":"<<b<<",\"calls\":"<<calls
    <<",\"node_limit\":"<<limit<<",\"production_exit_code\":"<<code
    <<",\"weak_graph_count\":"<<collars.size()
    <<",\"weak_graphs\":[";
 bool comma=false;
 for(auto const&[faces,centers]:collars){
  if(comma)out<<",";comma=true;
  out<<"{\"centers\":"<<centers<<",\"faces\":[";
  for(size_t j=0;j<faces.size();j++){if(j)out<<",";out<<faces[j];}
  out<<"]}";
 }
 out<<"]}\n";out.close();
 if(!out)throw runtime_error("discovery snapshot write failed");
 cerr<<"INCOMPLETE DISCOVERY ONLY calls="<<calls<<" weak_graphs="<<collars.size()<<"\n";
 return 0;
}catch(exception const&e){cerr<<"DISCOVERY REJECTED "<<e.what()<<"\n";return 1;}}
