// Complete fixed-collar restricted recursion control, NOT a full boundary family.
#include "origin_collar_probe_body.inc"

int main(int argc,char**argv){try{
 if(argc!=5)throw runtime_error("usage: seed-origin input output flag slab");
 ifstream input(argv[1]);if(!input)throw runtime_error("seed open");
 int centers,F,H;
 if(!(input>>n>>b>>centers>>F)||n!=25||b<3||b>n||centers<b||centers>n||F<1||F>MAXF)
  throw runtime_error("seed header");
 scale=10000000;caps[0]=768677;caps[1]=1587443;caps[2]=2546859;cap8=4058615;
 screen=false;audit_order=false;limit=0;faces_needed=2*n-b-2;
 State initial;initial.next=centers;
 for(int i=0;i<b;i++){int j=(i+1)%b;initial.adjacency[i]|=uint32_t(1)<<j;initial.adjacency[j]|=uint32_t(1)<<i;}
 uint32_t previous=0;
 for(int f=0;f<F;f++){
  uint64_t mask;
  if(!(input>>mask)||mask>=(uint64_t(1)<<centers)||mask<=previous||pop(uint32_t(mask))!=3||
     !(mask&((uint32_t(1)<<b)-1)))throw runtime_error("seed face");
  previous=mask;initial.faces[initial.count++]=mask;
  for(int v=0;v<centers;v++)if(mask>>v&1)initial.adjacency[v]|=uint32_t(mask)^(uint32_t(1)<<v);
 }
 if(!(input>>H)||H<1||H>MAXN)throw runtime_error("seed holes");
 vector<Region> pending;int total=centers;
 for(int h=0;h<H;h++){
  int K,I;if(!(input>>K>>I)||K<3||K>MAXN||I<0)throw runtime_error("seed hole header");
  vector<int> boundary;
  for(int k=0;k<K;k++){int v;if(!(input>>v)||v<b||v>=centers)throw runtime_error("seed hole vertex");boundary.push_back(v);}
  total+=I;pending.push_back({boundary,I});
 }
 string extra;if(input>>extra||!input.eof()||total!=n)throw runtime_error("seed budget/extra");
 initialize_cover_origin(argv[3]);initialize_collar_chunks(argv[2],stoull(argv[4]));
 started=chrono::steady_clock::now();
 visit_collar(initial,pending,0);flush_collar_chunk();
 ofstream out(argv[2]);if(!out)throw runtime_error("seed manifest open");
 out<<"{\"schema\":\"complete-cover-origin-collar-sorted-chunks-v1\",\"complete_necessary_outer_search\":true"
    <<",\"complete_full_triangulations\":false,\"N\":"<<n<<",\"B\":"<<b
    <<",\"seeded_fixed_collar_restriction\":true,\"not_a_complete_boundary_family\":true"
    <<",\"screen\":false,\"mode\":\"seed-control\",\"scale\":"<<scale
    <<",\"caps\":["<<caps[0]<<","<<caps[1]<<","<<caps[2]<<"],\"cap8\":"<<cap8
    <<",\"eight_rod_screen\":false,\"calls\":"<<calls
    <<",\"unique_weak_graph_count_not_computed_by_native\":true";
 write_paid_summary(out);write_sparse_summary(out);write_cover_origin_summary(out);write_collar_chunk_manifest(out);
 out<<"}\n";out.close();if(!out)throw runtime_error("seed manifest write");
 return 0;
}catch(exception const&e){cerr<<"REJECTED "<<e.what()<<"\n";return 1;}}
