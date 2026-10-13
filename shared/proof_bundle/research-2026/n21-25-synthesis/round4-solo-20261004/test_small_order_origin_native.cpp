// Functional guard/angle controls on explicit whole input graphs; not enumeration.
#define main small_order_enumerator_main
#include "peel_small_order_origin_collar.cpp"
#undef main

int main(int argc,char**argv){try{
 if(argc!=4)throw runtime_error("usage: small-order-control input origin-flag cap8");
 ifstream input(argv[1]);int count;
 if(!(input>>n>>b>>count)||n>MAXN||b<3||b>n||count<1||count>MAXF)
  throw runtime_error("control input header");
 faces_needed=2*n-b-2;scale=10000000;
 // For angle tests the Python driver writes exact per-order caps after faces.
 State state;state.next=n;
 for(int i=0;i<b;i++){int j=(i+1)%b;state.adjacency[i]|=uint32_t(1)<<j;state.adjacency[j]|=uint32_t(1)<<i;}
 uint32_t previous=0;
 for(int f=0;f<count;f++){
  uint64_t mask;
  if(!(input>>mask)||mask<=previous||mask>=(uint64_t(1)<<n)||pop(uint32_t(mask))!=3)
   throw runtime_error("control face");
  previous=mask;state.faces[state.count++]=uint32_t(mask);
  for(int v=0;v<n;v++)if(mask>>v&1)state.adjacency[v]|=uint32_t(mask)^(uint32_t(1)<<v);
 }
 if(!(input>>caps[0]>>caps[1]>>caps[2]))throw runtime_error("control angle caps");
 string extra;if(input>>extra||!input.eof())throw runtime_error("extra control input");
 cap8=stoll(argv[3]);screen=true;audit_order=false;
 initialize_cover_origin(argv[2]);
 bool obstruction=already_cover_origin_paid(state);
 cout<<"ORIGIN "<<(obstruction?1:0)<<" ANGLE "<<(possible(state)?1:0)<<"\n";
 return 0;
}catch(exception const& e){cerr<<"REJECTED "<<e.what()<<"\n";return 1;}}
