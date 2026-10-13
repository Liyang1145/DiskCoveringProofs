// Earlier consequence of the existing minimum-boundary-root degree rule.
bool pending_degree_upper_enabled=false;
uint64_t pending_degree_upper_queries=0,pending_degree_upper_prunes=0;

void initialize_pending_degree_upper(string const&flag){
 if(flag!="0"&&flag!="1")throw runtime_error("pending degree upper flag must be 0 or 1");
 pending_degree_upper_enabled=flag=="1";
 pending_degree_upper_queries=pending_degree_upper_prunes=0;
}

bool pending_degree_upper_impossible(State const&s,vector<Region> const&pending){
 if(!pending_degree_upper_enabled)return false;
 pending_degree_upper_queries++;
 array<uint32_t,MAXN> available_existing{};
 array<int,MAXN> available_new{};
 uint32_t boundary_mask=(uint32_t(1)<<b)-1;
 for(auto const&region:pending){
  uint32_t vertices=0;
  for(int v:region.boundary){
   if(v<0||v>=n)throw runtime_error("pending degree upper invalid vertex");
   vertices|=uint32_t(1)<<v;
  }
  if(region.interior<0||region.interior>n)
   throw runtime_error("pending degree upper invalid budget");
  uint32_t original=vertices&boundary_mask;
  while(original){
   int v=first(original);original&=original-1;
   available_existing[v]|=vertices;
   available_new[v]+=region.interior;
  }
 }
 int current_root_degree=pop(s.adjacency[0]);
 for(int v=1;v<b;v++){
  uint32_t neighbors=(s.adjacency[v]|available_existing[v])&~(uint32_t(1)<<v);
  int upper=min(n-1,pop(neighbors)+available_new[v]);
  if(upper<current_root_degree){
   pending_degree_upper_prunes++;
   return true;
  }
 }
 return false;
}

void write_pending_degree_upper_summary(ostream&out){
 out<<",\"pending_degree_upper_screen\":"<<(pending_degree_upper_enabled?"true":"false")
    <<",\"pending_degree_upper_queries\":"<<pending_degree_upper_queries
    <<",\"pending_degree_upper_prunes_not_type_count\":"<<pending_degree_upper_prunes;
}
