// Exact completed-subproblem reuse; no isomorphism or geometric decision.
#include <unordered_set>
#include <exception>
#include <new>
bool exact_state_reuse_enabled=false;
uint64_t exact_state_reuse_hits=0,exact_state_reuse_queries=0;
uint64_t exact_state_reuse_clears=0,exact_state_reuse_words=0;
uint64_t exact_state_reuse_peak_words=0,exact_state_reuse_allocation_failures=0;
struct ExactStateKeyHash {
 size_t operator()(vector<uint32_t> const& key)const noexcept {
#ifdef FORCE_EXACT_STATE_HASH_COLLISIONS
  return 0;
#else
  uint64_t value=1469598103934665603ULL;
  for(uint32_t word:key){value^=word;value*=1099511628211ULL;}
  return size_t(value);
#endif
 }
};
struct ExactStateKeyEqual {
 bool operator()(vector<uint32_t> const&a,vector<uint32_t> const&c)const noexcept {
  if(a.size()!=c.size())return false;
  for(size_t i=0;i<a.size();i++)if(a[i]!=c[i])return false;
  return true;
 }
};
unordered_set<vector<uint32_t>,ExactStateKeyHash,ExactStateKeyEqual> completed_collar_states;
constexpr uint64_t EXACT_STATE_MAX_KEYS=65536,EXACT_STATE_MAX_WORDS=4194304;

void initialize_exact_state_reuse(string const& flag){
 if(flag!="0"&&flag!="1")throw runtime_error("state reuse flag must be 0 or 1");
 exact_state_reuse_enabled=flag=="1";
 completed_collar_states.clear();
 exact_state_reuse_hits=exact_state_reuse_queries=exact_state_reuse_clears=0;
 exact_state_reuse_words=exact_state_reuse_peak_words=exact_state_reuse_allocation_failures=0;
}

vector<uint32_t> exact_collar_state_key(State const&s,vector<Region> const&pending,int omitted_faces){
 if(!exact_state_reuse_enabled)return {};
 vector<uint32_t> key;
 size_t length=6+size_t(n)+size_t(s.count);
 for(auto const&region:pending)length+=2+region.boundary.size();
 if(length>EXACT_STATE_MAX_WORDS)return {};
 try{
  key.reserve(length);
  for(int value:{n,b,s.next,s.count,omitted_faces,int(pending.size())})key.push_back(uint32_t(value));
  for(int i=0;i<n;i++)key.push_back(s.adjacency[i]);
  for(int i=0;i<s.count;i++)key.push_back(s.faces[i]);
  for(auto const&region:pending){
   key.push_back(uint32_t(region.interior));key.push_back(uint32_t(region.boundary.size()));
   for(int vertex:region.boundary)key.push_back(uint32_t(vertex));
  }
  if(key.size()!=length)throw runtime_error("exact state key length mismatch");
 }catch(bad_alloc const&){
  exact_state_reuse_allocation_failures++;exact_state_reuse_enabled=false;
  completed_collar_states.clear();exact_state_reuse_words=0;return {};
 }
 return key;
}

bool exact_collar_state_already_completed(vector<uint32_t> const&key){
 if(key.empty()||!exact_state_reuse_enabled)return false;
 exact_state_reuse_queries++;
 bool found=completed_collar_states.find(key)!=completed_collar_states.end();
 if(found)exact_state_reuse_hits++;
 return found;
}

struct CompletedCollarStateVisit {
 vector<uint32_t> key;
 int exceptions_at_entry;
 explicit CompletedCollarStateVisit(vector<uint32_t> value):
  key(move(value)),exceptions_at_entry(uncaught_exceptions()){}
 ~CompletedCollarStateVisit()noexcept{
  if(key.empty()||!exact_state_reuse_enabled||uncaught_exceptions()!=exceptions_at_entry)return;
  try{
   if(completed_collar_states.size()>=EXACT_STATE_MAX_KEYS||
      exact_state_reuse_words+key.size()>EXACT_STATE_MAX_WORDS){
    completed_collar_states.clear();exact_state_reuse_words=0;exact_state_reuse_clears++;
   }
   auto words=key.size();
   auto inserted=completed_collar_states.emplace(move(key));
   if(inserted.second)exact_state_reuse_words+=words;
   exact_state_reuse_peak_words=max(exact_state_reuse_peak_words,exact_state_reuse_words);
  }catch(bad_alloc const&){
   exact_state_reuse_allocation_failures++;exact_state_reuse_enabled=false;
   completed_collar_states.clear();exact_state_reuse_words=0;
  }catch(...){
   // An optional cache cannot turn a completed original continuation into
   // a program failure or an incomplete continuation into a proof.
   exact_state_reuse_enabled=false;completed_collar_states.clear();exact_state_reuse_words=0;
  }
 }
};

void write_exact_state_reuse_summary(ostream&out){
 out<<",\"exact_completed_state_reuse\":"<<(exact_state_reuse_enabled?"true":"false")
    <<",\"exact_state_reuse_queries\":"<<exact_state_reuse_queries
    <<",\"exact_completed_state_reuse_hits_not_type_count\":"<<exact_state_reuse_hits
    <<",\"exact_state_reuse_cache_clears\":"<<exact_state_reuse_clears
    <<",\"exact_state_reuse_current_keys\":"<<completed_collar_states.size()
    <<",\"exact_state_reuse_peak_words\":"<<exact_state_reuse_peak_words
    <<",\"exact_state_reuse_allocation_failures\":"<<exact_state_reuse_allocation_failures;
}
