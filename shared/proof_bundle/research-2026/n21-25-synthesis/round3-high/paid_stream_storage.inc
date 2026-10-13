// Exact binary little-endian runs. Runs are retained, never silently deleted.
#ifndef PAID_BLOCK_LIMIT
#define PAID_BLOCK_LIMIT 100000
#endif
constexpr size_t SURVIVOR_BLOCK=PAID_BLOCK_LIMIT;
string residual_target;
vector<string> residual_runs;
uint64_t rows_to_runs=0;

void write_u32(ostream& out,uint32_t value){
 for(int j=0;j<4;j++)out.put(char((value>>(8*j))&255));
 if(!out)throw runtime_error("binary residual write failure");
}
void write_u64(ostream& out,uint64_t value){
 for(int j=0;j<8;j++)out.put(char((value>>(8*j))&255));
 if(!out)throw runtime_error("binary count write failure");
}
uint32_t read_u32(istream& in){
 uint32_t value=0;
 for(int j=0;j<4;j++){
  int byte=in.get();if(byte==char_traits<char>::eof())throw runtime_error("truncated residual run");
  value|=uint32_t(static_cast<unsigned char>(byte))<<(8*j);
 }
 return value;
}
void initialize_paid_storage(string const& output){
 residual_target=output;
 if(filesystem::exists(output)||filesystem::exists(output+".building")||filesystem::exists(output+".runs"))
  throw runtime_error("refuse to overwrite residual output/runs");
 filesystem::create_directory(output+".runs");
}
void flush_paid_run(){
 if(survivors.empty())return;
 string path=residual_target+".runs/run-"+to_string(residual_runs.size())+".bin";
 if(filesystem::exists(path))throw runtime_error("run overwrite refused");
 ofstream out(path,ios::binary);
 if(!out)throw runtime_error("run open failed");
 out.write("PAIDRUN1",8);
 write_u32(out,uint32_t(n));write_u32(out,uint32_t(b));write_u32(out,uint32_t(faces_needed));
 write_u64(out,uint64_t(survivors.size()));
 for(auto const& [code,stab]:survivors){
  if((int)code.size()!=faces_needed||stab<=0)throw runtime_error("run row size/stabilizer");
  write_u32(out,uint32_t(stab));
  for(auto face:code)write_u32(out,face);
 }
 out.close();if(!out)throw runtime_error("run close failed");
 rows_to_runs+=survivors.size();residual_runs.push_back(path);survivors.clear();
}
struct RunCursor{
 ifstream stream;
 uint64_t remaining=0;
 vector<uint32_t> previous,code;
 uint32_t stab=0;
 bool ended=false;
 explicit RunCursor(string const& path):stream(path,ios::binary){
  char magic[8];stream.read(magic,8);
  if(!stream||string(magic,8)!="PAIDRUN1")throw runtime_error("run header");
  if(read_u32(stream)!=uint32_t(n)||read_u32(stream)!=uint32_t(b)||
     read_u32(stream)!=uint32_t(faces_needed))throw runtime_error("run graph dimensions");
  for(int j=0;j<8;j++){
   int byte=stream.get();if(byte==char_traits<char>::eof())throw runtime_error("run count");
   remaining|=uint64_t(static_cast<unsigned char>(byte))<<(8*j);
  }
  advance();
 }
 bool advance(){
  if(!remaining){
   if(stream.peek()!=char_traits<char>::eof())throw runtime_error("extra run bytes");
   ended=true;stream.close();return false;
  }
  stab=read_u32(stream);code.clear();
  for(int j=0;j<faces_needed;j++)code.push_back(read_u32(stream));
  if(!stab||!is_sorted(code.begin(),code.end())||
     adjacent_find(code.begin(),code.end())!=code.end()||
     (!previous.empty()&&!(previous<code)))throw runtime_error("run sort/stabilizer failure");
  previous=code;remaining--;return true;
 }
};

uint64_t merge_paid_runs(string const& mode){
 flush_paid_run();
 ostringstream metadata;
 metadata<<"{\"complete\":false,\"residual_complete\":true,\"schema\":\"paid-peeling-residual-binary-v1\""
         <<",\"N\":"<<n<<",\"B\":"<<b<<",\"screen\":"<<(screen?"true":"false")
         <<",\"root_degree_prune\":true,\"mode\":\""<<mode<<"\",\"scale\":"<<scale
         <<",\"caps\":["<<caps[0]<<","<<caps[1]<<","<<caps[2]<<"],\"calls\":"<<calls
         <<",\"prunes\":"<<prunes<<",\"rooted\":"<<rooted
         <<",\"rows_to_runs\":"<<rows_to_runs<<",\"run_count\":"<<residual_runs.size()
         <<",\"survivor_block_size\":"<<SURVIVOR_BLOCK;
 write_paid_summary(metadata);metadata<<"}";
 auto text=metadata.str();
 if(text.size()>64*1024*1024)throw runtime_error("residual metadata limit");
 ofstream out(residual_target+".building",ios::binary);
 if(!out)throw runtime_error("binary residual output open");
 out.write("PAIDRSV1",8);
 write_u32(out,uint32_t(n));write_u32(out,uint32_t(b));write_u32(out,uint32_t(faces_needed));
 write_u32(out,uint32_t(text.size()));
 write_u64(out,0); // Patched only after the complete exact merge.
 out.write(text.data(),text.size());
 vector<unique_ptr<RunCursor>> cursors;
 auto later=[&](int left,int right){return cursors[left]->code>cursors[right]->code;};
 priority_queue<int,vector<int>,decltype(later)> queue(later);
 for(auto const& path:residual_runs){
  cursors.push_back(make_unique<RunCursor>(path));
  if(!cursors.back()->ended)queue.push(cursors.size()-1);
 }
 uint64_t unique_count=0,read_count=0;
 vector<uint32_t> previous;
 uint32_t previous_stab=0;
 while(!queue.empty()){
  int index=queue.top();queue.pop();
  auto& cursor=*cursors[index];
  if(previous==cursor.code){
   if(previous_stab!=cursor.stab)throw runtime_error("stabilizer disagreement across runs");
  }else{
   if(!previous.empty()&&!(previous<cursor.code))throw runtime_error("merge order");
   write_u32(out,cursor.stab);
   for(auto mask:cursor.code)write_u32(out,mask);
   previous=cursor.code;previous_stab=cursor.stab;unique_count++;
  }
  read_count++;
  if(cursor.advance())queue.push(index);
 }
 if(read_count!=rows_to_runs)throw runtime_error("run merge count");
 out.seekp(24,ios::beg);write_u64(out,unique_count);
 out.close();if(!out)throw runtime_error("final residual close");
 if(filesystem::exists(residual_target))throw runtime_error("residual output appeared during merge");
 filesystem::rename(residual_target+".building",residual_target);
 return unique_count;
}
