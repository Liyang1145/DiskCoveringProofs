// Same storage-only sorted slabs; a smaller independent C-drive safety guard.
size_t collar_slab_limit=0;
string collar_chunk_prefix;
vector<string> collar_chunk_files;
vector<uint64_t> collar_chunk_rows;
uint64_t collar_rows_to_chunks=0,collar_bytes_to_chunks=0;
constexpr uint64_t COLLAR_DISK_GUARD=4ULL*1024*1024*1024;

void initialize_collar_chunks(string const& output,size_t limit_rows){
 if(limit_rows<1||limit_rows>1000000)throw runtime_error("slab row limit bounds");
 collar_chunk_prefix=output+".chunk-";collar_slab_limit=limit_rows;
}

void flush_collar_chunk(){
 if(collars.empty())return;
 string path=collar_chunk_prefix+to_string(collar_chunk_files.size())+".jsonl";
 if(ifstream(path))throw runtime_error("refuse existing collar chunk");
 ofstream file(path);if(!file)throw runtime_error("collar chunk open");
 file<<"{\"schema\":\"sorted-outer-collar-slab-v1\",\"N\":"<<n<<",\"B\":"<<b
     <<",\"index\":"<<collar_chunk_files.size()<<",\"rows\":"<<collars.size()
     <<",\"not_a_complete_search\":true}\n";
 uint64_t count=0;
 for(auto const&[faces,centers]:collars){
  file<<"{\"centers\":"<<centers<<",\"faces\":[";
  for(size_t j=0;j<faces.size();j++){if(j)file<<",";file<<faces[j];}
  file<<"]}\n";count++;
  auto position=file.tellp();
  if(position<0||collar_bytes_to_chunks+uint64_t(position)>COLLAR_DISK_GUARD)
   throw runtime_error("DISK GUARD: sorted slab prefix is not a complete search");
 }
 auto bytes=file.tellp();file.close();
 if(!file||bytes<0||count!=collars.size())throw runtime_error("collar chunk write/count");
 collar_chunk_files.push_back(path);collar_chunk_rows.push_back(count);
 collar_rows_to_chunks+=count;collar_bytes_to_chunks+=uint64_t(bytes);
 collars.clear();
 cerr<<"SORTED COLLAR SLAB index="<<collar_chunk_files.size()-1<<" rows="<<count
     <<" cumulative_rows_not_unique_types="<<collar_rows_to_chunks<<"\n";
}

void write_collar_chunk_manifest(ostream& out){
 out<<",\"slab_limit\":"<<collar_slab_limit
    <<",\"rows_to_chunks_not_unique_types\":"<<collar_rows_to_chunks
    <<",\"bytes_to_chunks\":"<<collar_bytes_to_chunks
    <<",\"disk_guard_bytes\":"<<COLLAR_DISK_GUARD
    <<",\"chunk_count\":"<<collar_chunk_files.size()<<",\"chunks\":[";
 for(size_t j=0;j<collar_chunk_files.size();j++){
  if(j)out<<",";
  out<<"{\"file\":\""<<collar_chunk_files[j]<<"\",\"rows\":"<<collar_chunk_rows[j]<<"}";
 }
 out<<"]";
}
