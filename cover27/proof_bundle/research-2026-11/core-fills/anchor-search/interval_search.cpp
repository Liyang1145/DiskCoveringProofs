#include "polar_input.hpp"
#include <algorithm>
#include <bit>
#include <chrono>
#include <iostream>
#include <limits>
#include <memory>
#include <numeric>

namespace {
using namespace polar27;
using Word=std::uint64_t;
using Clock=std::chrono::steady_clock;
struct Span { int bin; Int lo,hi; bool operator==(const Span &) const=default; };
struct Row { int ring,index; Int theta; };
struct Domain {
    std::vector<Span> spans;
    std::vector<Int> caps;
    std::vector<int> bins;
    std::vector<Word> possible,sure;
    Int rlo=std::numeric_limits<Int>::max(),rhi=0,mass=0;
    Int alo=std::numeric_limits<Int>::max(),ahi=std::numeric_limits<Int>::min();
};
using D=std::shared_ptr<Domain>;
using State=std::array<D,N>;
struct Group {
    const std::vector<Bin> &bins;
    std::vector<std::vector<Int>> caps;
};
struct Limit {};

Int wrap(Int x,Int period){
    const Int v=x%period;
    return v<0?v+period:v;
}

class Solver {
    const Input &in;
    std::array<std::shared_ptr<Group>,N> groups;
    std::vector<Row> rows;
    std::vector<int> offset;
    struct Window { int ring; Int theta,half; };
    std::vector<Window> windows;
    Clock::time_point start=Clock::now();
    Int node_limit,nodes=0,conflicts=0,units=0;
    int maxdepth=0;

    Int width(int k,int bin,int ring) const {
        const Int a=groups[k]->bins[bin].arcs[ring];
        return a<0?a:std::min(in.turn/2,a+1);
    }
    std::pair<int,int> roles_for(int ring) const {
        if(ring==int(in.rings.size())-1)return {0,B};
        if(ring==in.core_ring)return {B,B+in.exact_core};
        return {0,N};
    }
    bool allowed_role(int k,int ring) const {
        const auto [first,last]=roles_for(ring);
        return first<=k&&k<last;
    }

    void sample_mask(Word *bits,int ring,Int lo,Int hi) const {
        if(hi<lo)return;
        const int samples=in.rings[ring].samples;
        const Int step=in.turn/samples;
        auto nonwrapped=[&](Int a,Int b) {
            const int l=int((a+step-1)/step),h=int(b/step);
            if(h<l)return;
            for(int w=l/64;w<=h/64;w++){
                const int first=std::max(l-64*w,0),last=std::min(h-64*w,63);
                const Word mask=last==63?~Word(0):(Word(1)<<(last+1))-1;
                bits[w]|=mask&(~Word(0)<<first);
            }
        };
        const Int span=hi-lo;
        if(span>=in.turn-1){nonwrapped(0,in.turn-1);return;}
        lo=wrap(lo,in.turn);
        hi=lo+span;
        nonwrapped(lo,std::min(hi,in.turn-1));
        if(hi>=in.turn)nonwrapped(0,hi-in.turn);
    }

    void summarize(int k,Domain &d) const {
        const Group &g=*groups[k];
        const int nr=int(in.rings.size());
        d.caps.assign(in.cuts.size(),0);
        d.possible.assign(offset.back(),0);
        d.sure.assign(offset.back(),~Word(0));
        int last=-1;
        for(const Span &span:d.spans){
            d.mass+=span.hi-span.lo+1;
            d.alo=std::min(d.alo,span.lo);
            d.ahi=std::max(d.ahi,span.hi);
            if(span.bin==last)continue;
            last=span.bin;
            d.bins.push_back(span.bin);
            const Bin &bin=g.bins[span.bin];
            d.rlo=std::min(d.rlo,bin.rlo);
            d.rhi=std::max(d.rhi,bin.rhi);
            for(int q=0;q<int(d.caps.size());q++)
                d.caps[q]=std::max(d.caps[q],g.caps[span.bin][q]);
        }
        std::vector<Word> temp;
        for(int s=0;s<nr;s++){
            const int begin=offset[s],n=offset[s+1]-begin;
            if(n==0)continue;
            auto *pos=d.possible.data()+begin,*sure=d.sure.data()+begin;
            if(!allowed_role(k,s)){std::fill(sure,sure+n,0);continue;}
            temp.resize(n);
            const int tail=in.rings[s].samples%64;
            const Word end=tail?(Word(1)<<tail)-1:~Word(0);
            sure[n-1]=end;
            for(const Span &span:d.spans){
                const Int a=width(k,span.bin,s);
                if(a<0)std::fill(sure,sure+n,0);
                else if(a>=in.turn/2){
                    std::fill(pos,pos+n,~Word(0)); pos[n-1]=end;
                }else{
                    sample_mask(pos,s,span.lo-a,span.hi+a);
                    if(std::any_of(sure,sure+n,[](Word w){return w!=0;})){
                        std::fill(temp.begin(),temp.end(),0);
                        sample_mask(temp.data(),s,span.hi-a,span.lo+a);
                        for(int j=0;j<n;j++)sure[j]&=temp[j];
                    }
                }
                if(pos[n-1]==end && std::all_of(pos,pos+n-1,[](Word w){return w==~Word(0);}) &&
                   std::none_of(sure,sure+n,[](Word w){return w!=0;}))break;
            }
        }
    }

    D make(int k,std::vector<Span> spans,const D &old={}) const {
        if(spans.empty())return {};
        if(old&&old->spans==spans)return old;
        auto d=std::make_shared<Domain>();
        d->spans=std::move(spans);
        summarize(k,*d);
        return d;
    }

    State initial() const {
        State d{};
        for(int k=0;k<N;k++){
            for(int j=0;j<k;j++)if(groups[j]==groups[k]){d[k]=d[j];break;}
            if(d[k])continue;
            const Spec &role=in.roles[k];
            std::vector<Span> spans;
            for(int j=0;j<int(groups[k]->bins.size());j++){
                Int lo=0,hi=in.turn-1;
                if(k==in.min_core){lo=in.core_angle_lo;hi=in.core_angle_hi;}
                else if(role.fixed)hi=0;
                else if(role.ring>=0){
                    const Int a=width(k,j,role.ring);
                    if(a<0)continue;
                    lo=role.anchor-a;
                    hi=std::min(lo+in.turn-1,role.anchor+a);
                }
                spans.push_back({j,lo,hi});
            }
            d[k]=make(k,std::move(spans));
        }
        return d;
    }

    template<class F>
    void overlaps(int k,const Span &span,const Row &row,const F &emit) const {
        const Int a=width(k,span.bin,row.ring);
        if(a<0)return;
        if(a>=in.turn/2){emit(span.lo,span.hi);return;}
        for(Int shift:{-in.turn,Int(0),in.turn}){
            const Int lo=std::max(span.lo,row.theta+shift-a);
            const Int hi=std::min(span.hi,row.theta+shift+a);
            if(lo<=hi)emit(lo,hi);
        }
    }
    Int hits(int k,const Domain &d,const Row &row) const {
        Int count=0;
        for(const Span &s:d.spans)
            overlaps(k,s,row,[&](Int a,Int b){count+=b-a+1;});
        return count;
    }
    D constrain(int k,const D &d,const Row &row,bool cover) const {
        std::vector<Span> spans;
        spans.reserve(d->spans.size());
        for(const Span &s:d->spans){
            Int next=s.lo;
            overlaps(k,s,row,[&](Int a,Int b){
                if(cover)spans.push_back({s.bin,a,b});
                else if(next<a)spans.push_back({s.bin,next,a-1});
                next=b+1;
            });
            if(!cover&&next<=s.hi)spans.push_back({s.bin,next,s.hi});
        }
        return make(k,std::move(spans),d);
    }
    int status(int k,const Domain &d,const Row &row) const {
        if(row.index<0){
            const Int h=hits(k,d,row);
            return h==0?0:h==d.mass?2:1;
        }
        const int w=offset[row.ring]+row.index/64;
        const Word bit=Word(1)<<(row.index%64);
        return d.sure[w]&bit?2:d.possible[w]&bit?1:0;
    }

    Int distance(Int theta,Int lo,Int hi) const {
        Int best=in.turn;
        for(Int k:{-in.turn,Int(0),in.turn}){
            const Int t=theta+k;
            best=std::min(best,std::max({Int(0),lo-t,t-hi}));
        }
        return best;
    }

    bool window_cuts(State &d,bool &changed) const {
        for(const Window w:windows){
            const Int length=2*w.half;
            const auto [first,last]=roles_for(w.ring);
            std::array<Int,N> caps{};
            Int sum=0;
            for(int k=first;k<last;k++){
                const Int a=d[k]->caps[w.ring]+1;
                const Int delta=distance(w.theta,d[k]->alo,d[k]->ahi);
                caps[k]=std::max(Int(0),std::min({length,2*a,a+w.half-delta}));
                sum+=caps[k];
            }
            if(sum<length)return false;
            const Int spare=sum-length;
            for(int k=first;k<last;k++)if(caps[k]>spare){
                const Int need=caps[k]-spare;
                std::vector<Span> next;
                next.reserve(d[k]->spans.size());
                for(const Span &s:d[k]->spans){
                    const Int a=width(k,s.bin,w.ring);
                    if(a<0||2*a<need)continue;
                    const Int radius=a+w.half-need;
                    if(radius<0)continue;
                    for(Int z:{-in.turn,Int(0),in.turn}){
                        const Int lo=std::max(s.lo,w.theta+z-radius);
                        const Int hi=std::min(s.hi,w.theta+z+radius);
                        if(lo<=hi)next.push_back({s.bin,lo,hi});
                    }
                }
                const D clipped=make(k,std::move(next),d[k]);
                if(!clipped)return false;
                changed|=clipped!=d[k];
                d[k]=clipped;
            }
        }
        return true;
    }

    bool chain(const State &d,const std::vector<int> &order,int ring,
               std::array<Int,N> &min_right,std::array<Int,N> &max_left) const {
        if(order.empty())return true;
        const Int dead_right=-4*in.turn,dead_left=4*in.turn;
        const int n=int(order.size()),first=order.front();
        Int initial_right=dead_right,initial_left=dead_left;
        for(const Span &s:d[first]->spans){
            const Int a=width(first,s.bin,ring);
            if(a<0)continue;
            initial_right=std::max(initial_right,s.hi+a);
            initial_left=std::min(initial_left,s.lo-a);
        }
        if(initial_right==dead_right)return false;

        Int right=initial_right;
        for(int j=1;j<n;j++){
            const int k=order[j];
            max_left[k]=right;
            Int reach=dead_right;
            for(const Span &s:d[k]->spans){
                const Int a=width(k,s.bin,ring);
                if(a>=0&&s.lo-a<=right)reach=std::max(reach,std::min(s.hi,right+a)+a);
            }
            if(reach==dead_right)return false;
            right=reach;
        }
        max_left[first]=right-in.turn;
        if(initial_left>max_left[first])return false;

        Int left=initial_left+in.turn;
        for(int j=n-1;j>=1;j--){
            const int k=order[j];
            min_right[k]=left;
            Int reach=dead_left;
            for(const Span &s:d[k]->spans){
                const Int a=width(k,s.bin,ring);
                if(a>=0&&s.hi+a>=left)reach=std::min(reach,std::max(s.lo,left-a)-a);
            }
            if(reach==dead_left)return false;
            left=reach;
        }
        min_right[first]=left;
        return min_right[first]<=initial_right;
    }

    bool capacities(State &d,bool &changed) const {
        for(const auto &x:d)if(!x)return false;
        std::vector<Int> total(in.cuts.size(),0);
        for(const auto &x:d)for(int q=0;q<int(total.size());q++)total[q]+=x->caps[q];
        for(int q=0;q<int(total.size());q++)if(total[q]<in.cuts[q].required)return false;
        const Int lo0=d[0]->rlo,hi1=d[B-1]->rhi,lo1=d[1]->rlo;
        Int hi0=d[0]->rhi;
        for(int k=1;k<B;k++)hi0=std::min(hi0,d[k]->rhi);
        const int u=int(in.rings.size())-1;
        std::array<Int,N> lmax,rmin;
        lmax.fill(2*in.turn); rmin.fill(-2*in.turn);
        static const std::vector<int> outer_order=[](){
            std::vector<int> order(B);
            std::iota(order.begin(),order.end(),0);
            return order;
        }();
        if(!chain(d,outer_order,u,rmin,lmax)||!chain(d,in.core_order,in.core_ring,rmin,lmax))
            return false;
        Int min_core_lo=0,min_core_hi=in.scale;
        if(in.min_core>=0){
            min_core_lo=d[in.min_core]->rlo;
            for(int k:in.core_order)min_core_hi=std::min(min_core_hi,d[k]->rhi);
        }
        std::array<Int,N> norm_cap;
        std::array<Int,N> norm_floor{};
        norm_cap.fill(in.scale);
        auto apply_count=[&](const RadialCount &c) {
            int possible=0;
            if(c.needed>0){
                for(int k=c.first;k<c.last;k++)possible+=d[k]->rlo<=c.max_norm;
                if(possible<c.needed)return false;
                if(possible==c.needed)for(int k=c.first;k<c.last;k++)
                    if(d[k]->rlo<=c.max_norm)norm_cap[k]=std::min(norm_cap[k],c.max_norm);
            }else{
                for(int k=c.first;k<c.last;k++)possible+=d[k]->rhi>=c.max_norm;
                if(possible< -c.needed)return false;
                if(possible== -c.needed)for(int k=c.first;k<c.last;k++)
                    if(d[k]->rhi>=c.max_norm)norm_floor[k]=std::max(norm_floor[k],c.max_norm);
            }
            return true;
        };
        if(!apply_count({1,B,1,2*in.expanded_radius-lo0}))return false;
        for(const auto &c:in.counts)if(!apply_count(c))return false;
        for(int k=0;k<N;k++){
            const auto &g=*groups[k];
            std::vector<char> allowed(g.bins.size(),0);
            bool all=true;
            for(int j:d[k]->bins){
                const Bin &bin=g.bins[j];
                bool ok=bin.rlo<=norm_cap[k]&&bin.rhi>=norm_floor[k]
                        &&(k!=0||bin.rlo<=hi0)&&(k>=B||bin.rhi>=lo0)
                        &&(k!=1||bin.rlo<=hi1)&&(k!=B-1||bin.rhi>=lo1);
                if(in.min_core>=0&&14<=k&&k<24){
                    ok&=bin.rhi>=min_core_lo;
                    if(k==in.min_core)ok&=bin.rlo<=min_core_hi;
                }
                for(int q=0;ok&&q<int(total.size());q++)
                    ok=total[q]-d[k]->caps[q]+g.caps[j][q]>=in.cuts[q].required;
                allowed[j]=ok; all&=ok;
            }
            const int ring=k<B?u:(in.min_core>=0&&14<=k&&k<24?in.core_ring:-1);
            if(all&&ring<0)continue;
            std::vector<Span> spans;
            spans.reserve(d[k]->spans.size());
            for(auto s:d[k]->spans)if(allowed[s.bin]){
                if(ring>=0){
                    const Int a=width(k,s.bin,ring);
                    if(a<0)continue;
                    s.lo=std::max(s.lo,rmin[k]-a);
                    s.hi=std::min(s.hi,lmax[k]+a);
                }
                if(s.lo<=s.hi)spans.push_back(s);
            }
            const auto next=make(k,std::move(spans),d[k]);
            if(!next)return false;
            changed|=next!=d[k];
            d[k]=next;
        }
        return true;
    }

    bool propagate(State &d,std::vector<Row> &pending){
        while(true){
            bool changed=false;
            if(!capacities(d,changed)||!window_cuts(d,changed))return false;
            std::vector<Row> next;
            next.reserve(pending.size());
            for(const Row &row:pending){
                int count=0,only=-1;
                bool yes=false;
                const auto [first,last]=roles_for(row.ring);
                for(int k=first;k<last;k++){
                    const int s=status(k,*d[k],row);
                    if(s==2){yes=true;break;}
                    if(s==1){count++;only=k;}
                }
                if(yes)continue;
                if(count==0)return false;
                if(count==1){
                    const auto trimmed=constrain(only,d[only],row,true);
                    if(!trimmed)return false;
                    changed|=trimmed!=d[only];
                    d[only]=trimmed; units++;
                }else next.push_back(row);
            }
            pending.swap(next);
            if(!changed)return true;
        }
    }

    struct Choice { int k; Int hit; std::vector<int> same; };
    std::pair<Row,std::vector<Choice>> choose(const State &d,const std::vector<Row> &pending) const {
        int least=N+1;
        std::vector<Row> tied;
        for(const Row &row:pending){
            int count=0;
            const auto [first,last]=roles_for(row.ring);
            for(int k=first;k<last;k++)count+=status(k,*d[k],row)>0;
            if(count<least){least=count;tied.clear();}
            if(count==least&&tied.size()<64)tied.push_back(row);
        }
        Row winner=tied.front();
        double best=std::numeric_limits<double>::infinity();
        std::vector<Choice> options;
        for(const Row &row:tied){
            std::vector<Choice> choices;
            double score=0;
            const auto [first,last]=roles_for(row.ring);
            for(int k=first;k<last;k++)if(status(k,*d[k],row)>0){
                auto same=std::find_if(choices.begin(),choices.end(),[&](const Choice &c){
                    return groups[k]==groups[c.k]&&d[k]->spans==d[c.k]->spans;
                });
                if(same!=choices.end())same->same.push_back(k);
                else {
                    const Int h=hits(k,*d[k],row);
                    choices.push_back({k,h,{}});
                    score+=double(h)/d[k]->mass;
                }
            }
            if(score<best){best=score;winner=row;options=std::move(choices);}
        }
        std::stable_sort(options.begin(),options.end(),[&](const Choice &a,const Choice &b){
            return double(a.hit)/d[a.k]->mass<double(b.hit)/d[b.k]->mass;
        });
        return {winner,options};
    }

    Row gap(const State &d) const {
        for(int s=0;s<int(in.rings.size());s++){
            std::vector<std::pair<Int,Int>> arcs;
            const auto [first,last]=roles_for(s);
            for(int k=first;k<last;k++){
                const Span &c=d[k]->spans.front();
                const Int beta=width(k,c.bin,s);
                if(beta<0)continue;
                if(beta>=in.turn/2){arcs={{0,in.turn-1}};break;}
                const Int t=(c.lo+c.hi)/2;
                const Int l=wrap(t-beta,in.turn),h=l+2*beta;
                arcs.push_back({l,std::min(h,in.turn-1)});
                if(h>=in.turn)arcs.push_back({0,h-in.turn});
            }
            std::sort(arcs.begin(),arcs.end());
            Int end=-1;
            for(const auto [l,h]:arcs){
                if(l>end+1)break;
                end=std::max(end,h);
            }
            if(end<in.turn-1)return {s,-1,end+1};
        }
        return {-1,-1,0};
    }

    bool search(State d,std::vector<Row> pending,int depth){
        ++nodes;
        if(node_limit&&nodes>node_limit)throw Limit{};
        maxdepth=std::max(maxdepth,depth);
        if(nodes%10000==0)std::cerr<<"nodes "<<nodes<<" pending "<<pending.size()<<" depth "<<maxdepth
                                  <<" seconds "<<elapsed()<<"\n";
        if(!propagate(d,pending)){conflicts++;return false;}
        if(pending.empty()){
            const Row row=gap(d);
            if(row.ring>=0)pending.push_back(row);
            else {
                for(int k=0;k<N;k++){
                    const Span &span=d[k]->spans.front();
                    const Bin &bin=groups[k]->bins[span.bin];
                    std::cout<<"span "<<k<<" "<<bin.rlo<<" "<<bin.rhi<<" "<<span.lo<<" "<<span.hi
                             <<" count "<<d[k]->spans.size()<<"\n";
                }
                return true;
            }
        }
        const auto [row,options]=choose(d,pending);
        if(options.empty()){conflicts++;return false;}
        for(const auto &c:options){
            const D original=d[c.k];
            d[c.k]=constrain(c.k,original,row,true);
            if(d[c.k]&&search(d,pending,depth+1))return true;
            d[c.k]=constrain(c.k,original,row,false);
            if(!d[c.k])return false;
            for(int j:c.same){
                d[j]=constrain(j,d[j],row,false);
                if(!d[j])return false;
            }
        }
        return false;
    }

public:
    Solver(const Input &input,Int limit,bool local) : in(input),node_limit(limit){
        offset={0};
        for(int i=0;i<int(in.rings.size());i++){
            const auto n=in.rings[i].samples;
            for(int j=0;j<n;j++)rows.push_back({i,j,in.turn*j/n});
            offset.push_back(offset.back()+(n+63)/64);
        }
        for(int k=0;k<N;k++){
            const Spec s=in.roles[k];
            if(!s.fixed&&s.ring<0)for(int j=0;j<k;j++){
                const Spec t=in.roles[j];
                if(!t.fixed&&t.ring<0&&s.family==t.family&&(j<B)==(k<B)){groups[k]=groups[j];break;}
            }
            if(groups[k])continue;
            const auto &bins=in.families[s.family];
            auto group=std::make_shared<Group>(Group{bins,{}});
            group->caps.resize(bins.size(),std::vector<Int>(in.cuts.size()));
            for(int j=0;j<int(bins.size());j++)for(int q=0;q<int(in.cuts.size());q++)
                for(auto [ring,weight]:in.cuts[q].terms)if(allowed_role(k,ring))
                    group->caps[j][q]+=weight*std::max(Int(0),bins[j].arcs[ring]);
            groups[k]=group;
        }
        if(local){
            for(int s=0;s<int(in.rings.size());s++){
                const Int r=in.rings[s].radius;
                if(!(in.scale*47/100<=r&&r<=in.scale*82/100))continue;
                bool acute=true;
                for(int k=0;k<N;k++)for(int j=0;j<int(groups[k]->bins.size());j++)
                    acute&=width(k,j,s)<=in.turn/4;
                if(!acute)continue;
                for(int j=0;j<26;j++)for(Int half:{in.turn/26,in.turn/14})
                    windows.push_back({s,j*in.turn/26,half});
            }
        }
        std::cerr<<"rows "<<rows.size()<<" angular windows "<<windows.size()
                 <<" seconds "<<elapsed()<<"\n";
    }
    double elapsed() const { return std::chrono::duration<double>(Clock::now()-start).count(); }
    int run(){
        int result=1;
        try {
            const bool unresolved=search(initial(),rows,0);
            std::cout<<(unresolved?"unresolved ring relaxation":"excluded")<<"\n";
            result=unresolved?1:0;
        } catch(const Limit&){std::cout<<"unresolved node limit\n";}
        std::cout<<"nodes "<<nodes<<" conflicts "<<conflicts<<" units "<<units
                 <<" depth "<<maxdepth<<" seconds "<<elapsed()<<"\n";
        return result;
    }
};
}

int main(int argc,char **argv){
    if(argc<2){std::cerr<<"usage: interval_search table.txt [node limit] [windows]\n";return 2;}
    try {
        Input in(argv[1]);
        Solver s(in,argc>2?std::stoll(argv[2]):0,argc>3&&std::string(argv[3])=="windows");
        return s.run();
    } catch(const std::exception &e){std::cerr<<e.what()<<"\n";return 2;}
}
