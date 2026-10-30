// Third, compiled, catalog-relative replay. All checks use explicit exceptions.
// No Python producer imports, no forced-union or degree-capacity pruning.
#include "catalog_bits.hpp"
#include <openssl/sha.h>
#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <functional>
#include <iomanip>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>
using Mask=std::uint16_t;
using Key=std::vector<int>;
constexpr int N=792;
static std::vector<Mask> outside;
static std::array<int,4096> index_of;
static void need(bool ok,const std::string& why){if(!ok)throw std::runtime_error(why);}
static int pop(Mask m){return __builtin_popcount(static_cast<unsigned>(m));}
static bool has(Mask m,int p){return (m&(Mask(1)<<p))!=0;}
static std::string hash(const std::string& value){
    unsigned char result[SHA256_DIGEST_LENGTH];
    SHA256(reinterpret_cast<const unsigned char*>(value.data()),value.size(),result);
    std::ostringstream out;out<<std::hex<<std::setfill('0');
    for(unsigned char c:result)out<<std::setw(2)<<unsigned(c);
    return out.str();
}
static void combinations(int n,int k,int start,Mask prefix,std::vector<Mask>& output){
    if(k==0){output.push_back(prefix);return;}
    for(int p=start;p<=n-k;++p)combinations(n,k-1,p+1,Mask(prefix|(Mask(1)<<p)),output);
}
static void validate_link(const std::vector<Mask>& link){
    need(link.size()==15,"link must have15 blocks");
    need(std::set<Mask>(link.begin(),link.end()).size()==15,"duplicate link block");
    for(Mask b:link)need(b<4096&&pop(b)==6,"link block shape/range");
    std::vector<Mask> triples;combinations(12,3,0,0,triples);
    for(Mask t:triples)need(std::any_of(link.begin(),link.end(),[t](Mask b){return (b&t)==t;}),"uncovered source triple");
}
struct Star {
    int center;
    std::vector<Mask> rows,rest;
    std::vector<int> points;
    std::array<int,12> degree{};
    std::array<std::array<int,12>,12> pair{};
    std::array<Key,12> signatures;
    std::vector<Key> invariant;
    Star(const std::vector<Mask>& link,int c):center(c){
        for(int p=0;p<12;++p)if(p!=c)points.push_back(p);
        for(Mask b:link){if(has(b,c))rows.push_back(Mask(b&~(Mask(1)<<c)));else rest.push_back(b);}
        std::sort(rows.begin(),rows.end());
        for(int p:points){
            for(Mask b:rows)if(has(b,p))++degree[p];
            for(int q:points)for(Mask b:rows)if(has(b,p)&&has(b,q))++pair[p][q];
        }
        for(int p:points){
            Key detail;
            for(int q:points)if(q!=p)detail.push_back(16*degree[q]+pair[p][q]);
            std::sort(detail.begin(),detail.end());
            signatures[p].push_back(degree[p]);
            signatures[p].insert(signatures[p].end(),detail.begin(),detail.end());
            invariant.push_back(signatures[p]);
        }
        std::sort(invariant.begin(),invariant.end());
    }
};
struct Pattern {
    Key ids;
    std::bitset<N> bits;
    std::array<std::string,12> signature;
};
using Domains=std::array<std::vector<Pattern>,12>;
static Pattern pattern(const Key& ids){
    Pattern result;result.ids=ids;
    need(std::set<int>(ids.begin(),ids.end()).size()==ids.size(),"duplicate pattern block");
    for(int i:ids){
        need(i>=0&&i<N,"pattern block range");result.bits.set(std::size_t(i));
        for(int p=0;p<12;++p)if(has(outside[std::size_t(i)],p)){
            result.signature[p].push_back(char(i&255));
            result.signature[p].push_back(char((i>>8)&255));
        }
    }
    return result;
}
static void enumerate_maps(const Star& s,const Star& t,std::set<Key>& patterns){
    need(s.invariant==t.invariant,"star invariant precondition");
    if(s.rows.size()!=t.rows.size())return;
    std::array<std::vector<int>,12> candidates;
    for(int p:s.points)for(int q:t.points)if(s.signatures[p]==t.signatures[q])candidates[p].push_back(q);
    for(int p:s.points)if(candidates[p].empty())return;
    auto order=s.points;
    std::sort(order.begin(),order.end(),[&](int a,int b){return std::make_pair(candidates[a].size(),a)<std::make_pair(candidates[b].size(),b);});
    std::array<int,12> map;map.fill(-1);Mask used=0;
    auto image=[&](Mask b){
        Mask value=0;
        for(int p=0;p<12;++p)if(has(b,p)){need(map[p]>=0,"unmapped source point");value=Mask(value|(Mask(1)<<map[p]));}
        return value;
    };
    std::function<void(int)> search=[&](int k){
        if(k==11){
            std::vector<Mask> mapped;
            for(Mask b:s.rows)mapped.push_back(image(b));
            std::sort(mapped.begin(),mapped.end());
            if(mapped!=t.rows)return;
            Key ids;
            for(Mask b:s.rest){Mask v=Mask(image(b)|(Mask(1)<<t.center));need(pop(v)==7,"extension block size");int i=index_of[v];need(i>=0,"outside column lookup");ids.push_back(i);}
            std::sort(ids.begin(),ids.end());patterns.insert(std::move(ids));return;
        }
        int p=order[std::size_t(k)];
        for(int q:candidates[p]){
            if(has(used,q))continue;
            bool match=true;
            for(int j=0;j<k;++j){int prior=order[std::size_t(j)];if(s.pair[p][prior]!=t.pair[q][map[prior]]){match=false;break;}}
            if(!match)continue;
            map[p]=q;used=Mask(used|(Mask(1)<<q));search(k+1);used=Mask(used&~(Mask(1)<<q));map[p]=-1;
        }
    };
    search(0);
}
static std::vector<Star> source_stars;
static std::map<std::vector<Key>,std::vector<int>> source_groups;
static std::pair<std::vector<Pattern>,std::string> build_domain(const std::vector<Mask>& link,int q){
    Star target(link,q);std::set<Key> keys;
    auto it=source_groups.find(target.invariant);
    if(it!=source_groups.end())for(int i:it->second)enumerate_maps(source_stars[std::size_t(i)],target,keys);
    std::vector<Pattern> result;result.reserve(keys.size());std::ostringstream normalized;normalized<<'[';bool first=true;
    for(const Key& key:keys){
        if(!first){normalized<<',';}
        first=false;normalized<<'[';
        for(std::size_t j=0;j<key.size();++j){if(j)normalized<<',';normalized<<key[j];}
        normalized<<']';result.push_back(pattern(key));
    }
    normalized<<']';return {std::move(result),hash(normalized.str())};
}
using Active=std::array<std::vector<int>,4>;
static bool arc(const Domains& domains,const std::array<int,4>& zero,Active& active){
    while(true){
        std::array<std::array<std::unordered_set<std::string>,4>,4> available;
        for(int a=0;a<4;++a)for(int b=0;b<4;++b)if(a!=b)for(int i:active[a])available[a][b].insert(domains[zero[a]][std::size_t(i)].signature[zero[b]]);
        Active next;
        for(int a=0;a<4;++a){
            for(int i:active[a]){
                bool retain=true;
                for(int b=0;b<4;++b)if(a!=b&&available[b][a].count(domains[zero[a]][std::size_t(i)].signature[zero[b]])==0){retain=false;break;}
                if(retain)next[a].push_back(i);
            }
            if(next[a].empty()){active=std::move(next);return false;}
        }
        if(next==active)return true;
        active=std::move(next);
    }
}
static bool union_search(const Domains& domains,const std::array<int,4>& zero,const Active& initial,std::size_t budget,std::uint64_t& nodes){
    std::function<bool(const Active&,unsigned,const std::bitset<N>&)> visit=[&](const Active& active,unsigned todo,const std::bitset<N>& united){
        ++nodes;if(united.count()>budget)return false;if(todo==0)return true;
        int a=-1;
        for(int p=0;p<4;++p)if(todo&(1u<<p))if(a<0||active[p].size()<active[a].size())a=p;
        for(int i:active[a]){
            const Pattern& chosen=domains[zero[a]][std::size_t(i)];auto larger=united|chosen.bits;if(larger.count()>budget)continue;
            Active next=active;bool possible=true;
            for(int b=0;b<4;++b)if(b!=a&&(todo&(1u<<b))){
                next[b].clear();
                for(int j:active[b])if(domains[zero[b]][std::size_t(j)].signature[zero[a]]==chosen.signature[zero[b]])next[b].push_back(j);
                if(next[b].empty()){possible=false;break;}
            }
            if(possible&&visit(next,todo&~(1u<<a),larger))return true;
        }
        return false;
    };
    return visit(initial,15u,std::bitset<N>{});
}
static void self_test(){
    Domains d;Key ids;
    for(int i=0;i<N&&ids.size()<14;++i)if((outside[std::size_t(i)]&15u)==15u)ids.push_back(i);
    need(ids.size()==14,"synthetic source");
    for(int q=0;q<4;++q)d[q].push_back(pattern(ids));
    Active active;for(auto& a:active)a.push_back(0);std::array<int,4> zero{{0,1,2,3}};
    std::uint64_t nodes=0;need(union_search(d,zero,active,14,nodes),"positive14 union rejected");
    need(!union_search(d,zero,active,13,nodes),"budget13 did not reject14 union");
    Key inconsistent=ids;inconsistent.pop_back();d[1][0]=pattern(inconsistent);
    need(!union_search(d,zero,active,14,nodes),"inconsistent shared pencils accepted");
    bool rejected=false;try{pattern(Key{792});}catch(const std::runtime_error&){rejected=true;}need(rejected,"bad block id accepted");
    auto bad=std::vector<Mask>(CATALOG[0].begin(),CATALOG[0].end());bad[0]=bad[1];rejected=false;
    try{validate_link(bad);}catch(const std::runtime_error&){rejected=true;}need(rejected,"duplicate source block accepted");
}
int main(){
 try{
    combinations(12,7,0,0,outside);need(outside.size()==N,"outside block census");index_of.fill(-1);
    for(int i=0;i<N;++i)index_of[outside[std::size_t(i)]]=i;
    source_stars.reserve(68*12);
    for(const auto& row:CATALOG){std::vector<Mask> link(row.begin(),row.end());validate_link(link);for(int p=0;p<12;++p)source_stars.emplace_back(link,p);}
    for(std::size_t i=0;i<source_stars.size();++i)source_groups[source_stars[i].invariant].push_back(int(i));
    self_test();std::uint64_t total_pair=0,total_arc=0,total_search=0,total_nodes=0;
    for(int cid=0;cid<68;++cid){
        std::vector<Mask> link(CATALOG[std::size_t(cid)].begin(),CATALOG[std::size_t(cid)].end());Domains domains;
        for(int q=0;q<12;++q){auto made=build_domain(link,q);domains[q]=std::move(made.first);std::cout<<"{\"class_id\":"<<cid+1<<",\"point\":"<<q<<",\"patterns\":"<<domains[q].size()<<",\"sha256\":\""<<made.second<<"\"}\n";}
        bool pair[12][12]{};
        for(int a=0;a<12;++a)for(int b=a+1;b<12;++b){
            std::unordered_set<std::string> signatures;for(const Pattern& p:domains[a])signatures.insert(p.signature[b]);
            for(const Pattern& p:domains[b])if(signatures.count(p.signature[a])){pair[a][b]=pair[b][a]=true;break;}
        }
        std::uint64_t pair_count=0,arc_count=0,search_count=0;
        for(int a=0;a<9;++a)for(int b=a+1;b<10;++b)for(int c=b+1;c<11;++c)for(int e=c+1;e<12;++e){
            std::array<int,4> zero{{a,b,c,e}};bool blocked=false;
            for(int i=0;i<4;++i)for(int j=i+1;j<4;++j)if(!pair[zero[i]][zero[j]])blocked=true;
            if(blocked){++pair_count;continue;}
            Active active;for(int i=0;i<4;++i){active[i].resize(domains[zero[i]].size());std::iota(active[i].begin(),active[i].end(),0);}
            if(!arc(domains,zero,active)){++arc_count;continue;}
            need(!union_search(domains,zero,active,14,total_nodes),"a root class survives14-block union search");++search_count;
        }
        need(pair_count+arc_count+search_count==495,"root fourset census");total_pair+=pair_count;total_arc+=arc_count;total_search+=search_count;
        std::cout<<"{\"class_closed\":"<<cid+1<<",\"pair\":"<<pair_count<<",\"arc\":"<<arc_count<<",\"search\":"<<search_count<<"}\n"<<std::flush;
    }
    std::vector<Mask> control(KNOWN30.begin(),KNOWN30.end());need(std::set<Mask>(control.begin(),control.end()).size()==30,"control distinctness");
    for(Mask b:control)need(b<8192&&pop(b)==7,"control block shape");
    std::vector<Mask> quads;combinations(13,4,0,0,quads);need(quads.size()==715,"control quadruple count");
    for(Mask q:quads)need(std::any_of(control.begin(),control.end(),[q](Mask b){return (b&q)==q;}),"control misses quadruple");
    std::vector<Mask> root;for(Mask b:control)if(has(b,12))root.push_back(Mask(b&4095u));need(root.size()==15,"control root degree");
    int retained=0;
    for(int q=0;q<12;++q){int degree=0;for(Mask b:control)if(has(b,q))++degree;if(degree!=15)continue;
        auto built=build_domain(root,q);Key actual;for(Mask b:control)if(has(b,q)&&!has(b,12)){need(index_of[b]>=0,"control outside block");actual.push_back(index_of[b]);}
        std::sort(actual.begin(),actual.end());need(std::any_of(built.first.begin(),built.first.end(),[&](const Pattern& p){return p.ids==actual;}),"actual30-cover pencil missing");++retained;
    }
    need(retained==3,"control minimum-point count");need(total_pair==31263&&total_arc==2355&&total_search==42,"frozen global partition");
    std::cout<<"{\"status\":\"PASS_COMPILED_CATALOG_RELATIVE_PENCIL_EXCLUSION\",\"root_classes\":68,\"domains\":816,\"quadruples\":33660,\"pair_closed\":"<<total_pair<<",\"arc_closed\":"<<total_arc<<",\"union_closed\":"<<total_search<<",\"search_nodes\":"<<total_nodes<<",\"positive30_quadruples\":715,\"retained_positive_pencils\":3}\n";
    return 0;
 }catch(const std::exception& e){std::cerr<<"FAIL: "<<e.what()<<'\n';return 1;}
}
