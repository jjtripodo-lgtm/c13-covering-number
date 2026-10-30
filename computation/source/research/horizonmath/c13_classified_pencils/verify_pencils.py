#!/usr/bin/env python3
"""Exact classified-minimum-link overlap obstruction for 29-block C13 covers.

All checks are explicit and remain active under python -O. No solver, floating
arithmetic, or legacy LP/profile receipt is used. Completeness of the displayed
68-link catalog is separately reconstructed by independent_raw_replay.py;
its mathematical classification dependency is stated in the report.
"""
from pathlib import Path
from itertools import combinations
from collections import Counter
import hashlib,json,sys
ROOT=Path(__file__).parent
CATALOG_SHA='019af94696fb4cf543fbc741401141d53126200c3193a21193c6720f81a56510'
POINTS=tuple(range(12));BLOCKS=tuple(map(frozenset,combinations(POINTS,7)))
INDEX={b:i for i,b in enumerate(BLOCKS)}
POINT_MASKS=tuple(sum(1<<i for i,b in enumerate(BLOCKS) if p in b) for p in POINTS)

def require(ok,why):
    if not ok:raise ValueError(why)

def parse_catalog(data):
    require(data['schema']=='c13-minimum-link-catalog-v1','catalog schema')
    require(len(data['classes'])==68,'68 catalog classes required')
    links=[]
    for i,c in enumerate(data['classes'],1):
        require(type(c['class_id']) is int and c['class_id']==i,'catalog class order')
        rows=c['blocks'];require(len(rows)==15,'15 link blocks required')
        require(all(len(b)==6 and len(set(b))==6 and all(type(p) is int and p in POINTS for p in b) for b in rows),'link block shape')
        L=tuple(map(frozenset,rows));require(len(set(L))==15,'duplicate link block')
        require(all(any(set(t)<=b for b in L) for t in combinations(POINTS,3)),'link triple coverage')
        degrees=[sum(p in b for b in L) for p in POINTS]
        require(max(degrees)<=9 if i<68 else sorted(degrees)==[7]*10+[10]*2,'link degree class')
        links.append(L)
    return tuple(links)

def load_catalog(path=ROOT/'minimum_link_catalog.json'):
    raw=Path(path).read_bytes();require(hashlib.sha256(raw).hexdigest()==CATALOG_SHA,'catalog byte integrity')
    return parse_catalog(json.loads(raw))

def star_maps(source,sp,target,tp):
    """All unrestricted point bijections preserving the star hypergraph."""
    sd={a:sum(a in b for b in source) for a in sp};td={a:sum(a in b for b in target) for a in tp}
    if sorted(sd.values())!=sorted(td.values()):return
    sm={(a,b):sum({a,b}<=c for c in source) for a in sp for b in sp};tm={(a,b):sum({a,b}<=c for c in target) for a in tp for b in tp}
    sig=lambda a,points,deg,m:(deg[a],tuple(sorted((deg[b],m[a,b]) for b in points if b!=a)))
    cand={a:[b for b in tp if sig(a,sp,sd,sm)==sig(b,tp,td,tm)] for a in sp}
    if any(not c for c in cand.values()):return
    order=sorted(sp,key=lambda a:(len(cand[a]),-sd[a],a));mapping={};used=set();ts=set(target)
    def visit(k):
        if k==len(sp):
            if {frozenset(mapping[a] for a in b) for b in source}==ts:yield dict(mapping)
            return
        a=order[k]
        for b in cand[a]:
            if b in used or any(sm[a,c]!=tm[b,d] for c,d in mapping.items()):continue
            mapping[a]=b;used.add(b);yield from visit(k+1);used.remove(b);del mapping[a]
    yield from visit(0)

def invariant(star,points):
    deg={p:sum(p in b for b in star) for p in points}
    pair={(p,q):sum({p,q}<=b for b in star) for p in points for q in points}
    return len(star),tuple(sorted((deg[p],tuple(sorted((deg[q],pair[p,q]) for q in points if q!=p))) for p in points))

def direct_domain(target,tp,q,links):
    patterns=set()
    for L in links:
        for center in POINTS:
            source=tuple(b-{center} for b in L if center in b)
            if len(source)!=len(target):continue
            for g in star_maps(source,[p for p in POINTS if p!=center],target,tp):
                patterns.add(tuple(sorted(INDEX[frozenset(g[p] for p in b)|{q}] for b in L if center not in b)))
    return patterns

def domain_for(L,q,links,templates):
    star=tuple(b-{q} for b in L if q in b);tp=[p for p in POINTS if p!=q];sig=invariant(star,tp)
    for i,t in enumerate(templates):
        if sig!=t['invariant']:continue
        g=next(star_maps(t['star'],t['points'],star,tp),None)
        if g is not None:
            g[t['center']]=q
            return {tuple(sorted(INDEX[frozenset(g[p] for p in BLOCKS[j])] for j in pattern)) for pattern in t['patterns']},i
    patterns=direct_domain(star,tp,q,links);i=len(templates)
    templates.append({'invariant':sig,'star':star,'points':tp,'center':q,'patterns':patterns})
    return patterns,i

def arc_consistency(domains):
    """Synchronous removal: retain a pencil only with support at every point."""
    active={q:tuple(ds) for q,ds in domains.items()};rounds=[]
    while all(active.values()):
        sig={(q,s):{pat&POINT_MASKS[s] for pat in active[q]} for q in active for s in active if q!=s}
        new={q:tuple(pat for pat in active[q] if all(pat&POINT_MASKS[s] in sig[s,q] for s in active if s!=q)) for q in active}
        rounds.append([len(new[q]) for q in sorted(new)])
        if new==active:return new,rounds
        active=new
    return active,rounds

def compatible_union(domains,budget=14):
    """Exhaust all pair-compatible pencil choices with union at most budget.

    Positive return is only a pencil assignment, not a covering. An exhausted
    negative is the exact necessary-condition obstruction used in this proof.
    No degree pruning, forced-set intersection, or terminal cover checker.
    """
    require(type(budget) is int and budget>=0,'nonnegative union budget')
    require(all(type(q) is int and q in POINTS for q in domains),'pencil point range')
    require(all(type(pat) is int and pat>=0 and pat>>792==0 and pat & ~POINT_MASKS[q]==0 for q,ds in domains.items() for pat in ds),'pencil block incidence/range')
    nodes=0
    def visit(doms,union,chosen):
        nonlocal nodes
        nodes+=1
        if union.bit_count()>budget:return None
        if not doms:return {'union':union,'pencils':chosen}
        q=min(doms,key=lambda x:len(doms[x]))
        for pat in doms[q]:
            enlarged=union|pat
            if enlarged.bit_count()>budget:continue
            remaining={};possible=True
            for s,ds in doms.items():
                if s==q:continue
                sig=pat&POINT_MASKS[s]
                kept=tuple(other for other in ds if other&POINT_MASKS[q]==sig)
                if not kept:possible=False;break
                remaining[s]=kept
            if possible:
                result=visit(remaining,enlarged,chosen+[(q,pat)])
                if result is not None:return result
        return None
    result=visit({q:tuple(ds) for q,ds in domains.items()},0,[])
    return result,nodes

def check_class(cid,L,domains):
    pair={(q,s):bool({pat&POINT_MASKS[s] for pat in domains[q]}&{pat&POINT_MASKS[q] for pat in domains[s]}) for q,s in combinations(POINTS,2)}
    blocked=arc_closed=search_closed=0;searches=[]
    for zeros in combinations(POINTS,4):
        if any(not pair[p] for p in combinations(zeros,2)):
            blocked+=1;continue
        reduced,rounds=arc_consistency({q:domains[q] for q in zeros})
        if not all(reduced.values()):arc_closed+=1;continue
        result,nodes=compatible_union(reduced,14)
        require(result is None,f'class{cid} zero set{zeros} survives14-block pencil gate')
        search_closed+=1;searches.append({'minimum_points':list(zeros),'post_arc_domains':{str(q):len(ds) for q,ds in reduced.items()},'nodes':nodes})
    require(blocked+arc_closed+search_closed==495,'four-point census')
    return {'class_id':cid,'pair_closed':blocked,'arc_closed':arc_closed,'union_search_closed':search_closed,'searches':searches}

def positive_control(links,templates):
    data=json.loads((ROOT/'known30_control.json').read_text())
    require(all(len(b)==7 and len(set(b))==7 and all(type(x) is int and 0<=x<13 for x in b) for b in data['blocks']),'30-cover control point domain')
    full=tuple(map(frozenset,data['blocks']))
    require(len(full)==len(set(full))==30 and all(len(b)==7 for b in full),'30-cover control shape')
    require(all(any(set(t)<=b for b in full) for t in combinations(range(13),4)),'715 control quadruples')
    L=tuple(b-{12} for b in full if 12 in b);require(len(L)==15,'control minimum root')
    minimum=[q for q in POINTS if sum(q in b for b in full)==15];require(minimum==[0,4,8],'control minimum points')
    pencils={}
    for q in minimum:
        patterns,_=domain_for(L,q,links,templates)
        actual=tuple(sorted(INDEX[b] for b in full if q in b and 12 not in b))
        require(actual in patterns,'actual30-cover pencil absent')
        pencils[q]=(sum(1<<j for j in actual),)
    witness,_=compatible_union(pencils,15);require(witness is not None,'actual30 pencil assignment rejected')
    return {'cover_blocks':30,'covered_quadruples':715,'additional_minimum_points':minimum,'retained_actual_pencils':3,'outside_blocks':15}

def verify(progress=False):
    links=load_catalog();templates=[];classes=[];domain_rows=[]
    frozen=json.loads((ROOT/'domain_reconstruction_receipt.json').read_text())
    require(frozen['status']=='PASS_INDEPENDENT_ALL68_DOMAIN_REBUILD' and len(frozen['classes'])==68,'independent domain receipt')
    for cid,L in enumerate(links,1):
        domains={};dr=[]
        for q in POINTS:
            pats,ti=domain_for(L,q,links,templates);ordered=sorted(pats)
            digest=hashlib.sha256(json.dumps(ordered,separators=(',',':')).encode()).hexdigest()
            expected=frozen['classes'][cid-1]['domains'][q]
            require(expected['point']==q and expected['patterns']==len(pats) and expected['sha256']==digest,'independent domain hash disagreement')
            domains[q]=tuple(sorted(sum(1<<j for j in pat) for pat in pats))
            dr.append({'point':q,'patterns':len(pats),'sha256':digest})
        classes.append(check_class(cid,L,domains));domain_rows.append({'class_id':cid,'domains':dr})
        if progress:print(f'class{cid}: all495 minimum-point quadruples excluded',file=sys.stderr,flush=True)
    control=positive_control(links,templates)
    return {'status':'PASS_EXACT_ALL68_CLASSIFIED_PENCIL_OBSTRUCTION','root_link_classes':68,'figure1_classes':67,'exceptional_figure6_included':True,'minimum_point_quadruples':68*495,'remaining_14_block_pencil_assignments':0,'pair_closed':sum(c['pair_closed'] for c in classes),'arc_closed':sum(c['arc_closed'] for c in classes),'union_search_closed':sum(c['union_search_closed'] for c in classes),'classes':classes,'domain_digest':hashlib.sha256(json.dumps(domain_rows,separators=(',',':'),sort_keys=True).encode()).hexdigest(),'positive_control':control,'classification_dependency':'Published C(12,6,3)=15 and complete Figure1/Figure6 minimum-link classification, independently checked raw Figure1 catalog/domain reconstruction. No external proof of that classification is reproduced here.'}

if __name__=='__main__':print(json.dumps(verify(progress='--progress' in sys.argv),indent=2,sort_keys=True))
