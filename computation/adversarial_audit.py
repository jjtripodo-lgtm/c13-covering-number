#!/usr/bin/env python3
"""Deterministic differential controls; not a substitute for the full census."""
import sys,json,random,re,itertools,collections
from pathlib import Path
HERE=Path(__file__).resolve().parent
PROOF=HERE/'source/research/horizonmath/c13_classified_pencils'
if not PROOF.exists(): PROOF=HERE.parent/'source/research/horizonmath/c13_classified_pencils'
sys.path.insert(0,str(PROOF))
import verify_pencils as V
import independent_source as I
import peer_union_join as J

def need(ok,msg):
    if not ok: raise RuntimeError(msg)

def run():
    rng=random.Random(20261029)
    mapper_cases=0
    for n in (4,5,6):
        sp=tuple(range(n));tp=tuple(range(20,20+n))
        universe=[frozenset(s) for k in range(n+1) for s in itertools.combinations(sp,k)]
        for case in range(80):
            source=rng.sample(universe,rng.randrange(len(universe)+1))
            image=rng.sample(tp,n);g=dict(zip(sp,image))
            target=[frozenset(g[x] for x in b) for b in source]
            if case%2 and target:
                target=list(set(target)^{frozenset(rng.sample(tp,rng.randrange(n+1)))})
            expected=set()
            for perm in itertools.permutations(tp):
                m=dict(zip(sp,perm))
                if {frozenset(m[x] for x in b) for b in source}==set(target):expected.add(perm)
            for mapper in (V.star_maps,I.maps_by_partitions):
                got={tuple(m[x] for x in sp) for m in mapper(source,sp,target,tp)}
                need(got==expected,'hypergraph isomorphism differential failed')
            mapper_cases+=1
    join_cases=0;positive_cases=0;budget_checks=0
    for case in range(240):
        qs=tuple(sorted(rng.sample(range(12),4)))
        # Seed one shared family for half the cases; others use independent pencils.
        shared=set(rng.sample(range(792),rng.randrange(1,19)))
        domains={}
        for q in qs:
            pool=[i for i,b in enumerate(J.BLOCKS) if q in b]
            pats=[]
            if case%2==0:pats.append(frozenset(i for i in shared if q in J.BLOCKS[i]))
            for _ in range(rng.randrange(1,5)):
                pats.append(frozenset(rng.sample(pool,rng.randrange(0,9))))
            domains[q]=list(dict.fromkeys(pats))
        hist=collections.Counter()
        for choices in itertools.product(*(domains[q] for q in qs)):
            if all({i for i in choices[a] if qs[b] in J.BLOCKS[i]}=={i for i in choices[b] if qs[a] in J.BLOCKS[i]} for a,b in itertools.combinations(range(4),2)):
                hist[len(set().union(*choices))]+=1
        got=J.join_pencils(qs,domains)
        need(got['compatible_tuples']==sum(hist.values()),'tuple count mismatch')
        need(got['union_size_histogram']==dict(sorted(hist.items())),'union histogram mismatch')
        reduced,_=V.arc_consistency({q:tuple(sum(1<<i for i in p) for p in domains[q]) for q in qs})
        for budget in (0,7,13,14,15,25):
            witness,_=V.compatible_union(reduced,budget)
            need((witness is not None)==any(k<=budget for k in hist),'budget or arc filtering unsound')
            budget_checks+=1
        positive_cases+=bool(hist);join_cases+=1
    text=(HERE/'C13_manuscript.tex').read_text()
    rows=re.findall(r'\\\{([0-9,]+)\\\}',text)
    blocks=[frozenset(map(int,r.split(','))) for r in rows if len(r.split(','))==7]
    need(len(blocks)==len(set(blocks))==30,'manuscript witness extraction')
    needs=list(map(frozenset,itertools.combinations(range(1,14),4)))
    need(all(any(t<=b for b in blocks) for t in needs),'manuscript witness coverage')
    essential=0
    for removed in range(30):
        need(any(not any(t<=b for j,b in enumerate(blocks) if j!=removed) for t in needs),'deleted block did not spoil witness')
        essential+=1
    return {'status':'PASS_DIFFERENTIAL_AND_MANUSCRIPT_CONTROLS','seed':20261029,'mixed_rank_hypergraph_mapper_cases':mapper_cases,'literal_product_join_cases':join_cases,'join_cases_with_solution':positive_cases,'budget_and_arc_checks':budget_checks,'manuscript_foursets':len(needs),'single_block_deletions_rejected':essential,'boundary':'Finite differential controls, not a new proof or external specialist review.'}

if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
