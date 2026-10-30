#!/usr/bin/env python3
"""Independent complete six-relation join for four classified pencils.

Authored by the Erdos700 worker. No producer/atlas/CSP imports. Every compatible
quadruple is enumerated; no union-size, forced-block, or degree pruning is used.
Domain completeness and published minimum-link classification are prerequisites.
"""
from itertools import combinations
from collections import Counter

BLOCKS=tuple(frozenset(t) for t in combinations(range(12),7))


def need(ok,message):
    if not ok:raise ValueError(message)


def join_pencils(zeros,domains):
    """domains maps each of four distinct points to complete block-index sets.

    Returns compatible tuple count, union histogram and a minimum witness.
    Block indices use lexicographic combinations(range(12),7). A None minimum
    means no pair-compatible tuple exists. potential_cartesian_size is ONLY
    an input-domain statistic, not an inflated count of performed checks.
    """
    zeros=tuple(zeros)
    need(len(zeros)==4 and len(set(zeros))==4 and
         all(type(q) is int and 0<=q<12 for q in zeros),'four distinct points required')
    active={};potential=1
    for q in zeros:
        raw=list(domains[q]);pats=[frozenset(p) for p in raw]
        need(all(len(p)==len(r) for p,r in zip(pats,raw)),'duplicate block id')
        need(len(pats)==len(set(pats)),'duplicate pencil')
        need(all(all(type(i) is int and 0<=i<792 and q in BLOCKS[i] for i in p) for p in pats),
             'invalid block/point membership')
        active[q]=pats;potential*=len(pats)
    adj={}
    for a,b in combinations(range(4),2):
        qa,qb=zeros[a],zeros[b];lookup={}
        for j,pat in enumerate(active[qb]):
            signature=frozenset(i for i in pat if qa in BLOCKS[i])
            lookup.setdefault(signature,set()).add(j)
        adj[a,b]=[lookup.get(frozenset(i for i in pat if qb in BLOCKS[i]),set())
                  for pat in active[qa]]
    histogram=Counter();compatible=0;witness=None
    for ia,pa in enumerate(active[zeros[0]]):
        for ib in sorted(adj[0,1][ia]):
            pb=active[zeros[1]][ib]
            for ic in sorted(adj[0,2][ia]&adj[1,2][ib]):
                pc=active[zeros[2]][ic]
                for id_ in sorted(adj[0,3][ia]&adj[1,3][ib]&adj[2,3][ic]):
                    pd=active[zeros[3]][id_];choices=(pa,pb,pc,pd)
                    need(all(frozenset(i for i in choices[a] if zeros[b] in BLOCKS[i]) ==
                             frozenset(i for i in choices[b] if zeros[a] in BLOCKS[i])
                             for a,b in combinations(range(4),2)), 'invalid joined tuple')
                    compatible+=1;union=set().union(*choices);histogram[len(union)]+=1
                    if witness is None or len(union)<witness['size']:
                        witness={'size':len(union),'pencils':[sorted(p) for p in choices],
                                 'union':sorted(union)}
    return {'potential_cartesian_size':potential,'compatible_tuples':compatible,
            'union_size_histogram':dict(sorted(histogram.items())),
            'minimum_union':None if witness is None else witness['size'],
            'minimum_union_witness':witness}


def check_union(active):
    """Portable entry point: map four point labels to their pencil domains."""
    return join_pencils(tuple(sorted(active)),active)


def self_test():
    zeros=(0,1,2,3);selected=set(range(20,420,30))
    domains={q:[[i for i in sorted(selected) if q in BLOCKS[i]]] for q in zeros}
    got=join_pencils(zeros,domains)
    actual=set().union(*(set(domains[q][0]) for q in zeros))
    need(got['compatible_tuples']==1 and got['minimum_union']==len(actual)<=14,'positive14-block control failed')
    bad={q:[list(domains[q][0])] for q in zeros};bad[0][0].append(0)
    need(join_pencils(zeros,bad)['compatible_tuples']==0,'incompatible pair control failed')
    tampered={q:[list(domains[q][0])] for q in zeros};tampered[0][0].append(792)
    try:join_pencils(zeros,tampered)
    except ValueError:pass
    else:raise ValueError('malformed block passed')
    return {'status':'PASS_TUPLE_JOIN_CONTROLS','valid_tuple_union':len(actual),
            'incompatible_tuple_rejected':True,'malformed_block_rejected':True}

if __name__=='__main__':
    import json
    print(json.dumps(self_test(),sort_keys=True))
