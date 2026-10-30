"""Independent raw21952-completion star census, using fixed source center0.
No imports from atlas/domain producer. Partial-edge incidence partition search.
"""
from pathlib import Path
from itertools import combinations,product,permutations
from collections import Counter,defaultdict
import json,time
R=Path(__file__).parent;P=tuple(range(12));labels='0123456789AB'
words=['014589','0167AB','2345AB','236789','02468A','02579B','13469B','13578A','03478B','03569A','12479A','12568B']
core=tuple(frozenset(labels.index(x) for x in w) for w in words);short=tuple(frozenset(range(4*g,4*g+4)) for g in range(3))

def need(ok,msg):
 if not ok:raise ValueError(msg)
# Explicit12 source-core automorphisms move every possible pointed center to0.
for center in P:
 g,a=divmod(center,4);order=[g]+[j for j in range(3) if j!=g];inv={old:new for new,old in enumerate(order)}
 perm={4*j+b:4*inv[j]+(b^a if inv[j] in (0,1) else b) for j in range(3) for b in range(4)}
 need(perm[center]==0,'point transitivity map')
 need({frozenset(perm[x] for x in b) for b in core}==set(core),'literal core transitivity')
 need({frozenset(perm[x] for x in b) for b in short}==set(short),'short partition transitivity')
choices=[tuple(q|set(t) for t in combinations(sorted(set(P)-q),2)) for q in short]
stars=defaultdict(set);raw=0
for extras in product(*choices):
 L=core+extras;star=tuple(sorted(tuple(sorted(b-{0})) for b in L if 0 in b));rest=tuple(sorted(tuple(sorted(b)) for b in L if 0 not in b));stars[star].add(rest);raw+=1
need(raw==21952,'raw source completeness')


def maps_by_partitions(source,sp,target,tp):
 sd={x:sum(x in b for b in source) for x in sp};td={x:sum(x in b for b in target) for x in tp}
 if sorted(sd.values())!=sorted(td.values()):return
 order=sorted(sp,key=lambda x:(sum(sd[y]==sd[x] for y in sp),x));images=[];unused=set(tp)
 def signature(rows,vertices):return Counter(tuple(int(v in b) for v in vertices) for b in rows)
 source_sig=[signature(source,order[:k]) for k in range(1,len(order)+1)]
 def dfs(k):
  if k==len(order):yield dict(zip(order,images));return
  for y in sorted(unused):
   if td[y]!=sd[order[k]]:continue
   images.append(y)
   if signature(target,images)==source_sig[k]:
    unused.remove(y);yield from dfs(k+1);unused.add(y)
   images.pop()
 yield from dfs(0)

outside=tuple(map(frozenset,combinations(P,7)));oid={b:i for i,b in enumerate(outside)}
fig6labels='0123456789TE';fig6words=['012345','012678','0129TE','0378TE','0456TE','045789','034569','13689E','14579E','14568T','13457T','23679T','24589T','24567E','23458E'];F6=tuple(frozenset(fig6labels.index(c) for c in w) for w in fig6words)
