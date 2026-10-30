"""Independent literal/raw-source full68-root domain rebuild; no atlas imports."""
from independent_source import *
from peer_union_join import check_union, self_test
import hashlib
start=time.time()
# Independently exhaust quartet permutations and within-quartet permutations.
coregroup=[];p4=list(permutations(range(4)))
for gp in permutations(range(3)):
 for within in product(p4,repeat=3):
  g=tuple(4*gp[i//4]+within[i//4][i%4] for i in P)
  if {frozenset(g[x] for x in b) for b in core}==set(core):coregroup.append(g)
need(len(coregroup)==576,'independent base group')
def key(extras):return tuple(sorted(tuple(sorted(b)) for b in extras))
unseen={key(extras) for extras in product(*choices)};reps=[];sizes=[]
need(len(unseen)==21952,'independent raw root census')
while unseen:
 rep=min(unseen);orb={key(frozenset(g[x] for x in b) for b in rep) for g in coregroup};need(orb<=unseen,'orbit partition overlap');unseen-=orb;reps.append(rep);sizes.append(len(orb))
need(len(reps)==67 and sum(sizes)==21952,'independent root quotient')
rootlinks=[core+tuple(frozenset(b) for b in rep) for rep in reps]+[F6]
frozen=json.load(open(R/'domain_reconstruction_receipt.json'));catalog=json.load(open(R/'minimum_link_catalog.json'));templates=[];results=[];self_test()
need(len(catalog['classes'])==68 and len(frozen['classes'])==68,'all68 frozen classes')

def inv(star,vertices):
 d={x:sum(x in b for b in star) for x in vertices}
 return len(star),tuple(sorted((d[x],tuple(sorted(sum({x,y}<=set(b) for b in star) for y in vertices if y!=x))) for x in vertices))

def direct_domain(target,tp,q):
 found=set();f6=set()
 for star,rests in stars.items():
  if len(star)!=len(target):continue
  for g in maps_by_partitions(star,list(range(1,12)),target,tp):
   for rest in rests:found.add(tuple(sorted(oid[frozenset(g[x] for x in b)|{q}] for b in rest)))
 for center in P:
  star=[b-{center} for b in F6 if center in b]
  if len(star)!=len(target):continue
  for g in maps_by_partitions(star,[p for p in P if p!=center],target,tp):
   f6.add(tuple(sorted(oid[frozenset(g[x] for x in b)|{q}] for b in F6 if center not in b)))
 return found|f6,len(f6)


import sys

def classify(cid,domains):
    # Every ordered pair retains the literal joint-block set of each pencil.
    signatures={(q,s):[frozenset(i for i in pat if s in outside[i]) for pat in domains[q]] for q in P for s in P if q!=s}
    pairs={(q,s):bool(set(signatures[q,s])&set(signatures[s,q])) for q,s in combinations(P,2)}
    blocked=closed=0;joins=[]
    for zeros in combinations(P,4):
        if any(not pairs[pair] for pair in combinations(zeros,2)):
            blocked+=1;continue
        active={q:set(range(len(domains[q]))) for q in zeros}
        while all(active.values()):
            available={(q,s):{signatures[q,s][i] for i in active[q]} for q in zeros for s in zeros if q!=s}
            newer={q:{i for i in active[q] if all(signatures[q,s][i] in available[s,q] for s in zeros if q!=s)} for q in zeros}
            if newer==active:break
            active=newer
        if not all(active.values()):closed+=1;continue
        remaining={q:[domains[q][i] for i in sorted(active[q])] for q in zeros}
        joined=check_union(remaining)
        need(joined['compatible_tuples']>0 and joined['minimum_union']>14,'live14-block minimum pencil tuple')
        joins.append({'minimum_points':list(zeros),**joined})
    need(blocked+closed+len(joins)==495,'independent fourset completeness')
    return {'class_id':cid,'foursets':495,'pair_closed':blocked,'arc_closed':closed,'joins':joins}

for cid,L in enumerate(rootlinks,1):
 need({tuple(sorted(b)) for b in L}=={tuple(b) for b in catalog['classes'][cid-1]['blocks']},'raw catalog completeness comparison')
 row=[];full_domains={}
 for q in P:
  target=tuple(b-{q} for b in L if q in b);tp=[p for p in P if p!=q];sig=inv(target,tp);found=None
  for ti,t in enumerate(templates):
   if sig!=t['invariant']:continue
   g=next(maps_by_partitions(t['star'],t['points'],target,tp),None)
   if g is not None:
    g[t['center']]=q;found={tuple(sorted(oid[frozenset(g[x] for x in outside[j])] for j in pat)) for pat in t['patterns']};break
  if found is None:
   found,nf6=direct_domain(target,tp,q);ti=len(templates);templates.append({'invariant':sig,'star':target,'points':tp,'center':q,'patterns':found,'figure6_patterns':nf6})
   pass
  ordered=sorted(found);digest=hashlib.sha256(json.dumps(ordered,separators=(',',':')).encode()).hexdigest()
  expected=frozen['classes'][cid-1]['domains'][q];need(expected['point']==q and expected['patterns']==len(found) and expected['sha256']==digest,'independent domain integrity/completeness disagreement')
  full_domains[q]=tuple(map(frozenset,ordered));row.append({'point':q,'star_type':ti,'patterns':len(found),'sha256':digest})
 result=classify(cid,full_domains);result['domains']=row;results.append(result)
 if '--progress' in sys.argv:print('class',cid,'PASS independent exact join',file=sys.stderr,flush=True)
control=json.load(open(R/'known30_control.json'))['blocks']
need(all(len(b)==7 and len(set(b))==7 and all(type(p) is int and 0<=p<13 for p in b) for b in control),'independent30 point domain')
masks=[sum(1<<p for p in b) for b in control]
need(len(masks)==len(set(masks))==30 and all(m.bit_count()==7 for m in masks),'independent30 control shape')
need(all(any(m&t==t for m in masks) for t in (sum(1<<p for p in q) for q in combinations(range(13),4))),'independent715 positive control')
result={'status':'PASS_INDEPENDENT_GLOBAL29_PENCIL_EXCLUSION','source_raw_completions':21952,'source_core_group':576,'figure1_root_classes':67,'exceptional_figure6':True,'source_star_types':len(templates),'root_classes':len(results),'point_quadruples':sum(x['foursets'] for x in results),'pair_closed':sum(x['pair_closed'] for x in results),'arc_closed':sum(x['arc_closed'] for x in results),'joined_cases':sum(len(x['joins']) for x in results),'compatible_tuples':sum(j['compatible_tuples'] for x in results for j in x['joins']),'minimum_joined_union':min(j['minimum_union'] for x in results for j in x['joins']),'positive30_quadruples':715,'classes':results}
rows_for_hash=[{'class_id':c['class_id'],'domains':[{k:d[k] for k in ['point','patterns','sha256']} for d in c['domains']]} for c in results]
result['domain_digest']=hashlib.sha256(json.dumps(rows_for_hash,separators=(',',':'),sort_keys=True).encode()).hexdigest()
need(result['root_classes']==68 and result['point_quadruples']==33660,'global census complete')
need(result['joined_cases']==42 and result['minimum_joined_union']==15,'frozen integral frontier')
print(json.dumps(result,indent=2,sort_keys=True))
