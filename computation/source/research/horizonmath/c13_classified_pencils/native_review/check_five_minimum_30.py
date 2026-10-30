"""Bounded scout: test every compatible four-pencil union as a30-cover.

Completeness depends on the separately checked all68/all495 domain/arc census.
This script does not modify or form part of the currently frozen proof packet.
"""
import json,sys,hashlib,time
from pathlib import Path
from itertools import combinations
from collections import Counter
P=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(P))
from verify_pencils import load_catalog,domain_for
catalog=load_catalog();templates=[];frozen=json.load(open(P/'domain_reconstruction_receipt.json'));global_replay=json.load(open(P/'independent_replay.json'));blocks=tuple(map(frozenset,combinations(range(12),7)))

def need(ok,msg):
 if not ok:raise ValueError(msg)

def tuples(active,zeros):
 adj={}
 for a,b in combinations(range(4),2):
  qa,qb=zeros[a],zeros[b];lookup={}
  for j,p in enumerate(active[qb]):lookup.setdefault(frozenset(i for i in p if qa in blocks[i]),set()).add(j)
  adj[a,b]=[lookup.get(frozenset(i for i in p if qb in blocks[i]),set()) for p in active[qa]]
 for ia,pa in enumerate(active[zeros[0]]):
  for ib in sorted(adj[0,1][ia]):
   pb=active[zeros[1]][ib]
   for ic in sorted(adj[0,2][ia]&adj[1,2][ib]):
    pc=active[zeros[2]][ic]
    for id_ in sorted(adj[0,3][ia]&adj[1,3][ib]&adj[2,3][ic]):yield(pa,pb,pc,active[zeros[3]][id_])

rows=[];valid=[];start=time.time()
for entry in global_replay['classes']:
 cid=entry['class_id'];L=catalog[cid-1]
 for case in entry['joins']:
  zeros=case['minimum_points'];active={}
  for q in zeros:
   ds,_=domain_for(L,q,catalog,templates);ordered=sorted(tuple(p) for p in ds);expected=frozen['classes'][cid-1]['domains'][q]
   need(hashlib.sha256(json.dumps(ordered,separators=(',',':')).encode()).hexdigest()==expected['sha256'],'domain SHA')
   active[q]=list(map(frozenset,ordered))
  while True:
   available={(q,s):{frozenset(i for i in pat if s in blocks[i]) for pat in active[q]} for q in zeros for s in zeros if q!=s}
   newer={q:[pat for pat in active[q] if all(frozenset(i for i in pat if s in blocks[i]) in available[s,q] for s in zeros if s!=q)] for q in zeros}
   if newer==active:break
   active=newer;need(all(active.values()),'unexpected empty residual')
  Y=set(range(12))-set(zeros);targets=[frozenset(t) for t in combinations(sorted(Y),4) if not any(set(t)<=b for b in L)]
  cover=[sum(1<<i for i,t in enumerate(targets) if t<=b) for b in blocks];wanted=(1<<len(targets))-1;hist=Counter();count=0;best=None
  for choices in tuples(active,zeros):
   union=frozenset().union(*choices);need(len(union)==15,'union not15');coverage=0
   for j in union:coverage|=cover[j]
   missing=(wanted&~coverage).bit_count();hist[missing]+=1;count+=1
   if best is None or missing<best['missing']:best={'missing':missing,'union':sorted(union),'uncovered':[sorted(t) for i,t in enumerate(targets) if not(coverage>>i&1)]}
   if missing==0:
    full=[b|{12} for b in L]+[blocks[j] for j in union]
    need(all(any(set(t)<=b for b in full) for t in combinations(range(13),4)),'positive direct715 check')
    valid.append({'class_id':cid,'zero_points':zeros,'blocks':[sorted(b) for b in full]})
  need(count==case['compatible_tuples'],'exact tuple count disagreement')
  rows.append({'class_id':cid,'zero_points':zeros,'target_quadruples':len(targets),'compatible_tuples':count,'uncovered_histogram':dict(sorted(hist.items())),'best':best})
  out={'status':'EXACT30_MINIMUM_LINK_EXTENSION_SCOUT','cases':len(rows),'tuple_count':sum(r['compatible_tuples'] for r in rows),'valid30_candidates':len(valid),'minimum_uncovered':min(r['best']['missing'] for r in rows),'rows':rows,'valid_candidates':valid,'boundary':'Finite scout on complete classified minimum-link tuples; any stronger30-cover degree theorem needs independent extension-coverage replay and source-completeness composition.'}
  Path(__file__).with_name('five-minimum-30-scout.json').write_text(json.dumps(out,indent=2))
  print(cid,zeros,count,dict(hist),'valid',len(valid),round(time.time()-start,1),flush=True)
print('COMPLETE',sum(r['compatible_tuples'] for r in rows),'valid',len(valid),flush=True)
