"""Read a compiled replay and compare every domain and census to frozen proof."""
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('output',type=Path);p.add_argument('--proof-dir',type=Path,default=Path(__file__).resolve().parent.parent);a=p.parse_args()
frozen=json.loads((a.proof_dir/'domain_reconstruction_receipt.json').read_text());expected={(c['class_id'],d['point']):d for c in frozen['classes'] for d in c['domains']}
rows=[json.loads(line) for line in a.output.read_text().splitlines()];seen=set();closed={};summary=None
for r in rows:
 if 'point' in r:
  k=(r['class_id'],r['point'])
  if k in seen or k not in expected:raise ValueError('duplicate or unknown domain')
  seen.add(k);e=expected[k]
  if r['patterns']!=e['patterns'] or r['sha256']!=e['sha256']:raise ValueError(('domain mismatch',k))
 elif 'class_closed' in r:
  c=r['class_closed']
  if c in closed or not 1<=c<=68 or r['pair']+r['arc']+r['search']!=495:raise ValueError('class census')
  closed[c]=r
 elif 'status' in r:
  if summary is not None:raise ValueError('duplicate summary')
  summary=r
 else:raise ValueError('unknown record')
if len(seen)!=816 or len(closed)!=68 or summary is None:raise ValueError('incomplete replay')
if summary['status']!='PASS_COMPILED_CATALOG_RELATIVE_PENCIL_EXCLUSION':raise ValueError('bad final status')
for key,target in [('pair_closed',31263),('arc_closed',2355),('union_closed',42),('positive30_quadruples',715),('retained_positive_pencils',3)]:
 if summary[key]!=target:raise ValueError(('final count',key))
print(json.dumps({'status':'PASS_COMPILED_DOMAIN_AND_GLOBAL_CENSUS_CROSSCHECK','verified_domain_hashes':816,'class_censuses':68,'output_sha256':hashlib.sha256(a.output.read_bytes()).hexdigest(),'summary':summary,'boundary':'Third catalog-relative C++ replay; complete catalog/classification remains independently established by the Python raw-source proof and published theorem.'},indent=2,sort_keys=True))
