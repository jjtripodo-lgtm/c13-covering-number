"""Fail-closed crosscheck of complete budget15 C++ replay and Python coverage."""
import argparse,hashlib,json
from pathlib import Path

def check(rows,frozen,scout):
 def need(b,m):
  if not b:raise ValueError(m)
 expected={(c['class_id'],d['point']):d for c in frozen['classes'] for d in c['domains']}
 seen=set();classes={};cases={};summary=final=None
 for r in rows:
  if 'point' in r:
   k=(r['class_id'],r['point']);need(k in expected and k not in seen,'domain identity');seen.add(k)
   need(r['patterns']==expected[k]['patterns'] and r['sha256']==expected[k]['sha256'],'domain content')
  elif 'class_closed' in r:
   c=r['class_closed'];need(c not in classes and 1<=c<=68,'class identity');classes[c]=r
   need(all(type(r[k]) is int and 0<=r[k]<=495 for k in ('pair','arc','search')),'class count shape');need(r['pair']+r['arc']+r['search']==495,'class total')
  elif 'rigidity_class' in r:
   k=(r['rigidity_class'],tuple(r['minimum_points']));need(k not in cases,'duplicate join');cases[k]=r
   need(len(k[1])==4 and tuple(sorted(set(k[1])))==k[1],'point set')
   need(all(int(g)>=2 and type(n) is int and n>0 for g,n in r['uncovered_histogram'].items()),'coverage gap')
   need(sum(r['uncovered_histogram'].values())==r['tuples'],'tuple total')
  elif 'status' in r:need(summary is None,'duplicate summary');summary=r
  elif 'rigidity_status' in r:need(final is None,'duplicate final');final=r
  else:raise ValueError('unknown record')
 need(len(seen)==816 and len(classes)==68 and len(cases)==42,'incomplete replay')
 need(summary is not None and summary['status']=='PASS_COMPILED_CATALOG_RELATIVE_BUDGET15_RIGIDITY','budget15 summary')
 for field,target in [('pair_closed',31263),('arc_closed',2355),('union_closed',42),('quadruples',33660),('positive30_quadruples',715),('retained_positive_pencils',3)]:need(summary[field]==target,'summary count')
 for field,key in [('pair_closed','pair'),('arc_closed','arc'),('union_closed','search')]:need(sum(r[key] for r in classes.values())==summary[field],'closure sum')
 need(final=={'rigidity_status':'COMPLETE_NATIVE_30_COVER_MINIMUM_POINT_TEST','tuples':280152,'valid30':0,'minimum_uncovered':2},'final assertion')
 need(sum(r['tuples'] for r in cases.values())==280152,'global tuple sum')
 reference={(r['class_id'],tuple(r['zero_points'])):r for r in scout['rows']};need(reference.keys()==cases.keys(),'independent case coverage')
 for k,r in cases.items():need(r['uncovered_histogram']==reference[k]['uncovered_histogram'] and r['tuples']==reference[k]['compatible_tuples'],'independent coverage mismatch')
 return {'status':'PASS_FULL_BUDGET15_RIGIDITY','domains':816,'foursets':33660,'joins':42,'compatible_tuples':280152,'valid30':0,'minimum_uncovered':2,'sharp_control_minimum_points':4}

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('output',type=Path);p.add_argument('--proof-dir',type=Path,required=True);p.add_argument('--scout',type=Path,default=Path(__file__).with_name('five-minimum-30-scout.json'));a=p.parse_args()
 receipt=check([json.loads(l) for l in a.output.read_text().splitlines()],json.loads((a.proof_dir/'domain_reconstruction_receipt.json').read_text()),json.loads(a.scout.read_text()))
 receipt['output_sha256']=hashlib.sha256(a.output.read_bytes()).hexdigest();print(json.dumps(receipt,sort_keys=True,indent=2))
