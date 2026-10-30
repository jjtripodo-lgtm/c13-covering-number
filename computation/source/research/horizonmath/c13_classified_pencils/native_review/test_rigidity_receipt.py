import copy,json,unittest
from pathlib import Path
from validate_rigidity import check
P=Path(__file__).parent
F=P.parent
class Tests(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.rows=[json.loads(l) for l in (P/'native-rigidity-budget15.jsonl').read_text().splitlines()];cls.frozen=json.loads((F/'domain_reconstruction_receipt.json').read_text());cls.scout=json.loads((P/'five-minimum-30-scout.json').read_text())
 def reject(self,rows,pattern):
  with self.assertRaisesRegex(ValueError,pattern):check(rows,self.frozen,self.scout)
 def test_positive(self):self.assertEqual(check(self.rows,self.frozen,self.scout)['sharp_control_minimum_points'],4)
 def test_missing_domain(self):self.reject(self.rows[1:],'incomplete')
 def test_duplicate_domain(self):self.reject(self.rows+[self.rows[0]],'domain identity')
 def test_hash(self):
  r=copy.deepcopy(self.rows);r[0]['sha256']='0'*64;self.reject(r,'domain content')
 def test_budget14_status(self):
  r=copy.deepcopy(self.rows);next(x for x in r if 'status' in x)['status']='PASS_COMPILED_CATALOG_RELATIVE_PENCIL_EXCLUSION';self.reject(r,'budget15')
 def test_false_cover(self):
  r=copy.deepcopy(self.rows);x=next(x for x in r if 'rigidity_class' in x);x['uncovered_histogram']['0']=1;self.reject(r,'coverage gap')
 def test_missing_case(self):self.reject([x for x in self.rows if not ('rigidity_class' in x and x['rigidity_class']==68)],'incomplete')
 def test_false_histogram(self):
  r=copy.deepcopy(self.rows);x=next(x for x in r if 'rigidity_class' in x);x['uncovered_histogram']['2']+=1;x['uncovered_histogram']['3']-=1;self.reject(r,'independent coverage mismatch')
 def test_negative_class_count(self):
  r=copy.deepcopy(self.rows);x=next(x for x in r if 'class_closed' in x);x['pair']=-1;x['arc']=496;x['search']=0;self.reject(r,'class count shape')
 def test_bool_class_count(self):
  r=copy.deepcopy(self.rows);x=next(x for x in r if 'class_closed' in x);x['pair']=True;self.reject(r,'class count shape')
 def test_bad_final(self):
  r=copy.deepcopy(self.rows);r[-1]['valid30']=1;self.reject(r,'final assertion')
if __name__=='__main__':unittest.main()
