"""Direct all-quadruple positive checks for sharp minimum-point claims."""
from itertools import combinations
from pathlib import Path
import json

def verify(data,count,minima):
 blocks=data['blocks']
 if type(blocks) is not list or len(blocks)!=count:raise ValueError('block count')
 for b in blocks:
  if type(b) is not list or len(b)!=7 or any(type(p)is not int or not 0<=p<13 for p in b) or len(set(b))!=7:raise ValueError('block shape')
 if len({tuple(sorted(b)) for b in blocks})!=count:raise ValueError('duplicate block')
 blocks=list(map(set,blocks));degrees=[sum(p in b for b in blocks) for p in range(13)]
 if min(degrees)<15 or degrees.count(15)!=minima:raise ValueError('point degrees')
 if not all(any(set(q)<=b for b in blocks) for q in combinations(range(13),4)):raise ValueError('uncovered quadruple')
 return {'blocks':count,'degree15_points':[p for p,d in enumerate(degrees) if d==15],'degrees':degrees,'covered_quadruples':715}

if __name__=='__main__':
 P=Path(__file__).parent
 a=verify(json.loads((P.parent/'known30_control.json').read_text()),30,4)
 b=verify(json.loads((P/'known31_five_minimum_control.json').read_text()),31,5)
 print(json.dumps({'status':'PASS_SHARP_MINIMUM_POINT_CONTROLS','known30':a,'known31':b},sort_keys=True,indent=2))
