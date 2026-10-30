import copy,json,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import verify_pencils as V
from peer_union_join import self_test

class ProofControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.links=V.load_catalog();cls.data=json.loads((V.ROOT/'minimum_link_catalog.json').read_text())
    def test_catalog_positive(self):
        self.assertEqual(len(self.links),68)
        self.assertEqual(sorted(sum(p in b for b in self.links[-1]) for p in V.POINTS),[7]*10+[10]*2)
    def test_missing_figure6_rejected(self):
        data=copy.deepcopy(self.data);data['classes'].pop()
        with self.assertRaisesRegex(ValueError,'68 catalog'):V.parse_catalog(data)
    def test_catalog_malformed_fields_rejected(self):
        for field,value,message in [('class_id',False,'class order'),('blocks',[[0,1,2,3,4,5]]*15,'duplicate link block')]:
            data=copy.deepcopy(self.data);data['classes'][0][field]=value
            with self.assertRaisesRegex(ValueError,message):V.parse_catalog(data)
        data=copy.deepcopy(self.data);data['classes'][0]['blocks'][0][0]=True
        with self.assertRaisesRegex(ValueError,'link block shape'):V.parse_catalog(data)
    def test_catalog_bytes_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'catalog.json';p.write_text(json.dumps(self.data)+' ')
            with self.assertRaisesRegex(ValueError,'catalog byte integrity'):V.load_catalog(p)
    def test_star_maps_positive_and_negative(self):
        source=(frozenset([0,1]),frozenset([1,2]));target=(frozenset([3,4]),frozenset([4,5]))
        maps=list(V.star_maps(source,[0,1,2],target,[3,4,5]));self.assertEqual(len(maps),2)
        self.assertTrue(all(g[1]==4 for g in maps))
        bad=(frozenset([3,4]),frozenset([3,4]))
        self.assertEqual(list(V.star_maps(source,[0,1,2],bad,[3,4,5])),[])
    def test_union_budget_exact_positive(self):
        # Synthetic finite-domain positive control, not a purported covering.
        ids=[i for i,b in enumerate(V.BLOCKS) if set(range(4))<=b][:7]
        common=sum(1<<i for i in ids);doms={q:(common,) for q in range(4)}
        witness,_=V.compatible_union(doms,7);self.assertIsNotNone(witness)
        witness,_=V.compatible_union(doms,6);self.assertIsNone(witness)
        reduced,_=V.arc_consistency(doms);self.assertEqual(reduced,doms)
    def test_malformed_union_domains(self):
        with self.assertRaisesRegex(ValueError,'point range'):V.compatible_union({12:(1,)})
        with self.assertRaisesRegex(ValueError,'incidence/range'):V.compatible_union({0:(1<<792,)})
        with self.assertRaisesRegex(ValueError,'incidence/range'):V.compatible_union({0:(-1,)})
        with self.assertRaisesRegex(ValueError,'incidence/range'):V.compatible_union({0:(True,)})
    def test_peer_positive_and_malformed_controls(self):
        self_test()
    def test_published30_cover_pencils_retained(self):
        out=V.positive_control(self.links,[])
        self.assertEqual(out['retained_actual_pencils'],3);self.assertEqual(out['covered_quadruples'],715)
    def test_control_external_point_rejected(self):
        data=json.loads((V.ROOT/'known30_control.json').read_text());data['blocks'][0][0]=13
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp);(p/'known30_control.json').write_text(json.dumps(data))
            with patch.object(V,'ROOT',p):
                with self.assertRaisesRegex(ValueError,'point domain'):V.positive_control(self.links,[])
    def test_bad_published_control_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp);(p/'known30_control.json').write_text(json.dumps({'blocks':[]}))
            with patch.object(V,'ROOT',p):
                with self.assertRaisesRegex(ValueError,'30-cover control shape'):V.positive_control(self.links,[])

if __name__=='__main__':unittest.main()
