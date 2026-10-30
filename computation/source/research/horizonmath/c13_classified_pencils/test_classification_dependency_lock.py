import unittest

import classification_dependency_lock as A


class ClassificationDependencyLockTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = A.verify()

    def test_source_reconstruction(self):
        self.assertEqual(
            self.out["status"],
            "PASS_C13_CLASSIFICATION_DEPENDENCY_LOCK",
        )
        self.assertEqual(self.out["figure1_raw_completions"], 21952)
        self.assertEqual(self.out["figure1_construction_group_order"], 576)
        self.assertEqual(self.out["figure1_quotient_classes"], 67)
        self.assertEqual(self.out["figure1_orbit_total"], 21952)
        self.assertTrue(self.out["exceptional_figure6_included"])
        self.assertEqual(self.out["frozen_catalog_classes"], 68)
        self.assertTrue(self.out["all_rebuilt_links_are_15_block_123_covers"])

    def test_pointed_star_mappers_match_bruteforce(self):
        self.assertEqual(self.out["star_mapper_bruteforce_cases"], 1536)
        self.assertGreater(self.out["star_mapper_bruteforce_isomorphisms"], 0)


if __name__ == "__main__":
    unittest.main()
