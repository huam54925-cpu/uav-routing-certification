import itertools
import json
from pathlib import Path
import random
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from uav_q1.lower_bounds import assignment, verify_assignment, distance_matrix, mst_cost, fixed_fleet_bound, minimum_fleet_bound

class BoundTests(unittest.TestCase):
    def test_alternating_revisits_refute_distinct_neighbor_bound(self):
        points=[{'x':100,'y':0,'visits':3},{'x':101,'y':0,'visits':3}]
        actual_km=(100+5*1+101)*.1
        old_km=(3*(1+100)+3*(1+101))*.1/2
        self.assertAlmostEqual(actual_km,20.6)
        self.assertAlmostEqual(old_km,30.45)
        self.assertGreater(old_km,actual_km)
        bound=fixed_fleet_bound(points,1,limit_h=1)
        self.assertFalse(bound['excluded'])
        self.assertLessEqual(bound['routing_lower_km'],actual_km)
        self.assertGreater(.5+old_km/55,1)
        self.assertLess(.5+actual_km/55,1)

    def test_assignment_certificate_against_exhaustive_permutations(self):
        rng=random.Random(16)
        for n in range(1,7):
            for _ in range(5):
                costs=[[rng.randrange(100) for _ in range(n)] for _ in range(n)]
                certificate=assignment(costs)
                expected=min(sum(costs[i][p[i]] for i in range(n)) for p in itertools.permutations(range(n)))
                self.assertEqual(certificate['objective_units'],expected)
                certificate['row_potentials'][0]+=1
                with self.assertRaises(ValueError): verify_assignment(costs,certificate)

    def test_mst_keeps_zero_edges(self):
        d=distance_matrix([{'x':0,'y':0},{'x':10,'y':0}])
        self.assertEqual(mst_cost(d),1_000_000)

    def test_single_point_requires_separate_uavs(self):
        n,_=minimum_fleet_bound([{'x':10,'y':0,'visits':3}])
        self.assertEqual(n,3)

    def test_four_case_fleet_bounds(self):
        data=json.loads((ROOT.parents[2]/'research/alns_next/instances.json').read_text())
        self.assertEqual([minimum_fleet_bound(v['points'])[0] for v in data['cases'].values()],[3,2,4,4])

if __name__=='__main__':unittest.main()
