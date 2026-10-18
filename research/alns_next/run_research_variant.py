import argparse
from functools import partial
import sys
from alns_solver import Solver,main
from neighborhood_core import EnhancedSolver
from group_neighborhood import GroupSolver
if __name__=='__main__':
    p=argparse.ArgumentParser(add_help=False)
    p.add_argument('--variant',choices=['baseline','both','regional','balanced','wide'],default='regional')
    a,rest=p.parse_known_args();sys.argv=[sys.argv[0]]+rest
    factory=Solver if a.variant=='baseline' else partial(EnhancedSolver if a.variant=='both' else GroupSolver,variant=a.variant)
    main(solver_cls=factory)
