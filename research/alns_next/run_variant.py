"""One shared CLI implementation and one BudgetExpired class."""
import argparse
from functools import partial
import sys
from alns_solver import Solver, main
from neighborhood_core import EnhancedSolver

if __name__ == '__main__':
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--variant', choices=['baseline','joint','cross','both'], default='both')
    args, rest = parser.parse_known_args()
    sys.argv = [sys.argv[0]] + rest
    factory = Solver if args.variant == 'baseline' else partial(EnhancedSolver, variant=args.variant)
    main(solver_cls=factory)
