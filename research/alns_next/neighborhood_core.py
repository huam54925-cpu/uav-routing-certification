"""Experimental neighborhoods; original constraints and objective are unchanged."""
import time
from alns_solver import Solver


class EnhancedSolver(Solver):
    def __init__(self, *args, variant='both', **kwargs):
        super().__init__(*args, **kwargs)
        if variant not in ('joint', 'cross', 'both'):
            raise ValueError('Expected joint, cross, or both')
        self.variant = variant
        self.destroy_names = Solver.destroy_names + (('joint_repeat',) if variant in ('joint','both') else ())
        self.diagnostics = {'joint_calls':0, 'cross':{'proposals':0,'legal':0,'score_improvements':0,'seconds':0.}}

    def destroy(self, routes, mode):
        if mode != 4:
            return super().destroy(routes, mode)
        self.diagnostics['joint_calls'] += 1
        counts = {}
        for u, p in enumerate(self.physical):
            counts.setdefault(p, []).append(u)
        repeated = [p for p, tasks in counts.items() if len(tasks) > 1]
        if not repeated:
            return super().destroy(routes, 2)
        center = self.rng.choice(repeated)
        removed = set(counts[center])
        # Remove nearby visits to give reinsertion room; do not force cross-UAV visits.
        target = min(self.n, max(len(removed), self.n // 6))
        nearby = sorted((u for u in range(self.n) if u not in removed),
                        key=lambda u: self.travel[center][self.physical[u]])
        removed.update(nearby[:max(0, target-len(removed))])
        partial = []
        for route in routes:
            kept = []
            for u in route:
                if u in removed:
                    continue
                if kept and self.physical[kept[-1]] == self.physical[u]:
                    removed.add(u)  # Removing a separator exposes an illegal adjacency.
                else:
                    kept.append(u)
            partial.append(kept)
        return partial, sorted(removed)

    def cross_exchange(self, routes, trials=120, max_block=3):
        started = time.monotonic()
        try:
            return self._cross_exchange(routes, trials, max_block)
        finally:
            self.diagnostics['cross']['seconds'] += time.monotonic()-started

    def _cross_exchange(self, routes, trials, max_block):
        """Exchange two nonempty blocks, optionally reverse them; accept score gains."""
        current = [r[:] for r in routes]
        value = self.score(current)
        if self.k < 2:
            return current
        for _ in range(trials):
            self.check_time()
            self.diagnostics['cross']['proposals'] += 1
            a, b = self.rng.sample(range(self.k), 2)
            la = self.rng.randint(1, min(max_block, len(current[a])))
            lb = self.rng.randint(1, min(max_block, len(current[b])))
            i = self.rng.randrange(len(current[a])-la+1)
            j = self.rng.randrange(len(current[b])-lb+1)
            x, y = current[a][i:i+la], current[b][j:j+lb]
            if self.rng.random() < .5:
                x = x[::-1]
            if self.rng.random() < .5:
                y = y[::-1]
            ra = current[a][:i] + y + current[a][i+la:]
            rb = current[b][:j] + x + current[b][j+lb:]
            if not self.valid(ra) or not self.valid(rb):
                continue
            self.diagnostics['cross']['legal'] += 1
            candidate = current[:]
            candidate[a], candidate[b] = ra, rb
            new_value = self.score(candidate)
            if new_value < value - 1e-12:
                self.diagnostics['cross']['score_improvements'] += 1
                current, value = candidate, new_value
        return current

    def intensify(self, routes, trials=250):
        if self.variant == 'joint':
            return super().intensify(routes, trials)
        # Keep approximately the same number of proposals as the old implementation.
        first = trials // 2
        routes = super().intensify(routes, first)
        return self.cross_exchange(routes, trials-first)
