"""Coupled regional destruction and load-compensating two-way block exchange."""
from alns_solver import Solver
from neighborhood_core import EnhancedSolver

class GroupSolver(EnhancedSolver):
    def __init__(self,*args,variant='regional',**kwargs):
        super().__init__(*args,variant='both',**kwargs)
        if variant not in ('regional','balanced','wide'): raise ValueError(variant)
        self.variant=variant
        self.destroy_names=Solver.destroy_names+('coupled_region',)
        self.diagnostics['group']={'calls':0,'removed':0}

    def destroy(self,routes,mode):
        if mode!=4:return Solver.destroy(self,routes,mode)
        self.check_time()
        a=max(range(self.k),key=lambda i:self.route_time(routes[i]))
        if self.rng.random()<.3:a=self.rng.randrange(self.k)
        candidates=[b for b in range(self.k) if b!=a]
        # Prefer routes sharing inspection locations; sometimes use a different pairing.
        pa={self.physical[u] for u in routes[a]}
        weights=[1+len(pa & {self.physical[u] for u in routes[b]}) for b in candidates]
        b=self.rng.choices(candidates,weights)[0]
        ids={p['id']:i+1 for i,p in enumerate(self.data['points'])}
        targets=[ids[x] for x in (10,11,36,57,47) if x in ids]
        center=(self.rng.choice(targets) if targets and self.rng.random()<.4
                else self.physical[self.rng.choice(routes[a])])
        count=self.rng.randint(3,7 if self.variant!='wide' else 12)
        removed=set()
        for k in (a,b):
            if self.variant=='balanced':
                start=self.rng.randrange(len(routes[k]))
                removed.update(routes[k][start:start+count])
            else:
                ranked=sorted(routes[k],key=lambda u:self.travel[center][self.physical[u]])
                removed.update(ranked[:count])
        partial=[]
        for route in routes:
            kept=[]
            for u in route:
                if u in removed:continue
                if kept and self.physical[kept[-1]]==self.physical[u]:removed.add(u)
                else:kept.append(u)
            partial.append(kept)
        self.diagnostics['group']['calls']+=1
        self.diagnostics['group']['removed']+=len(removed)
        return partial,sorted(removed)

    def intensify(self,routes,trials=250):
        routes=Solver.intensify(self,routes,trials//2)
        # Both directions change simultaneously; service-count changes enter score().
        return self.cross_exchange(routes,trials-trials//2,max_block=8 if self.variant=='wide' else 5)
