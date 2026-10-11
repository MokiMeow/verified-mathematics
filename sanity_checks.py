"""Exact finite sanity checks, not a substitute for the Lean proof."""
from fractions import Fraction as Q
from itertools import product
import json

def objective(weights, values):
    return sum((w*x for w,x in zip(weights, values)), Q(0))*sum(
        (w/x for w,x in zip(weights,values)), Q(0))

checks=0
weight_vectors = [[], [0], [1], [1,2], [1,1,1], [0,2,5], [1,3,7,9]]
intervals = [(Q(1),Q(1)),(Q(1),Q(4)),(Q(2,3),Q(7,2))]
for weights in weight_vectors:
    for m,M in intervals:
        ends=list(product([m,M], repeat=len(weights)))
        best=max((objective(weights,x) for x in ends), default=Q(0))
        total=sum(weights)
        gaps=[]
        for x in ends:
            u=sum(w for w,t in zip(weights,x) if t==m)
            # When m=M either endpoint label is valid; label all as lower.
            v=total-u
            assert 4*m*M*objective(weights,x)==(m+M)**2*total**2-(M-m)**2*(u-v)**2
            gaps.append((u-v)**2)
        expected=((m+M)**2*total**2-(M-m)**2*min(gaps))/(4*m*M)
        assert best==expected
        grid=[m+(M-m)*Q(k,4) for k in range(5)]
        for x in product(grid,repeat=len(weights)):
            assert objective(weights,x)<=best
            checks+=1

m,M=Q(1),Q(4)
weights=[1,2]
sharp=max(objective(weights,x) for x in product([m,M],repeat=2))
classical=(m+M)**2*sum(weights)**2/(4*m*M)
assert sharp==Q(27,2) and classical==Q(225,16)
assert sharp<classical
print(json.dumps({'exact_grid_checks':checks,
                  'weight_vectors':weight_vectors,
                  'intervals':[[str(a),str(b)] for a,b in intervals],
                  'grid_points_per_coordinate':5,
                  'example_weights':weights,
                  'm':str(m),'M':str(M),'sharp_product':str(sharp),
                  'classical_product_bound':str(classical),
                  'proof_status':'sanity only; infinite theorem requires Lean'}))
