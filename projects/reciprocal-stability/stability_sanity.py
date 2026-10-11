"""Exact sanity checks of the two complete stability theorems."""
from fractions import Fraction as F
from itertools import product, permutations
import json

count2=count3=0
intervals = [(F(1),F(2)),(F(1),F(4)),(F(2,3),F(7,2)),(F(1),F(1))]
weight_pairs = [(F(0),F(1)),(F(1),F(0)),(F(1),F(2)),(F(1,3),F(2,3))]
for m,M in intervals:
    grid=[m+(M-m)*F(k,8) for k in range(9)]
    for p,q in weight_pairs:
        best=(p+q)**2+p*q*(M-m)**2/(m*M)
        for x,y in product(grid,repeat=2):
            actual=(p*x+q*y)*(p/x+q/y)
            d2=min((x-m)**2+(y-M)**2,(x-M)**2+(y-m)**2)
            assert best-actual >= p*q*d2/(m*M)
            count2+=1
    best3=F(9)+2*(M-m)**2/(m*M)
    ends=set(permutations([m,m,M]))|set(permutations([m,M,M]))
    for x,y,z in product(grid,repeat=3):
        d2=min(sum((a-b)**2 for a,b in zip((x,y,z),end)) for end in ends)
        actual=(x+y+z)*(1/x+1/y+1/z)
        assert best3-actual >= 2*d2/(m*M)
        count3+=1
    if m<M:
        values=(m,(m+M)/2,M)
        d2=min(sum((a-b)**2 for a,b in zip(values,end)) for end in ends)
        actual=sum(values)*sum(1/a for a in values)
        assert d2==(M-m)**2/4 and best3-actual==2*d2/(m*M)

print(json.dumps(dict(two_point_checks=count2,three_point_checks=count3,
                      intervals=[[str(a),str(b)] for a,b in intervals],
                      two_point_weight_pairs=[[str(a),str(b)] for a,b in weight_pairs],
                      grid_points_per_coordinate=9,
                      method='Fixed-grid exact rational checks of a separate Python restatement, not validation of Lean statement fidelity.',
                      midpoint_stability_equality_verified=True,
                      scope='Sanity only; generality and coefficient optimality proved in Lean.')))
