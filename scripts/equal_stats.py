"""Count planar equilibria for equal-magnitude charges (1,1,1) and (1,1,-1) on random triangles."""
import sys, numpy as np
sys.path.insert(0, __file__.rsplit('/',1)[0])
from search3 import zeros
rng = np.random.default_rng(int(sys.argv[2]))
for q in ([1.,1,1],[1.,1,-1],[1.,-1,1],[-1.,1,1]):
    hist = {}
    for k in range(int(sys.argv[1])):
        p, h = rng.uniform(-1, 2), rng.uniform(0.02, 2.5)
        A = np.array([[0,0],[1,0],[p,h]], float)
        Z, idx = zeros(A, np.array(q))
        n = len(Z); hist[n] = hist.get(n,0)+1
        if n > 4: print("FLAG", q, p, h, Z.tolist(), flush=True)
    print(q, dict(sorted(hist.items())), flush=True)
