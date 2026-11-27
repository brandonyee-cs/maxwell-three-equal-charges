"""Random walk inside the region {configurations with >= 4 planar equilibria}, flagging any > 4.
Params: q=(1,s,t), a3=(p,h). Usage: python scripts/search_walk.py steps seed"""
import sys, numpy as np
sys.path.insert(0, __file__.rsplit('/',1)[0])
from search3 import zeros
rng = np.random.default_rng(int(sys.argv[2]))
cur = np.array([1., 1., 0.5, np.sqrt(3)/2])  # s,t,p,h : equal charges, equilateral
def count(z):
    s,t,p,h = z
    if h <= 1e-3: return -1, None
    Z, idx = zeros(np.array([[0,0],[1,0],[p,h]],float), np.array([1.,s,t]))
    return len(Z), Z
n0,_ = count(cur); print("start", n0, flush=True)
hist = {}; step = 0.2
for k in range(int(sys.argv[1])):
    prop = cur + rng.normal(size=4) * step * np.array([abs(cur[0])+.1, abs(cur[1])+.1, 1, cur[3]])
    if rng.random() < 0.1: prop[0] *= -1
    if rng.random() < 0.1: prop[1] *= -1
    n, Z = count(prop)
    hist[n] = hist.get(n,0)+1
    if n > 4: print("FLAG", prop.tolist(), n, Z.tolist(), flush=True)
    if n >= 4: cur = prop
    if k % 500 == 0: print(k, cur.tolist(), dict(sorted(hist.items())), flush=True)
print("final", dict(sorted(hist.items())))
