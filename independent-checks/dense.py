import sys, math, random
sys.path.insert(0,'.')
from solve import all_eq
rng=random.Random(int(sys.argv[1]))
N=int(sys.argv[2])
hist={}; viol=[]; minnrm=[]
for t in range(N):
    # sample triangle apex in region u in [-1,2], w in [0.05,3] (covers all shapes up to similarity/relabel)
    u=rng.uniform(-1,2); w=rng.uniform(0.05,3)
    for q in ([1,1,1],[1,1,-1],[1,-1,1],[-1,1,1]):
        f=all_eq(q,u,w,nseeds=500,rng=rng)
        n=len(f); hist[(tuple(q),n)]=hist.get((tuple(q),n),0)+1
        if n>4: viol.append((q,u,w,f))
        for e in f: minnrm.append((abs(e[3]),q,u,w))
for k in sorted(hist): print(k,hist[k])
print('viol',viol[:5])
minnrm.sort(); print('smallest |sum q/R^3| at equilibria', minnrm[:3])
