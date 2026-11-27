import sys, math, random
sys.path.insert(0,'.')
from solve import all_eq
rng=random.Random(int(sys.argv[1]))
qs=[[1,1,1],[1,1,-1],[1,-1,1],[-1,1,1]]
hist={}; viol=[]
k=int(sys.argv[1]); 
us=[0.2+0.05*i for i in range(13)]
ws=[0.55+0.05*j for j in range(10)]
for i,u in enumerate(us):
  if i%4!=k: continue
  for w in ws:
    for q in qs:
        f=all_eq(q,u,w,nseeds=700,rng=rng)
        n=len(f); hist[(tuple(q),n)]=hist.get((tuple(q),n),0)+1
        if q==[1,1,1] and n!=2: print('u=%.2f w=%.2f n=%d'%(u,w,n), [('%.3g'%e[2]) for e in f])
        if n>4: viol.append((q,u,w,f))
for kk in sorted(hist): print(kk,hist[kk])
print('viol',viol)
