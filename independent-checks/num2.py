import numpy as np, sys
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2])
def FJ(X,a,q):
    F=np.zeros_like(X); J=np.zeros((X.shape[0],2,2)); I=np.eye(2)
    for aj,qj in zip(a,q):
        D=X-aj; r=np.linalg.norm(D,axis=1)
        F+=qj*D/r[:,None]**3
        J+=qj*(I[None]/r[:,None,None]**3-3*D[:,:,None]*D[:,None,:]/r[:,None,None]**5)
    return F,J
def eqs(a,q,M=90):
    lo=a.min(0)-1.5; hi=a.max(0)+1.5
    g=np.stack(np.meshgrid(np.linspace(lo[0],hi[0],M),np.linspace(lo[1],hi[1],M)),-1).reshape(-1,2)
    th=np.linspace(0,2*np.pi,72,endpoint=False)
    far=np.concatenate([R*np.stack([np.cos(th),np.sin(th)],1)+a.mean(0) for R in (4,8,16,40)])
    X=np.concatenate([g,far])+1e-7*rng.standard_normal((len(g)+len(far),2))
    for it in range(120):
        F,J=FJ(X,a,q)
        det=J[:,0,0]*J[:,1,1]-J[:,0,1]*J[:,1,0]
        det=np.where(np.abs(det)<1e-300,1e-300,det)
        dx=-np.stack([J[:,1,1]*F[:,0]-J[:,0,1]*F[:,1],-J[:,1,0]*F[:,0]+J[:,0,0]*F[:,1]],1)/det[:,None]
        dmin=np.min(np.linalg.norm(X[:,None,:]-a[None],axis=2),1)
        L=np.linalg.norm(dx,axis=1); cap=0.3*dmin
        dx*=np.minimum(1,cap/np.maximum(L,1e-300))[:,None]
        X=X+dx
    F,J=FJ(X,a,q)
    R=np.linalg.norm(X[:,None,:]-a[None],axis=2)
    scale=(np.abs(q)[None]/R**2).sum(1)
    good=(np.linalg.norm(F,axis=1)<1e-10*scale)&(np.linalg.norm(X,axis=1)<500)&(R.min(1)>1e-4)
    sols=[]
    for x in X[good]:
        if all(np.linalg.norm(x-s)>1e-6 for s in sols): sols.append(x)
    out=[]
    for x in sols:
        F,J=FJ(x[None],a,q); r=np.linalg.norm(x-a,axis=1)
        out.append((x,np.linalg.det(J[0]),(q/r**3).sum()))
    return out
if N==0:
    a=np.array([[0,0],[1,0],[0.5,np.sqrt(3)/2]])
    for q in ([1.,1,1],[-1.,1,1]): print(q,[(x.round(4).tolist(),round(d,3),round(n,3)) for x,d,n in eqs(a,np.array(q))])
    sys.exit()
from collections import Counter
hist={"111":Counter(),"-111":Counter()}
for t in range(N):
    m=t%4
    if m==0: a2=np.array([rng.uniform(-1.5,2.5),rng.uniform(0.01,2.5)])
    elif m==1: a2=np.array([rng.uniform(-0.5,1.5),rng.uniform(1e-3,0.1)])  # near-collinear
    elif m==2: a2=np.array([rng.uniform(0.4,0.6),rng.uniform(0.6,1.0)])  # near equilateral/isosceles
    else: a2=np.array([rng.uniform(-6,6),rng.uniform(0.01,6)])
    a=np.array([[0,0],[1,0],a2])
    for name,q in (("111",np.array([1.,1,1])),("-111",np.array([-1.,1,1]))):
        s=eqs(a,q); c=len(s)
        nd=all(abs(d)>1e-8 and abs(n)>1e-8 for x,d,n in s)
        hist[name][(c,nd)]+=1
        if c>4: print("VIOLATION?",name,a2.tolist(),c,[(x.round(5).tolist(),d,n) for x,d,n in s],flush=True)
print({k:dict(v) for k,v in hist.items()},flush=True)
