import math, random, sys

# Charges at (0,0),(1,0),(u,w). Field F = sum q (p-a)/R^3 (= -grad V). Find all zeros in plane.
def field(q, P, x, y):
    fx = fy = 0.0
    a=b=c=0.0
    for qj,(X,Y) in zip(q,P):
        dx, dy = x-X, y-Y
        r2 = dx*dx+dy*dy
        R = math.sqrt(r2)
        R3 = R**3; R5 = R**5
        fx += qj*dx/R3; fy += qj*dy/R3
        # jacobian of F: dFx/dx = q(R^2-3dx^2)/R^5 = -q(2dx^2-dy^2)/R^5
        a += qj*(2*dx*dx-dy*dy)/R5
        b += qj*3*dx*dy/R5
        c += qj*(2*dy*dy-dx*dx)/R5
    return fx, fy, a, b, c

def newton(q,P,x,y,it=200):
    for _ in range(it):
        try:
            fx,fy,a,b,c = field(q,P,x,y)
        except ZeroDivisionError:
            return None
        # J = -[[a,b],[b,c]]
        det = a*c-b*b
        if det == 0: return None
        # solve J d = -F  => -[[a,b],[b,c]] d = -F => [[a,b],[b,c]] d = F
        dx = ( c*fx - b*fy)/det
        dy = (-b*fx + a*fy)/det
        # damping
        s = 1.0
        n = math.hypot(dx,dy)
        lim = 0.5*max(1e-12, min(math.hypot(x-X,y-Y) for X,Y in P))
        if n > lim: s = lim/n
        x += s*dx; y += s*dy
        if abs(x)>1e6 or abs(y)>1e6: return None
        if n < 1e-14*(1+abs(x)+abs(y)): break
    try:
        fx,fy,a,b,c = field(q,P,x,y)
    except ZeroDivisionError:
        return None
    sc = sum(abs(qj)/((x-X)**2+(y-Y)**2) for qj,(X,Y) in zip(q,P))
    if math.hypot(fx,fy) < 1e-9*sc:
        return (x,y,a*c-b*b, sum(qj/math.hypot(x-X,y-Y)**3 for qj,(X,Y) in zip(q,P)))
    return None

def all_eq(q,u,w,nseeds=1500,rng=random):
    P=[(0,0),(1,0),(u,w)]
    cx=(1+u)/3; cy=w/3
    scale=max(1,math.hypot(u,w))
    found=[]
    seeds=[]
    for i in range(nseeds):
        r = scale*10**rng.uniform(-3,2.5); t=rng.uniform(0,2*math.pi)
        seeds.append((cx+r*math.cos(t), cy+r*math.sin(t)))
        # near each charge / edge points
    for (X,Y) in P:
        for k in range(60):
            r=10**rng.uniform(-4,0.5); t=rng.uniform(0,2*math.pi)
            seeds.append((X+r*math.cos(t),Y+r*math.sin(t)))
    for i in range(3):
        for j in range(3):
            if i<j:
                for k in range(40):
                    s=rng.uniform(-3,4)
                    x=P[i][0]+s*(P[j][0]-P[i][0])+rng.gauss(0,0.05); y=P[i][1]+s*(P[j][1]-P[i][1])+rng.gauss(0,0.05)
                    seeds.append((x,y))
    for (x,y) in seeds:
        r=newton(q,P,x,y)
        if r is None: continue
        if all(math.hypot(r[0]-f[0],r[1]-f[1])>1e-7*(1+math.hypot(r[0],r[1])) for f in found):
            found.append(r)
    return found

if __name__=='__main__':
    rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 0)
    # equilateral test
    for q in ([1,1,1],[1,1,-1],[1,-1,1],[-1,1,1]):
        f=all_eq(q,0.5,math.sqrt(3)/2,rng=rng)
        print('equilateral',q,len(f),[(round(a,4),round(b,4),'det%.3g'%d,'nrm%.3g'%s) for a,b,d,s in f])
    N=int(sys.argv[2]) if len(sys.argv)>2 else 300
    hist={}
    worst=[]
    for trial in range(N):
        u=rng.uniform(-3,4); w=rng.choice([-1,1])*10**rng.uniform(-2,1)
        for q in ([1,1,1],[1,1,-1],[1,-1,1],[-1,1,1],[-1,-1,-1],[-1,-1,1]):
            f=all_eq(q,u,w,nseeds=600,rng=rng)
            n=len(f)
            hist[(tuple(q),n)]=hist.get((tuple(q),n),0)+1
            if n>4:
                worst.append((q,u,w,n,f))
    for k in sorted(hist): print(k,hist[k])
    for wv in worst[:10]: print('VIOLATION?',wv)
