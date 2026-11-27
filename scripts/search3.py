"""L1 numerical exploration: count planar equilibria of 3 point charges.

For non-collinear charges every equilibrium lies in the plane of the charges
(see NOTES.md, Lemma P), so we work in R^2.
Normalisation: a1=(0,0), a2=(1,0), a3=(p,h), h>0; charges q=(1,s,t).
Field F(x) = sum q_j (x-a_j)/|x-a_j|^3 (=-grad V).  Zeros found by vectorised
multistart Newton from a dense log-polar cloud around each charge and the
centroid; deduplicated.  Sanity check: sum of indices sign(det DF) must be -2
when sum q != 0 (Poincare-Hopf on the plane: +1 at infinity, +1 per charge).

Usage: python scripts/search3.py N seed  -> logs/search3_<seed>.log
"""
import sys, numpy as np

def field(X, A, q):
    F = np.zeros_like(X); J = np.zeros(X.shape[:-1] + (2, 2))
    for a, c in zip(A, q):
        dx = X[:, 0] - a[0]; dy = X[:, 1] - a[1]; r2 = dx * dx + dy * dy
        i3 = c / (r2 * np.sqrt(r2)); i5 = 3 * i3 / r2
        F[:, 0] += i3 * dx; F[:, 1] += i3 * dy
        J[:, 0, 0] += i3 - i5 * dx * dx; J[:, 1, 1] += i3 - i5 * dy * dy
        J[:, 0, 1] -= i5 * dx * dy
    J[:, 1, 0] = J[:, 0, 1]
    return F, J

def starts(A, nr=16, nth=24):
    pts = []
    th = np.linspace(0, 2 * np.pi, nth, endpoint=False)
    cen = A.mean(0)
    for c, rs in [(a, np.geomspace(1e-3, 3, nr)) for a in A] + [(cen, np.geomspace(1e-2, 1e4, 2 * nr))]:
        R, T = np.meshgrid(rs, th)
        pts.append(np.stack([c[0] + R * np.cos(T), c[1] + R * np.sin(T)], -1).reshape(-1, 2))
    return np.concatenate(pts)

def zeros(A, q, it=60):
    X = starts(A)
    for _ in range(it):
        F, J = field(X, A, q)
        det = J[:, 0, 0] * J[:, 1, 1] - J[:, 0, 1] * J[:, 1, 0]
        ok = np.abs(det) > 1e-300
        dx = np.zeros_like(X)
        dx[ok, 0] = (J[ok, 1, 1] * F[ok, 0] - J[ok, 0, 1] * F[ok, 1]) / det[ok]
        dx[ok, 1] = (-J[ok, 1, 0] * F[ok, 0] + J[ok, 0, 0] * F[ok, 1]) / det[ok]
        # damp steps
        n = np.linalg.norm(dx, axis=1); sc = np.minimum(1, (0.5 * np.linalg.norm(X - A.mean(0), axis=1) + 0.1) / (n + 1e-300))
        X = X - dx * sc[:, None]
        X = np.where(np.isfinite(X), X, 0.123)
    F, J = field(X, A, q)
    dmin = np.min([np.linalg.norm(X - a, axis=1) for a in A], axis=0)
    # relative residual
    scale = sum(abs(c) / np.maximum(np.linalg.norm(X - a, axis=1), 1e-12) ** 2 for a, c in zip(A, q))
    good = (np.linalg.norm(F, axis=1) < 1e-9 * scale) & (dmin > 1e-6)
    Z = []
    for x in X[good]:
        if all(np.linalg.norm(x - z) > 1e-6 * (1 + np.linalg.norm(z)) for z in Z):
            Z.append(x)
    Z = np.array(Z).reshape(-1, 2)
    if len(Z):
        _, J = field(Z, A, q)
        idx = np.sign(J[:, 0, 0] * J[:, 1, 1] - J[:, 0, 1] * J[:, 1, 0])
    else:
        idx = np.array([])
    return Z, idx

def run(N, seed):
    rng = np.random.default_rng(seed)
    hist = {}; best = []
    for k in range(N):
        mode = rng.integers(3)
        if mode == 0:   # generic
            s, t = rng.normal(size=2) * 2
        elif mode == 1:  # log-uniform magnitudes, random signs
            s, t = np.exp(rng.uniform(-4, 4, 2)) * rng.choice([-1, 1], 2)
        else:  # equal magnitudes (Tsai case) as control
            s, t = rng.choice([-1, 1], 2).astype(float)
        p, h = rng.uniform(-1.5, 2.5), np.exp(rng.uniform(-4, 1.5))
        A = np.array([[0, 0], [1, 0], [p, h]], float); q = np.array([1, s, t])
        Z, idx = zeros(A, q)
        n = len(Z); hist[n] = hist.get(n, 0) + 1
        chk = int(idx.sum()) if n else 0
        line = f"{k} mode={mode} q=(1,{s:.6g},{t:.6g}) a3=({p:.6g},{h:.6g}) n={n} indexsum={chk}"
        if n > 4 or (abs(q.sum()) > 1e-3 and chk != -2):
            print("FLAG", line, Z.tolist(), flush=True)
        if n > 4: best.append(line)
    print("histogram", dict(sorted(hist.items())))
    return best

if __name__ == "__main__":
    N = int(sys.argv[1]); seed = int(sys.argv[2])
    run(N, seed)
