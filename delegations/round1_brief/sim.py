import numpy as np
from scipy.linalg import sqrtm
rng=np.random.default_rng(0)
def stats(L,n):
    S=(L+L.T)/2; T=(L-L.T)/2
    ev=np.linalg.eigvalsh(S); lp=np.sort(ev[ev>0])[::-1][:n]; lm=np.sort(-ev[ev<0])[::-1][:n]
    k=min(len(lp),len(lm)); lp,lm=lp[:k],lm[:k]
    sv=np.linalg.svd(T,compute_uv=False)[:2*n:2][:k]
    nL=np.sum(L*L)
    a=np.sum(T*T)/nL; b=2*lp@lm/nL; dif=lp-lm
    c=np.sum(np.maximum(dif,0)**2)/nL; d=np.sum(np.maximum(-dif,0)**2)/nL
    e1=np.linalg.norm(sv-np.sqrt(lp*lm))/np.linalg.norm(sv)
    return [float(np.squeeze(x)) for x in (e1,abs(a-b),min(c,d),c-d)]
def from_SW(sig,W):
    n=len(sig)
    U=np.vstack([np.eye(n),np.zeros((n,n))])
    R=np.real(sqrtm(np.eye(n)-W.T@W))
    V=np.vstack([W,R])
    return U@np.diag(sig)@V.T
def rep(name,fn,trials=20):
    r=np.array([stats(fn(),n) for _ in range(trials)])
    m=r.mean(0); print(f"{name:52s} err(1)={m[0]:.3f} |a-b|={m[1]:.3f} min(c,d)={m[2]:.4f} c-d={m[3]:+.3f}")
n,N=64,768
rep("Gaussian Q,K independent",lambda: (lambda K,Q: K.T@Q)(rng.standard_normal((n,N)),rng.standard_normal((n,N))))
for r in [0.3,0.7]:
    def f(r=r):
        Q=rng.standard_normal((n,N));G=rng.standard_normal((n,N));K=r*Q+np.sqrt(1-r*r)*G;return K.T@Q
    rep(f"Gaussian correlated r={r}",f)
gam=lambda: rng.gamma(2.0,1.0,n)
print("--- SVD model L=U diag(sig) V^T, sig~Gamma(2), W=U^T V ---")
for r in [0.0,0.4]:
  for eps in [0.0,0.1,0.3,0.5]:
    def f(r=r,eps=eps):
        X=rng.standard_normal((n,n))/np.sqrt(n); np.fill_diagonal(X,0)
        W=r*np.eye(n)+eps*X; s=np.linalg.norm(W,2)
        if s>0.98: W*=0.98/s
        return from_SW(gam(),W)
    rep(f"W = {r}*I + {eps}*offdiag noise",f)
def f():
    t=rng.uniform(0,0.8,n); return from_SW(gam(),np.diag(t))
rep("W diagonal, t_i~U(0,0.8) (sorting mismatch)",f)
def f():
    t=rng.uniform(-0.6,0.6,n); return from_SW(gam(),np.diag(t))
rep("W diagonal, t_i~U(-0.6,0.6) mixed signs",f)
def f():
    O=np.linalg.qr(rng.standard_normal((n,n)))[0]; return from_SW(gam(),0.9*O)
rep("W = 0.9 * Haar orthogonal (fully mixed)",f)
def f():
    A=rng.standard_normal((n,n)); A=(A+A.T)/2; A/=np.linalg.norm(A,2); return from_SW(gam(),0.9*A)
rep("W = 0.9 * random symmetric contraction",f)
