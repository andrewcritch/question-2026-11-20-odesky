import numpy as np
rng=np.random.default_rng(0)
def profile(L):
    S=(L+L.T)/2; T=(L-L.T)/2
    ev=np.linalg.eigvalsh(S); n=np.linalg.matrix_rank(L) # use given n
    return S,T
def prof(L,n):
    S=(L+L.T)/2; T=(L-L.T)/2
    ev=np.sort(np.linalg.eigvalsh(S))
    lp=ev[::-1][:n]; lm=-ev[:n]
    sv=np.linalg.svd(T,compute_uv=False)[0:2*n:2]
    F=np.sum(L*L)
    a=np.sum(T*T)/F; b=2*lp@lm/F; x=lp-lm
    c=np.sum(np.clip(x,0,None)**2)/F; d=np.sum(np.clip(-x,0,None)**2)/F
    err=np.max(np.abs(sv-np.sqrt(lp*lm))/sv)
    return np.array([a,b,c,d]),err
def block(sig,t,N):
    n=len(sig); O=np.linalg.qr(rng.standard_normal((N,N)))[0]
    L=np.zeros((N,N))
    for i in range(n):
        e1=O[:,2*i]; e2=O[:,2*i+1]
        u=e1; v=t[i]*e1+np.sqrt(1-t[i]**2)*e2
        L+=sig[i]*np.outer(u,v)
    return L
# R13: comonotone vs not
n,N=5,12
for trial in range(3):
    al=np.sort(rng.uniform(.5,3,n)); be=np.sort(rng.uniform(.2,1,n))  # comonotone, al>be
    sig=al+be; t=(al-be)/sig
    p,e=prof(block(sig,t,N),n); w=sig**2/np.sum(sig**2)
    print("comono",p,"a-b",p[0]-p[1],"err",e,"c-d formula",p[2]-p[3]-np.sum(w*t*np.abs(t)))
    # mixed-sign comonotone
    al=np.sort(rng.uniform(.2,2,n)); be=np.sort(rng.uniform(.2,2,n))
    sig=al+be; t=(al-be)/sig
    p,e=prof(block(sig,t,N),n); w=sig**2/np.sum(sig**2)
    print("comono mixed",np.round(t,2),"a-b",p[0]-p[1],"c-d - formula",p[2]-p[3]-np.sum(w*t*np.abs(t)),"cd",p[2]*p[3])
# R14: ensemble convergence
f=lambda r: np.exp(r)+1.0; g=lambda r: 0.5+0.3*np.tanh(r)
rho=rng.standard_normal(n)
for N in [100,1000,10000,100000]:
    P=rng.standard_normal((n,N)); M=rng.standard_normal((n,N))
    A=2*np.sqrt(f(rho))[:,None]*P/np.sqrt(N); B=2*np.sqrt(g(rho))[:,None]*M/np.sqrt(N)
    Q=(A-B)/2; K=(A+B)/2
    # profile via small Gram-free route: compute L only on span
    Fm=np.vstack([Q,K]); U,_=np.linalg.qr(Fm.T)  # N x 2n basis
    Qs=Q@U; Ks=K@U; L=Ks.T@Qs
    p,e=prof(L,n); print(N,p,"a-b",p[0]-p[1],"err",e)
al=f(rho);be=g(rho);sig=al+be;t=(al-be)/sig;print("limit",prof(block(sig,t,12),n))
# counterexample to 'position set by law of (f-g)/(f+g)'
def cd(fv,gv,p):
    fv,gv,p=map(np.array,(fv,gv,p)); return p@((fv-gv)*np.abs(fv-gv))/(p@((fv+gv)**2))
print("A",cd([2,3],[1,3],[.5,.5]),"B",cd([1,4],[1,2],[.5,.5]))
# finite-n check of case A/B via block forms with n large
for fv,gv in [([2,3],[1,3]),([1,4],[1,2])]:
    rr=rng.integers(0,2,200); al=np.array(fv)[rr]; be=np.array(gv)[rr]
    sig=al+be; t=(al-be)/sig; p,e=prof(block(sig,t,402),200); print("n=200 c-d",p[2]-p[3],"a-b",p[0]-p[1])
