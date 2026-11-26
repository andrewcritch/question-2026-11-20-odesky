import numpy as np, sys
from safetensors.numpy import load_file
w=load_file(sys.argv[1]); N,n=768,64; rng=np.random.default_rng(1)
def tsig(K,Q):
    U,s,Vt=np.linalg.svd(K.T@Q); s=s[:n]; t=np.diag(U[:,:n].T@Vt[:n].T); return s,t
dat=[]
for l in range(12):
    Wa=w[f'h.{l}.attn.c_attn.weight'].astype(float)
    for h in range(12):
        s,t=tsig(Wa[:,N+h*n:N+(h+1)*n].T,Wa[:,h*n:(h+1)*n].T)
        if abs(t.mean())>0.05 or t.std()>0.15: dat.append(abs(np.corrcoef(s,t)[0,1]))
print(f"data: heads with structure {len(dat)}, median |corr(sigma_i,t_i)| = {np.median(dat):.3f} [{np.percentile(dat,10):.3f},{np.percentile(dat,90):.3f}]")
Neff=430
for r0,g in [(-0.05,0.25),(-0.3,0.4),(-0.6,0.55),(0.3,-0.3)]:
    cs=[];ts=[]
    for _ in range(10):
        X0,Y0,F=[rng.standard_normal((n,Neff))/np.sqrt(Neff) for _ in range(3)]; gg=rng.standard_normal(n)
        Q=X0+abs(g)*gg[:,None]*F; K=r0*X0+np.sqrt(1-r0*r0)*Y0+g*gg[:,None]*F
        s,t=tsig(K,Q); cs.append(abs(np.corrcoef(s,t)[0,1])); ts.append(t.std())
    print(f"agy cand2 r0={r0:+.2f} gamma={g:+.2f}: median |corr(sigma,t)|={np.median(cs):.3f}, unweighted std t={np.mean(ts):.3f}")
