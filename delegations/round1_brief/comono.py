import numpy as np, sys
from scipy.stats import kendalltau
from safetensors.numpy import load_file
rng=np.random.default_rng(0); n=64
def prof(sig,t):
    lp=sig*(1+t)/2; lm=sig*(1-t)/2; st=sig*np.sqrt(1-t*t)/2; F=np.sum(sig**2)
    a=2*np.sum(lp*lm)/F; P=np.sort(lp)[::-1]; M=np.sort(lm)[::-1]; b=2*P@M/F
    e=np.linalg.norm(np.sort(st)[::-1]-np.sqrt(P*M))/np.linalg.norm(st)
    d=P-M; c=np.sum(np.maximum(d,0)**2)/F; dd=np.sum(np.maximum(-d,0)**2)/F
    return a,b,c,dd,e
# 1. exactness check of theorem on random comonotone and non-comonotone blocks
for trial in range(3):
    sig=np.sort(rng.gamma(2,1,n))[::-1]; t=np.clip(0.3+0.2*rng.standard_normal(n),-.9,.9)
    # make comonotone: choose lam+ and lam- both decreasing
    lp=np.sort(rng.gamma(2,1,n))[::-1]; lm=np.sort(rng.gamma(2,0.5,n))[::-1]
    s2=lp+lm; t2=(lp-lm)/s2
    a,b,c,d,e=prof(s2,t2); print("comonotone: a-b=%.1e err1=%.1e cd=%.1e"%(a-b,e,c*d))
    a,b,c,d,e=prof(sig,t); print("generic   : a-b=%.1e err1=%.1e"%(a-b,e))
# 2. GPT-2: Kendall tau between block lambda+ and lambda-
w=load_file(sys.argv[1]); N=768; taus=[]; e_diag=[]
for l in range(12):
    Wa=w[f'h.{l}.attn.c_attn.weight'].astype(float)
    for h in range(12):
        Q=Wa[:,h*n:(h+1)*n].T;K=Wa[:,N+h*n:N+(h+1)*n].T
        U,s,Vt=np.linalg.svd(K.T@Q);s=s[:n];t=np.diag(U[:,:n].T@Vt[:n].T)
        taus.append(kendalltau(s*(1+t),s*(1-t))[0]); e_diag.append(prof(s,t)[4])
taus=np.array(taus); e_diag=np.array(e_diag)
print("GPT-2 Kendall tau(lambda+_i, lambda-_i) in diagonal surrogate: median %.3f [%.3f,%.3f]"%(np.median(taus),*np.percentile(taus,[10,90])))
print("corr(1-tau, err1 of diagonal surrogate) = %.3f"%np.corrcoef(1-taus,e_diag)[0,1])
