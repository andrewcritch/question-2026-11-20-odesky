import numpy as np, sys
from scipy.stats import kendalltau
from safetensors.numpy import load_file
w=load_file(sys.argv[1]); pre='' if 'h.0.attn.c_attn.weight' in w else 'transformer.'
N=w[f'{pre}h.0.attn.c_attn.weight'].shape[0]; n=64; H=N//n; Lyr=sum(1 for k in w if k.endswith('attn.c_attn.weight'))
def prof(L):
    S=(L+L.T)/2;T=(L-L.T)/2;ev=np.linalg.eigvalsh(S)
    lp=np.sort(ev[ev>0])[::-1][:n];lm=np.sort(-ev[ev<0])[::-1][:n];sv=np.linalg.svd(T,compute_uv=False)[:2*n:2];F=np.sum(L*L)
    a=np.sum(T*T)/F;b=2*lp@lm/F;d=lp-lm;c=np.sum(np.maximum(d,0)**2)/F;dd=np.sum(np.maximum(-d,0)**2)/F
    return a,b,c,dd,np.linalg.norm(sv-np.sqrt(lp*lm))/np.linalg.norm(sv)
R={k:[] for k in 'amb cmd err1 diag tstd offrms kurt tau bottomfrac q'.split()}
for l in range(Lyr):
    Wa=w[f'{pre}h.{l}.attn.c_attn.weight'].astype(float)
    for h in range(H):
        Q=Wa[:,h*n:(h+1)*n].T;K=Wa[:,N+h*n:N+(h+1)*n].T;L=K.T@Q
        a,b,c,d,e=prof(L);U,s,Vt=np.linalg.svd(L);s=s[:n];Wm=U[:,:n].T@Vt[:n].T;t=np.diag(Wm);E=Wm-np.diag(t)
        off=~np.eye(n,dtype=bool);v=E[off];wt=s**2/np.sum(s**2);tb=wt@t
        R['amb'].append(a-b);R['cmd'].append(c-d);R['err1'].append(e);R['diag'].append(np.sum(t**2)/np.sum(Wm**2))
        R['tstd'].append(np.sqrt(wt@(t-tb)**2));R['offrms'].append(np.sqrt(np.mean(v**2)));R['kurt'].append(np.mean(v**4)/np.mean(v**2)**2)
        R['tau'].append(kendalltau(s*(1+t),s*(1-t))[0])
        E2=E.copy();E2[-8:,-8:]=0;v2=E2[off];R['bottomfrac'].append(np.mean(v2**4)/np.mean(v2**2)**2)
        R['q'].append(np.sum(np.outer(s,s)*E*E.T)/np.sum(s**2))
print(f"model N={N}, layers={Lyr}, heads={Lyr*H}; 1/sqrt(N)={1/np.sqrt(N):.4f}")
for k,v in R.items():
    v=np.array(v); print(f"  {k:10s} {np.median(v):+.4f} [{np.percentile(v,10):+.4f},{np.percentile(v,90):+.4f}]")
print("  frac a>b:",np.mean(np.array(R['amb'])>0).round(3)," corr(q,a-b):",np.corrcoef(R['q'],R['amb'])[0,1].round(3))
print("  (bottomfrac = kurtosis after zeroing bottom 8x8)")
