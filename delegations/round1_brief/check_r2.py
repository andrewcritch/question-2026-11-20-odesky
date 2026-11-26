import numpy as np, sys
from safetensors.numpy import load_file
rng=np.random.default_rng(3); n=64
def score(E):
    iu=np.triu_indices(n,1);x=E[iu];y=E.T[iu];m=np.maximum(abs(x),abs(y));k=m>=np.quantile(m,0.95)
    return np.mean(abs(x[k]+y[k])/(abs(x[k])+abs(y[k])))
nul=[score(rng.standard_normal((n,n))) for _ in range(200)]
print("Gaussian null top-5%% symmetry score: median %.3f [%.3f,%.3f]"%(np.median(nul),*np.percentile(nul,[10,90])))
w=load_file(sys.argv[1]); N=768; kfull=[];kzb=[];frac=[]; rhoB=[]
for l in range(12):
    Wa=w[f'h.{l}.attn.c_attn.weight'].astype(float)
    for h in range(12):
        Q=Wa[:,h*n:(h+1)*n].T;K=Wa[:,N+h*n:N+(h+1)*n].T
        U,s,Vt=np.linalg.svd(K.T@Q);W=U[:,:n].T@Vt[:n].T;E=W-np.diag(np.diag(W))
        off=~np.eye(n,dtype=bool); v=E[off]; kfull.append(np.mean(v**4)/np.mean(v**2)**2)
        E2=E.copy();E2[56:,56:]=0; v2=E2[off]; kzb.append(np.mean(v2**4)/np.mean(v2**2)**2)
        big=np.abs(E)>5*np.sqrt(np.mean(v**2)); B=np.zeros_like(big);B[56:,56:]=True
        frac.append((big&B).sum()/max(big.sum(),1))
        iu=np.triu_indices(8,1);Bb=E[56:,56:];rhoB.append(np.corrcoef(Bb[iu],Bb.T[iu])[0,1])
print("kurtosis full median %.1f, bottom 8x8 zeroed %.2f"%(np.median(kfull),np.median(kzb)))
print("median share of >5xRMS entries in bottom 8x8: %.2f; median pair corr in bottom block %.2f"%(np.median(frac),np.median(rhoB)))
