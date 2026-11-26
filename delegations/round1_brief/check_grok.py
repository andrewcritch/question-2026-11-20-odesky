import numpy as np, sys
from safetensors.numpy import load_file
w=load_file(sys.argv[1]); N,n=768,64
ku=[];sym=[];q=[];ab=[]
for l in range(12):
    Wa=w[f'h.{l}.attn.c_attn.weight'].astype(float)
    for h in range(12):
        Q=Wa[:,h*n:(h+1)*n].T;K=Wa[:,N+h*n:N+(h+1)*n].T
        U,s,Vt=np.linalg.svd(K.T@Q);W=U[:,:n].T@Vt[:n].T
        iu=np.triu_indices(n,1);x=W[iu];y=W.T[iu]
        off=np.concatenate([x,y]);ku.append(np.mean(off**4)/np.mean(off**2)**2)
        m=np.maximum(abs(x),abs(y));k=m>=np.quantile(m,0.95)
        sym.append(np.mean(abs(x[k]+y[k])/(abs(x[k])+abs(y[k]))))
print("median off-diag kurtosis",np.median(ku).round(1),"; median top-5% symmetry score",np.median(sym).round(3),"(random-sign null ~0.5)")
