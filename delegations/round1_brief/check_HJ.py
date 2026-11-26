import numpy as np, sys
from safetensors.numpy import load_file
w=load_file(sys.argv[1]); N,n=768,64; kH=[];kJ=[]
for l in range(12):
    Wa=w[f'h.{l}.attn.c_attn.weight'].astype(float)
    for h in range(12):
        Q=Wa[:,h*n:(h+1)*n].T;K=Wa[:,N+h*n:N+(h+1)*n].T
        U,s,Vt=np.linalg.svd(K.T@Q);W=U[:,:n].T@Vt[:n].T;E=W-np.diag(np.diag(W))
        iu=np.triu_indices(n,1);H=((E+E.T)/2)[iu];J=((E-E.T)/2)[iu]
        kH.append(np.mean(H**4)/np.mean(H**2)**2);kJ.append(np.mean(J**4)/np.mean(J**2)**2)
print("kurtosis H median",np.median(kH).round(2),np.percentile(kH,[10,90]).round(2)," J median",np.median(kJ).round(2),np.percentile(kJ,[10,90]).round(2))
