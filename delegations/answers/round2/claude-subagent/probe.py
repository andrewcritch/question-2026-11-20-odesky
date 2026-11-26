import numpy as np
from safetensors.numpy import load_file
w=load_file('/private/tmp/claude-501/-Users-andrew-maisi-questions-2026-11-20-odesky/8a345037-c99c-4fe5-98da-2190c1ebad66/scratchpad/dl_gpt2/model.safetensors');N,n=768,64
gap_big=[];gap_all=[];cs=[];spars=[]
for l in range(12):
    Wa=w[f'h.{l}.attn.c_attn.weight'].astype(float)
    for h in range(12):
        Q=Wa[:,h*n:(h+1)*n].T;K=Wa[:,N+h*n:N+(h+1)*n].T
        U,s,Vt=np.linalg.svd(K.T@Q);U=U[:,:n];s=s[:n];W=U.T@Vt[:n].T
        iu=np.triu_indices(n,1);x=W[iu];y=W.T[iu];m=np.maximum(abs(x),abs(y))
        g=abs(np.log(s[iu[0]])-np.log(s[iu[1]])); k=m>=np.quantile(m,0.95)
        gap_big.append(np.median(g[k])); gap_all.append(np.median(g))
        cs.append(np.corrcoef(np.log(m),np.log(g+1e-3))[0,1])
        # fraction of off-diag energy in top 5% pairs
        e=x**2+y**2; spars.append(np.sort(e)[::-1][:len(e)//20].sum()/e.sum())
print('median log-sigma gap: top5% pairs',np.median(gap_big),' all pairs',np.median(gap_all))
print('corr(log|pair|, log gap) median',np.median(cs))
print('energy share of top 5% pairs: median',np.median(spars),np.percentile(spars,[10,90]))
