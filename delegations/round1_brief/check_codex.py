import numpy as np
from safetensors.numpy import load_file
import sys
sys.path.insert(0,'.')
w=load_file(sys.argv[1]); N,n=768,64
def prof(L):
    S=(L+L.T)/2;T=(L-L.T)/2;ev=np.linalg.eigvalsh(S)
    lp=np.sort(ev[ev>0])[::-1][:n];lm=np.sort(-ev[ev<0])[::-1][:n];F=np.sum(L*L)
    return np.sum(T*T)/F, 2*lp@lm/F
mx=0;viol=0;cnt=0;qs=[];abs_=[]
for l in range(12):
    Wa=w[f'h.{l}.attn.c_attn.weight'].astype(float)
    for h in range(12):
        Q=Wa[:,h*n:(h+1)*n].T;K=Wa[:,N+h*n:N+(h+1)*n].T;L=K.T@Q
        U,s,Vt=np.linalg.svd(L);U,s,V=U[:,:n],s[:n],Vt[:n].T;W=U.T@V;t=np.diag(W);F=np.sum(s**2)
        E=W-np.diag(t);m2=np.sum(s**2*t**2)/F;q=np.sum(np.outer(s,s)*E*E.T)/F
        a,b=prof(L);mx=max(mx,abs(a-(1-m2-q)/2));qs.append(q);abs_.append(a-b)
        Ld=U@np.diag(s*t)@U.T*0  # placeholder
        # diagonal-only surrogate: build from (s, diag t) in 2n dims
        R=np.sqrt(np.clip(1-t**2,0,None))
        Ub=np.vstack([np.eye(n),np.zeros((n,n))]);Vb=np.vstack([np.diag(t),np.diag(R)])
        ad,bd=prof(Ub@np.diag(s)@Vb.T);cnt+=1;viol+=(ad-bd>1e-9)
print("max |a-(1-m2-q)/2| =",mx)
print("diagonal surrogates with a-b>0:",viol,"of",cnt)
print("raw heads with a-b>0:",sum(x>0 for x in abs_),"corr(q,a-b)=",np.corrcoef(qs,abs_)[0,1].round(4))
