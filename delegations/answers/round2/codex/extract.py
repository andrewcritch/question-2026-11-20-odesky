import os
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['VECLIB_MAXIMUM_THREADS']='1'
os.environ['OMP_NUM_THREADS']='1'
import numpy as np, json, csv
from safetensors.numpy import load_file
from scipy.linalg import eigh
PATH='/private/tmp/claude-501/-Users-andrew-maisi-questions-2026-11-20-odesky/8a345037-c99c-4fe5-98da-2190c1ebad66/scratchpad/dl_gpt2/model.safetensors'
n=64

def profile(s,W):
    e,B=eigh(np.eye(n)-W.T@W,check_finite=False)
    R=(B*np.sqrt(np.maximum(e,0)))@B.T
    L=np.zeros((2*n,2*n));L[:n,:n]=s[:,None]*W.T;L[:n,n:]=s[:,None]*R
    ev=eigh((L+L.T)/2,eigvals_only=True,check_finite=False)
    lp=ev[-n:][::-1];lm=-ev[:n]
    sv=eigh(1j*(L-L.T)/2,eigvals_only=True,check_finite=False)[-n:][::-1]
    F=s@s; t=np.diag(W);E=W-np.diag(t);wt=s*s/F
    q=np.sum(s[:,None]*s[None,:]*E*E.T)/F
    a=(1-wt@(t*t)-q)/2;b=2*lp@lm/F
    df=lp-lm;c=np.maximum(df,0)@np.maximum(df,0)/F;d=np.minimum(df,0)@np.minimum(df,0)/F
    iu=np.triu_indices(n,1);x=E[iu];y=E.T[iu];z=np.r_[x,y];ii=np.maximum(abs(x),abs(y))>=np.quantile(np.maximum(abs(x),abs(y)),.95)
    return dict(err1=np.linalg.norm(sv-np.sqrt(np.maximum(lp*lm,0)))/np.linalg.norm(sv),amb=a-b,cmd=c-d,mincd=min(c,d),diag=np.sum(t*t)/np.sum(W*W),offrms=np.sqrt(np.mean(z*z)),kurt=np.mean(z**4)/np.mean(z*z)**2,PR=1/(wt@wt),tbar=wt@t,tstd=np.sqrt(wt@((t-wt@t)**2)),q=q,symtop=np.mean(abs(x[ii]+y[ii])/(abs(x[ii])+abs(y[ii]))),a=a,b=b,c=c,d=d,logerr=np.sum(np.log(sv))-.5*np.sum(np.log(lp*lm)))

def extract():
    weights=load_file(PATH);ss=[];WW=[];out=[]
    for l in range(12):
      A=weights[f'h.{l}.attn.c_attn.weight'].astype(float)
      for h in range(12):
        Q=A[:,64*h:64*(h+1)];K=A[:,768+64*h:768+64*(h+1)]
        uq,rq=np.linalg.qr(Q);uk,rk=np.linalg.qr(K);u,s,vt=np.linalg.svd(rk@rq.T);W=(uk@u).T@(uq@vt.T)
        ss.append(s);WW.append(W);out.append(dict(layer=l,head=h,**profile(s,W)))
      print('layer',l,flush=True)
    np.savez('heads.npz',s=ss,W=WW)
    with open('actual.csv','w') as f:
      wr=csv.DictWriter(f,fieldnames=out[0]);wr.writeheader();wr.writerows(out)
    print({k:np.quantile([r[k] for r in out],[.1,.5,.9]).tolist() for k in out[0]})
if __name__=='__main__':extract()
