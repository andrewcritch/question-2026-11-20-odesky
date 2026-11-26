import os
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['VECLIB_MAXIMUM_THREADS']='1'
import numpy as np, csv, json
from safetensors.numpy import load_file
n=64

def profile(s,W):
    e,B=np.linalg.eigh(np.eye(len(s))-W.T@W)
    R=(B*np.sqrt(np.maximum(e,0)))@B.T
    L=np.zeros((2*len(s),2*len(s))); L[:len(s),:len(s)]=s[:,None]*W.T; L[:len(s),len(s):]=s[:,None]*R
    ev=np.linalg.eigvalsh((L+L.T)/2)
    lp=ev[-len(s):][::-1]; lm=-ev[:len(s)]
    sv=np.linalg.eigvalsh(1j*(L-L.T)/2)[-len(s):][::-1]
    norm=s@s; a=np.sum((L-L.T)**2)/4/norm; b=2*lp@lm/norm; diff=lp-lm
    c=np.maximum(diff,0)@np.maximum(diff,0)/norm; d=np.minimum(diff,0)@np.minimum(diff,0)/norm
    return dict(a=a,b=b,c=c,d=d,err1=np.linalg.norm(sv-np.sqrt(np.maximum(lp*lm,0)))/np.linalg.norm(sv),a_minus_b=a-b,c_minus_d=c-d,mincd=min(c,d))

def summaries(s,W):
    t=np.diag(W); w=s*s/(s@s); E=W-np.diag(t)
    return dict(tbar=w@t,tstd=np.sqrt(w@(t-w@t)**2),offrms=np.sqrt(np.sum(E*E)/(len(s)*(len(s)-1))),diagfrac=t@t/np.sum(W*W),PR=1/(w@w),pred_cd=w@(t*abs(t)),tmin=t.min(),tmax=t.max())

def extract():
    wts=load_file('ensemble_brief/gpt2_model.safetensors'); pre='' if 'h.0.attn.c_attn.weight' in wts else 'transformer.'
    ss=[]; WW=[]; keys=[]; rows=[]
    for l in range(12):
        A=wts[f'{pre}h.{l}.attn.c_attn.weight'].astype(float); g=wts[f'{pre}h.{l}.ln_1.weight'].astype(float)
        for h in range(12):
            for var in ['raw','lnfold']:
                Q=A[:,64*h:64*(h+1)].copy(); K=A[:,768+64*h:768+64*(h+1)].copy()
                if var=='lnfold':
                    Q*=g[:,None]; K*=g[:,None]; Q-=Q.mean(0); K-=K.mean(0)
                uq,rq=np.linalg.qr(Q); uk,rk=np.linalg.qr(K); x,s,yt=np.linalg.svd(rk@rq.T)
                W=(uk@x).T@(uq@yt.T); t=np.diag(W); E=W-np.diag(t)
                r=dict(layer=l,head=h,var=var,**profile(s,W),**summaries(s,W))
                r.update(recip=np.sum(E*E.T)/np.sum(E*E),offtrace=np.sum(s[:,None]*s[None,:]*E*E.T)/(s@s),snorm=np.linalg.norm(W,2),rankcorr=np.corrcoef(np.arange(64),t)[0,1])
                b=profile(s,np.diag(t))
                r.update({'block_'+k:v for k,v in b.items()})
                ss.append(s); WW.append(W); keys.append([l,h,0 if var=='raw' else 1]); rows.append(r)
        print('extracted layer',l,flush=True)
    np.savez('heads.npz',s=ss,W=WW,keys=keys)
    with open('diagnostics.csv','w') as f:
        wr=csv.DictWriter(f,fieldnames=rows[0]); wr.writeheader(); wr.writerows(rows)
    source=list(csv.DictReader(open('ensemble_brief/gpt2_W.csv')))
    err=max(abs(r[k]-float(next(z for z in source if int(z['layer'])==r['layer'] and int(z['head'])==r['head'] and z['var']==r['var'])[k])) for r in rows for k in ['a','b','c','d','err1','tbar','tstd','offrms','PR'])
    print('maximum discrepancy vs original csv',err)
    for var in ['raw','lnfold']:
        rr=[r for r in rows if r['var']==var]; print(var)
        for k in ['recip','offtrace','snorm','a_minus_b','block_a_minus_b','err1','block_err1']:
            print(k,np.quantile([r[k] for r in rr],[.1,.5,.9]))
if __name__=='__main__': extract()
