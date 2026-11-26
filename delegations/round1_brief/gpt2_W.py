import numpy as np, sys, csv
from safetensors.numpy import load_file
wts=load_file(sys.argv[1]); out=sys.argv[2]
N,n,H=768,64,12
pre='' if 'h.0.attn.c_attn.weight' in wts else 'transformer.'
rng=np.random.default_rng(0)
def profile(L):
    S=(L+L.T)/2; T=(L-L.T)/2
    ev=np.linalg.eigvalsh(S); lp=np.sort(ev[ev>0])[::-1][:n]; lm=np.sort(-ev[ev<0])[::-1][:n]
    sv=np.linalg.svd(T,compute_uv=False)[:2*n:2]
    nL=np.sum(L*L); a=np.sum(T*T)/nL; b=2*lp@lm/nL; dif=lp-lm
    c=np.sum(np.maximum(dif,0)**2)/nL; d=np.sum(np.maximum(-dif,0)**2)/nL
    e1=np.linalg.norm(sv-np.sqrt(lp*lm))/np.linalg.norm(sv)
    return a,b,c,d,e1
def analyze(L):
    a,b,c,d,e1=profile(L)
    U,s,Vt=np.linalg.svd(L); U,s,V=U[:,:n],s[:n],Vt[:n].T
    W=U.T@V; t=np.diag(W); w=s**2/np.sum(s**2)
    tbar=w@t; tstd=np.sqrt(w@(t-tbar)**2)
    off=W-np.diag(t); offrms=np.sqrt(np.sum(off**2)/(n*n-n))
    pred_cd=w@(t*np.abs(t))
    pr=np.sum(s**2)**2/np.sum(s**4)
    # rank-n surrogate with W replaced by its diagonal (block normal form), same Sigma,t
    # and constant-t surrogate: profile is exactly rank-one point at tbar
    return dict(a=a,b=b,c=c,d=d,err1=e1,a_minus_b=a-b,mincd=min(c,d),c_minus_d=c-d,
                tbar=tbar,tstd=tstd,offrms=offrms,pred_cd=pred_cd,diagfrac=np.sum(t**2)/np.sum(W**2),PR=pr,
                tmin=t.min(),tmax=t.max())
rows=[]
P=np.eye(N)-np.ones((N,N))/N
for l in range(12):
    Wa=wts[f'{pre}h.{l}.attn.c_attn.weight']; g=wts[f'{pre}h.{l}.ln_1.weight']
    for h in range(H):
        Q=Wa[:,h*n:(h+1)*n].T; K=Wa[:,N+h*n:N+(h+1)*n].T
        L=K.T@Q
        for var,LL in [('raw',L),('lnfold',P@(g[:,None]*L*g[None,:])@P)]:
            r=analyze(LL.astype(np.float64)); r.update(layer=l,head=h,var=var); rows.append(r)
        # null: same Q,K norms, gaussian
        Qg=rng.standard_normal((n,N))*np.linalg.norm(Q)/np.sqrt(n*N); Kg=rng.standard_normal((n,N))*np.linalg.norm(K)/np.sqrt(n*N)
        r=analyze(Kg.T@Qg); r.update(layer=l,head=h,var='gauss'); rows.append(r)
keys=list(rows[0].keys())
with open(out,'w',newline='') as f:
    wr=csv.DictWriter(f,fieldnames=keys); wr.writeheader(); wr.writerows(rows)
print('null offdiag rms 1/sqrt(N)=',1/np.sqrt(N))
for var in ['raw','lnfold','gauss']:
    R=[r for r in rows if r['var']==var]
    def q(k): v=np.array([r[k] for r in R]); return f"{np.median(v):+.3f} [{np.percentile(v,10):+.3f},{np.percentile(v,90):+.3f}]"
    print(f"\n== {var} (median [p10,p90]) ==")
    for k in ['err1','a_minus_b','mincd','c_minus_d','pred_cd','tbar','tstd','offrms','diagfrac','PR']:
        print(f"  {k:10s} {q(k)}")
    cd=np.array([r['c_minus_d'] for r in R]); pc=np.array([r['pred_cd'] for r in R])
    print(f"  corr(c-d, pred_cd)={np.corrcoef(cd,pc)[0,1]:.3f}  mean|c-d - pred|={np.mean(np.abs(cd-pc)):.3f}")
