"""Round-2 ensemble 'SVD-gauge split-pair' (SGSP). Fit per head on GPT-2, simulate, compare.
usage: python -I ens.py [nsim] [nu]
"""
import sys, numpy as np
from safetensors.numpy import load_file
WP='/private/tmp/claude-501/-Users-andrew-maisi-questions-2026-11-20-odesky/8a345037-c99c-4fe5-98da-2190c1ebad66/scratchpad/dl_gpt2/model.safetensors'
N,n=768,64
NSIM=int(sys.argv[1]) if len(sys.argv)>1 else 4
NU=float(sys.argv[2]) if len(sys.argv)>2 else 3.0
VARIANT=sys.argv[3] if len(sys.argv)>3 else 'tsym'   # tsym: heavy tail in symmetric part; gauss: none; tboth: both
rng=np.random.default_rng(11)
RHO=float(sys.argv[4]) if len(sys.argv)>4 else 0.05
FSPK=float(sys.argv[5]) if len(sys.argv)>5 else 0.5

def fullstats(L):
    k=L.shape[0]
    S=(L+L.T)/2; T=(L-L.T)/2
    ev=np.linalg.eigvalsh(S)
    lp=np.sort(ev[ev>1e-12*abs(ev).max()])[::-1][:n]; lm=np.sort(-ev[ev<-1e-12*abs(ev).max()])[::-1][:n]
    m=min(len(lp),len(lm)); lp,lm=lp[:m],lm[:m]
    sv=np.linalg.svd(T,compute_uv=False)[:2*n:2][:m]
    nL=np.sum(L*L); a=np.sum(T*T)/nL; b=2*lp@lm/nL; dif=lp-lm
    c=np.sum(np.maximum(dif,0)**2)/nL; d=np.sum(np.maximum(-dif,0)**2)/nL
    e1=np.linalg.norm(sv-np.sqrt(lp*lm))/np.linalg.norm(sv)
    U,s,Vt=np.linalg.svd(L); U,s,V=U[:,:n],s[:n],Vt[:n].T
    W=U.T@V; t=np.diag(W); wt=s**2/np.sum(s**2); tbar=wt@t; tstd=np.sqrt(wt@(t-tbar)**2)
    E=W-np.diag(t); offrms=np.sqrt(np.sum(E**2)/(n*n-n))
    F=np.sum(s**2); q=(np.outer(s,s)*E*E.T).sum()/F; m2=wt@(t**2)
    iu=np.triu_indices(n,1); x=W[iu]; y=W.T[iu]; off=np.concatenate([x,y])
    kurt=np.mean(off**4)/np.mean(off**2)**2
    mm=np.maximum(abs(x),abs(y)); kk=mm>=np.quantile(mm,0.95)
    sym=np.mean(abs(x[kk]+y[kk])/(abs(x[kk])+abs(y[kk])))
    return dict(err1=e1,a=a,b=b,amb=a-b,cmd=c-d,cpd=c+d,mincd=min(c,d),tbar=tbar,tstd=tstd,offrms=offrms,
                diag=np.sum(t**2)/np.sum(W**2),PR=F**2/np.sum(s**4),q=q,m2=m2,kurt=kurt,sym=sym)

def heavy(shape,nu):
    if not np.isfinite(nu): return rng.standard_normal(shape)
    z=rng.standard_t(nu,size=shape); return z/np.sqrt(nu/(nu-2))   # unit variance

def sample(p, variant=VARIANT, nu=NU):
    v,tau,om,vs,va=p['v'],p['tau'],p['om'],p['vs'],p['va']
    s=np.exp(np.sqrt(v)*rng.standard_normal(n))
    t=np.clip(tau+om*rng.standard_normal(n),-0.999,0.999)
    if variant=='gauss': Sm=heavy((n,n),np.inf); Am=heavy((n,n),np.inf)
    elif variant=='tboth': Sm=heavy((n,n),nu); Am=heavy((n,n),nu)
    elif variant=='spike':   # nu is reused as the spike fraction rho
        Sm=rng.standard_normal((n,n))*(rng.random((n,n))<nu)/np.sqrt(nu); Am=heavy((n,n),np.inf)
    elif variant=='spikemix':  # half of symmetric variance in sparse spikes, half Gaussian
        Sm=(rng.standard_normal((n,n))*(rng.random((n,n))<nu)/np.sqrt(nu)+rng.standard_normal((n,n)))/np.sqrt(2); Am=heavy((n,n),np.inf)
    else: Sm=heavy((n,n),nu); Am=heavy((n,n),np.inf)
    Sm=np.triu(Sm,1); Sm=Sm+Sm.T; Am=np.triu(Am,1); Am=Am-Am.T
    if variant=='mix':
        # bulk: isotropic Gaussian off-diagonal (no reciprocal correlation), variance p['beta']
        B=rng.standard_normal((n,n))*np.sqrt(p['beta'])
        # spikes: each unordered pair i<j is a spike w.p. RHO; spike is symmetric w.p. pi, else antisymmetric
        sp=np.triu(rng.random((n,n))<RHO,1); typ=np.where(rng.random((n,n))<p['pi'],1.0,-1.0)
        z=np.triu(rng.standard_normal((n,n)),1)*sp*np.sqrt(p['gam']/RHO)
        Sp=z+typ.T*0+ (z.T*np.triu(typ,1).T)
        W=np.diag(t)+B-np.diag(np.diag(B))+Sp
    else:
        W=np.diag(t)+np.sqrt(vs)*Sm+np.sqrt(va)*Am
    Uw,sw,Vw=np.linalg.svd(W); clipped=sw[0]>0.999
    W=(Uw*np.minimum(sw,0.999))@Vw
    # realize: U=[I;0], V=[W; (I-W^T W)^{1/2}] in R^{2n};  L=U diag(s) V^T
    C=np.eye(n)-W.T@W; ev,Ev=np.linalg.eigh(C); R=(Ev*np.sqrt(np.maximum(ev,0)))@Ev.T
    U=np.vstack([np.eye(n),np.zeros((n,n))]); V=np.vstack([W,R])
    # random orientation is irrelevant (O(2n) congruence invariance)
    return (U*s)@V.T, clipped

def fit(m):
    v=max(np.log(n/m['PR'])/4,1e-4)
    tau=m['tbar']; om=m['tstd']
    o2=m['offrms']**2
    kap=m['q']*np.exp(v)/(n-1)          # E[q] = kap * E sum_{i!=j} s_i s_j / E F = kap (n-1) e^{-v}
    kap=np.clip(kap,-o2,o2)
    gam=max(FSPK*o2,abs(kap)); pi=0.5*(1+kap/gam) if gam>0 else 0.5
    return dict(v=v,tau=tau,om=om,vs=(o2+kap)/2,va=(o2-kap)/2,beta=max(o2-gam,0),gam=gam,pi=pi)

w=load_file(WP); rows=[]
for l in range(12):
    Wa=w[f'h.{l}.attn.c_attn.weight'].astype(np.float64)
    for h in range(12):
        Q=Wa[:,h*n:(h+1)*n].T; K=Wa[:,N+h*n:N+(h+1)*n].T
        m=fullstats(K.T@Q); p=fit(m)
        sims=[];nclip=0
        for _ in range(NSIM):
            L,cl=sample(p); nclip+=cl; sims.append(fullstats(L))
        r=dict(l=l,h=h,nclip=nclip,**{'p_'+k:x for k,x in p.items()})
        for k in m: r['m_'+k]=m[k]; r['s_'+k]=float(np.mean([x[k] for x in sims]))
        rows.append(r)
import csv
out=f'/Users/andrew/maisi/questions/2026-11-20-odesky/delegations/answers/round2/claude-subagent/fit_{VARIANT}_nu{NU:g}_rho{RHO:g}_f{FSPK:g}.csv'
with open(out,'w',newline='') as f:
    wr=csv.DictWriter(f,fieldnames=list(rows[0])); wr.writeheader(); wr.writerows(rows)
def qq(v): v=np.asarray(v); return f'{np.median(v):+.3f} [{np.percentile(v,10):+.3f},{np.percentile(v,90):+.3f}]'
print(f'variant={VARIANT} nu={NU} rho={RHO} fspike={FSPK} nsim={NSIM}; heads with clipped W (any sim): {sum(r["nclip"]>0 for r in rows)}/144')
FIT=['PR','tbar','tstd','offrms','q']
for k in ['PR','tbar','tstd','offrms','q','err1','a','b','amb','cmd','cpd','mincd','diag','kurt','sym','m2']:
    me=np.array([r['m_'+k] for r in rows]); si=np.array([r['s_'+k] for r in rows])
    tag='FIT ' if k in FIT else 'pred'
    print(f'{tag} {k:7s} meas {qq(me):26s} model {qq(si):26s} corr {np.corrcoef(me,si)[0,1]:+.3f}')
amb_m=np.array([r['m_amb'] for r in rows]); amb_s=np.array([r['s_amb'] for r in rows])
print('sign agreement of a-b:',np.mean(np.sign(amb_m)==np.sign(amb_s)),' heads a>b meas',np.sum(amb_m>0),' model',np.sum(amb_s>0))
e_m=np.array([r['m_err1'] for r in rows]); e_s=np.array([r['s_err1'] for r in rows])
print('err1 median ratio model/meas',np.median(e_s/e_m))
for grp,sel in [('a>b',amb_m>0),('a<b',amb_m<=0)]:
    print(grp, 'err1 meas',qq(e_m[sel]),'model',qq(e_s[sel]),'sym meas',qq(np.array([r['m_sym'] for r in rows])[sel]))
worst=np.argsort(-np.abs(np.log(e_s/e_m)))[:8]
for i in worst: r=rows[i]; print(f"worst L{r['l']}H{r['h']} err1 meas {r['m_err1']:.3f} model {r['s_err1']:.3f} amb {r['m_amb']:+.3f}/{r['s_amb']:+.3f} kurt {r['m_kurt']:.1f}/{r['s_kurt']:.1f}")
