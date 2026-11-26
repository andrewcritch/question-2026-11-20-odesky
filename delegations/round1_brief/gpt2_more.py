import numpy as np, sys, csv
from safetensors.numpy import load_file
rows=list(csv.DictReader(open(sys.argv[2])))
for r in rows:
    for k in r:
        if k!='var': r[k]=float(r[k])
raw=[r for r in rows if r['var']=='raw']; ln=[r for r in rows if r['var']=='lnfold']
print("raw heads sorted by tbar (extremes):")
srt=sorted(raw,key=lambda r:r['tbar'])
for r in srt[:5]+srt[-5:]:
    print(f"  L{int(r['layer'])}H{int(r['head']):<3d} tbar={r['tbar']:+.3f} tstd={r['tstd']:.3f} t∈[{r['tmin']:+.2f},{r['tmax']:+.2f}] c-d={r['c_minus_d']:+.3f} a-b={r['a_minus_b']:+.3f} err1={r['err1']:.3f} diagfrac={r['diagfrac']:.2f}")
print("lnfold outliers by err1:")
for r in sorted(ln,key=lambda r:-r['err1'])[:8]:
    rr=[x for x in raw if x['layer']==r['layer'] and x['head']==r['head']][0]
    print(f"  L{int(r['layer'])}H{int(r['head']):<3d} err1 ln={r['err1']:.3f} raw={rr['err1']:.3f}  a-b ln={r['a_minus_b']:+.3f} PR ln={r['PR']:.1f} raw={rr['PR']:.1f}")
# correlations across heads
a=lambda k,R: np.array([r[k] for r in R])
print("corr(err1, tstd) raw:",np.corrcoef(a('err1',raw),a('tstd',raw))[0,1].round(3))
print("corr(a-b, tstd) raw:",np.corrcoef(a('a_minus_b',raw),a('tstd',raw))[0,1].round(3))
print("corr(|tbar|, diagfrac) raw:",np.corrcoef(np.abs(a('tbar',raw)),a('diagfrac',raw))[0,1].round(3))
print("frac heads |tbar|>2*tstd:",np.mean(np.abs(a('tbar',raw))>2*a('tstd',raw)).round(3))
by_layer=[np.median(np.abs([r['tbar'] for r in raw if r['layer']==l])) for l in range(12)]
print("median |tbar| by layer:",np.round(by_layer,3))
# within-head: does t_i trend with singular index?
wts=load_file(sys.argv[1]); N,n=768,64
cors=[]
for l in range(12):
    Wa=wts[f'h.{l}.attn.c_attn.weight']
    for h in range(12):
        Q=Wa[:,h*n:(h+1)*n].T.astype(float); K=Wa[:,N+h*n:N+(h+1)*n].T.astype(float)
        U,s,Vt=np.linalg.svd(K.T@Q); t=np.diag(U[:,:n].T@Vt[:n].T)
        cors.append(np.corrcoef(np.arange(n),t)[0,1]*np.sign(np.mean(t[:8])) if abs(np.mean(t))>0.05 else np.nan)
cors=np.array(cors); cors=cors[~np.isnan(cors)]
print(f"heads with |mean t|>0.05: {len(cors)}; median corr(index, signed t) = {np.median(cors):+.3f} (negative => top singular dirs more aligned)")
