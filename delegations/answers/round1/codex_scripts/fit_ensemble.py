"""Conditional tests: keep each measured Sigma, randomize W. No profile fit.
Run with supplied venv Python -I fit_ensemble.py. Seed and repetitions below.
"""
import os, sys
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['VECLIB_MAXIMUM_THREADS']='1'
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
import numpy as np, csv, json
from investigate import profile, summaries

R=32
rng=np.random.default_rng(20261124)
data=np.load('heads.npz'); ss=data['s'][::2]; WW=data['W'][::2]
actual=[dict(profile(s,W),**summaries(s,W)) for s,W in zip(ss,WW)]
eta=float(np.median([r['offrms'] for r in actual]))

def project(W):
    A,d,B=np.linalg.svd(W); return (A*np.minimum(d,.999))@B, float(np.max(d)>.999)

def draw_t(mu,sd,pr):
    # Remove the finite effective-sample bias in the weighted sample variance.
    var=sd**2/(1-1/pr)
    concentration=max((1-mu*mu)/max(var,1e-12)-1,.01)
    return 2*rng.beta((1+mu)*concentration/2,(1-mu)*concentration/2,64)-1

def noise(rho):
    G=rng.standard_normal((64,64)); S=(G+G.T)/np.sqrt(2); A=(G-G.T)/np.sqrt(2)
    E=np.sqrt((1+rho)/2)*S+np.sqrt((1-rho)/2)*A
    np.fill_diagonal(E,0); return E

def run():
    rows=[]; fitted=[]
    for h,(s,W,real) in enumerate(zip(ss,WW,actual)):
        t=np.diag(W); E=W-np.diag(t)
        rho=np.sum(E*E.T)/np.sum(E*E)
        q=np.sum(s[:,None]*s[None,:]*E*E.T)/(s@s)
        C=s.sum()**2/(s@s)-1
        rhoq=np.clip(q/(eta**2*C),-.999,.999)
        fitted.append(dict(layer=h//12,head=h%12,mu=real['tbar'],sd=real['tstd'],rho=rho,rhoq=rhoq,q=q))
        models=['block_beta','iid_beta','elliptic_beta','weighted_elliptic_beta','elliptic_realdiag']
        for model in models:
            rr=[]
            for trial in range(R):
                tt=t if model=='elliptic_realdiag' else draw_t(real['tbar'],real['tstd'],real['PR'])
                r=0 if model=='iid_beta' else (rhoq if model=='weighted_elliptic_beta' else rho)
                W0=np.diag(tt) if model=='block_beta' else np.diag(tt)+eta*noise(r)
                Ws,clipped=project(W0)
                z=dict(profile(s,Ws),**summaries(s,Ws)); z['clipped']=clipped
                rr.append(z)
            row=dict(layer=h//12,head=h%12,model=model)
            for k in rr[0]:
                row[k]=float(np.mean([r[k] for r in rr])); row[k+'_sd']=float(np.std([r[k] for r in rr]))
            rows.append(row)
        if h%12==11: print('fitted layer',h//12,flush=True)
    for name,rs in [('ensemble_predictions.csv',rows),('ensemble_parameters.csv',fitted)]:
        with open(name,'w') as f:
            wr=csv.DictWriter(f,fieldnames=rs[0]); wr.writeheader(); wr.writerows(rs)
    report=dict(repetitions=R,seed=20261124,eta=eta,models={})
    ks=['err1','a_minus_b','c_minus_d','mincd','tbar','tstd','offrms','diagfrac','tmin','tmax']
    for model in ['actual']+models:
        rs=actual if model=='actual' else [r for r in rows if r['model']==model]
        out={}
        for k in ks:
            x=np.array([r[k] for r in rs]); y=np.array([r[k] for r in actual])
            corr=float(np.corrcoef(x,y)[0,1]) if np.std(x)>1e-14 and np.std(y)>1e-14 else None
            out[k]=dict(quantiles=np.quantile(x,[.1,.5,.9]).tolist(),mae=float(np.mean(abs(x-y))),rmse=float(np.sqrt(np.mean((x-y)**2))),corr=corr)
        if model!='actual':out['clipping_fraction']=float(np.mean([r['clipped'] for r in rs]))
        report['models'][model]=out
    with open('ensemble_summary.json','w') as f: json.dump(report,f,indent=2)
    print(json.dumps(report,indent=2))
if __name__=='__main__':run()
