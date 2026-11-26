"""Mechanistic candidate: independent Gaussian feature pairs with random correlations.
Two fitted parameters per head; global effective dimension and strength shape.
"""
import os,sys
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['VECLIB_MAXIMUM_THREADS']='1'
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
import numpy as np,csv,json
from scipy.special import betaincinv
from scipy.optimize import least_squares
from investigate import profile,summaries
n=64; m=430; shape=10.; fit_reps=4; test_reps=16
rng=np.random.default_rng(8142)

def inputs(R):
    out=[]
    for _ in range(R):
        X=rng.normal(size=(m,n))/np.sqrt(m); Y=rng.normal(size=(m,n))/np.sqrt(m)
        # Reuse Gram matrices throughout optimization, so fits are cheap and smooth.
        xx=X.T@X; xy=X.T@Y; yy=Y.T@Y
        out.append((xx,xy,yy,rng.uniform(.00001,.99999,n),np.sqrt(rng.gamma(shape,1/shape,n))))
    return out

def sample(par,inp):
    mu=np.tanh(par[0]); concentration=np.exp(par[1])
    xx,xy,yy,u,strength=inp
    t=2*betaincinv((1+mu)*concentration/2,(1-mu)*concentration/2,u)-1
    v=np.sqrt(np.maximum(1-t*t,0)); ds=np.sqrt(strength)
    kk=xx*ds[:,None]*ds[None,:]
    qq=(xx*t[:,None]*t[None,:]+xy*t[:,None]*v[None,:]+xy.T*v[:,None]*t[None,:]+yy*v[:,None]*v[None,:])*ds[:,None]*ds[None,:]
    kq=(xx*t[None,:]+xy*v[None,:])*ds[:,None]*ds[None,:]
    rk=np.linalg.cholesky(kk).T; rq=np.linalg.cholesky(qq).T
    x,s,yt=np.linalg.svd(rk@rq.T)
    overlap=np.linalg.solve(rk.T,kq)@np.linalg.inv(rq)
    W=x.T@overlap@yt.T
    return s,W

def run():
    data=np.load('heads.npz'); SS=data['s'][::2]; WW=data['W'][::2]
    fit_inputs=inputs(fit_reps); test_inputs=inputs(test_reps)
    rows=[]
    for h,(s,W) in enumerate(zip(SS,WW)):
        target=summaries(s,W)
        def residual(par):
            z=[summaries(*sample(par,inp)) for inp in fit_inputs]
            return [(np.mean([r['tbar'] for r in z])-target['tbar']), (np.mean([r['tstd'] for r in z])-target['tstd'])]
        mu=target['tbar']; sd=max(target['tstd'],.06)
        p0=[np.arctanh(np.clip(mu,-.99,.99)),np.log(max((1-mu*mu)/(sd*sd)-1,.1))]
        fit=least_squares(residual,p0,bounds=([-4,-4],[4,9]),diff_step=.002,max_nfev=35,ftol=1e-5,xtol=1e-5,gtol=1e-5)
        z=[]
        for inp in test_inputs:
            sg,w=sample(fit.x,inp); z.append(dict(profile(sg,w),**summaries(sg,w)))
        row=dict(layer=h//12,head=h%12,mu=float(np.tanh(fit.x[0])),concentration=float(np.exp(fit.x[1])),fit_residual=float(np.linalg.norm(fit.fun)))
        row.update({k:float(np.mean([r[k] for r in z])) for k in z[0]}); rows.append(row)
        if h%12==11: print('fitted layer',h//12,flush=True)
    with open('feature_predictions.csv','w') as f:
        wr=csv.DictWriter(f,fieldnames=rows[0]); wr.writeheader();wr.writerows(rows)
    actual=[dict(profile(s,W),**summaries(s,W)) for s,W in zip(SS,WW)]
    out={}
    for k in actual[0]:
        a=np.array([r[k] for r in actual]);b=np.array([r[k] for r in rows]);out[k]=dict(quantiles=np.quantile(b,[.1,.5,.9]).tolist(),mae=float(np.mean(abs(a-b))),corr=float(np.corrcoef(a,b)[0,1]))
    out['fit_residual_quantiles']=np.quantile([r['fit_residual'] for r in rows],[.1,.5,.9,1]).tolist()
    with open('feature_summary.json','w') as f:json.dump(out,f,indent=2)
    print(json.dumps(out,indent=2))
if __name__=='__main__':run()
