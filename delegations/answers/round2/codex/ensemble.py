"""Eight-parameter sparse elliptic SVD ensemble. No target spectral errors used in fit."""
import os,sys
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['VECLIB_MAXIMUM_THREADS']='1'
os.environ['OMP_NUM_THREADS']='1'
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
import numpy as np, csv,json,argparse,multiprocessing as mp
from scipy.special import ndtri
from scipy.optimize import brentq
from extract import profile
n=64; iu=np.triu_indices(n,1); cap=.999

def spectrum(pr):
    z=ndtri((np.arange(n)+.5)/n)[::-1]
    def make(v):
        s=np.exp(v*(z-z.max()));return s/np.linalg.norm(s)
    v=brentq(lambda v:1/np.sum(make(v)**4)-pr,0,10)
    return make(v),v

def fit(s,W):
    s=s/np.linalg.norm(s);w=s*s;t=np.diag(W);z=np.log(s);z-=w@z
    mu=w@t; slope=(w*z)@(t-mu)/(w@(z*z));res=t-mu-slope*z
    sd=np.sqrt(w@(res*res)/max(1-2*np.sum(w*w),.1))
    E=W-np.diag(t);S=(E+E.T)/2;A=(E-E.T)/2
    etaS=np.sqrt(np.sum(S*S)/(n*(n-1)));etaA=np.sqrt(np.sum(A*A)/(n*(n-1)))
    f=np.clip(1-(np.median(abs(A[iu]))/.6744897501960817)**2/etaA**2,.001,.999)
    v=(s[:,None]*s[None,:])[iu]; target=(np.sum(v*A[iu]**2)/np.sum(A[iu]**2)-(1-f)*np.mean(v))/f
    target=np.clip(target,v.min()*1.001,v.max()*.999)
    lv=np.log(v)
    def centroid(beta):
        x=np.exp(beta*lv-np.max(beta*lv));return np.sum(x*v)/np.sum(x)
    beta=brentq(lambda b:centroid(b)-target,-300,300)
    sp,theta=spectrum(1/np.sum(w*w))
    return dict(mu=mu,slope=slope,sd=sd,etaS=etaS,etaA=etaA,f=f,beta=beta,theta=theta,chi=np.sum(v*A[iu]**2)/np.sum(A[iu]**2)/np.mean(v))

def draw(par,rng,p=.05,alpha=.25,conditional_s=None,variant='canonical'):
    z=ndtri((np.arange(n)+.5)/n)[::-1]
    s=np.exp(par['theta']*(z-z.max()));s/=np.linalg.norm(s)
    if conditional_s is not None:s=conditional_s/np.linalg.norm(conditional_s)
    z=np.log(s);z-=s*s@z
    t=par['mu']+par['slope']*z+par['sd']*rng.standard_normal(n)
    v=(s[:,None]*s[None,:])[iu]
    def variance(exponent):
        r=np.exp(exponent*np.log(v)-np.max(exponent*np.log(v)));return r/np.mean(r)
    xs=par['etaS']*np.sqrt(variance(alpha))*rng.standard_normal(len(v))
    xa=par['etaA']*(np.sqrt(1-par['f'])*rng.standard_normal(len(v))+np.sqrt(par['f']*variance(par['beta']))*rng.standard_normal(len(v))*(rng.random(len(v))<p)/np.sqrt(p))
    if variant=='shot':
        prob=variance(par['beta']);prob/=prob.sum();m=max(int(round(p*len(v))),1)
        loc=rng.choice(len(v),size=m,p=prob);tail=np.zeros(len(v));np.add.at(tail,loc,rng.standard_normal(m))
        tail*=par['etaA']*np.sqrt(par['f'])/np.sqrt(np.mean(tail*tail))
        bg=rng.standard_normal(len(v));bg*=par['etaA']*np.sqrt(1-par['f'])/np.sqrt(np.mean(bg*bg))
        xa=bg+tail
        xs*=par['etaS']/np.sqrt(np.mean(xs*xs))
    if variant=='norm':
        xs*=par['etaS']/np.sqrt(np.mean(xs*xs));xa*=par['etaA']/np.sqrt(np.mean(xa*xa))
    if variant=='moment':
        xa=np.sqrt(1-par['f'])*rng.standard_normal(len(v))+np.sqrt(par['f'])*rng.standard_normal(len(v))*(rng.random(len(v))<p)/np.sqrt(p)
        target=np.clip(par['chi']*np.mean(v),v.min()*1.001,v.max()*.999)
        lv=np.log(v)
        def tilt(b):
            r=xa*np.exp(.5*b*lv-.5*np.max(b*lv));return r
        beta=brentq(lambda b:np.sum(v*tilt(b)**2)/np.sum(tilt(b)**2)-target,-1000,1000)
        xa=tilt(beta);xa*=par['etaA']/np.sqrt(np.mean(xa*xa))
        xs*=par['etaS']/np.sqrt(np.mean(xs*xs))
    W=np.diag(t);W[iu]=xs+xa;W[(iu[1],iu[0])]=xs-xa
    u,d,vt=np.linalg.svd(W);clipped=float(d.max()>cap);excess=np.sum(np.maximum(d-cap,0)**2)/np.sum(d*d)
    W=(u*np.minimum(d,cap))@vt
    return s,W,clipped,excess

def worker(task):
    h,s,W,p,alpha,R,conditional,variant,seed=task;par=fit(s,W);rng=np.random.default_rng(seed+h*1009+int(p*10000));rs=[]
    for r in range(R):
        sh,Wh,clipped,excess=draw(par,rng,p,alpha,s if conditional else None,variant)
        row=profile(sh,Wh);row.update(clipped=clipped,excess=excess);rs.append(row)
    out=dict(layer=h//12,head=h%12)
    for k in rs[0]:
        vals=[r[k] for r in rs];out[k]=float(np.mean(vals));out[k+'_sd']=float(np.std(vals));out[k+'_lo']=float(np.quantile(vals,.05));out[k+'_hi']=float(np.quantile(vals,.95))
    return out,dict(layer=h//12,head=h%12,**par)

def write_csv(path,rows):
    with open(path,'w') as f:
        wr=csv.DictWriter(f,fieldnames=rows[0]);wr.writeheader();wr.writerows(rows)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--p',type=float,default=1/128);ap.add_argument('--alpha',type=float,default=.25);ap.add_argument('--R',type=int,default=32);ap.add_argument('--conditional',action='store_true');ap.add_argument('--variant',default='canonical');ap.add_argument('--label',default='model');ap.add_argument('--seed',type=int,default=230101);args=ap.parse_args()
    d=np.load('heads.npz');tasks=[(h,s,W,args.p,args.alpha,args.R,args.conditional,args.variant,args.seed) for h,(s,W) in enumerate(zip(d['s'],d['W']))]
    workers=int(os.environ.get('HEAVY_MAX_WORKERS','1'))
    if workers>1:
        with mp.Pool(processes=workers,maxtasksperchild=1) as pool:result=list(pool.imap(worker,tasks))
    else:result=[worker(t) for t in tasks]
    out=[r[0] for r in result];pars=[r[1] for r in result];write_csv(args.label+'_predictions.csv',out);write_csv(args.label+'_parameters.csv',pars)
    actual=list(csv.DictReader(open('actual.csv')));report={}
    for k in ['err1','amb','cmd','mincd','diag','offrms','kurt','PR','tbar','tstd','q','symtop','clipped','excess']:
        y=np.array([r[k] for r in out]);a=np.array([float(r[k]) for r in actual]) if k in actual[0] else y
        report[k]=dict(actual=np.quantile(a,[.1,.5,.9]).tolist(),pred=np.quantile(y,[.1,.5,.9]).tolist(),corr=float(np.corrcoef(a,y)[0,1]),mae=float(np.mean(abs(a-y))),coverage=float(np.mean([(float(ar[k])>=r[k+'_lo']) and (float(ar[k])<=r[k+'_hi']) for ar,r in zip(actual,out)]))) if k in actual[0] else dict(pred=np.quantile(y,[.1,.5,.9]).tolist())
    with open(args.label+'_summary.json','w') as f:json.dump(report,f,indent=2)
    print(json.dumps(report,indent=2),flush=True)
if __name__=='__main__':main()
