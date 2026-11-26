import os,sys
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['VECLIB_MAXIMUM_THREADS']='1'
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
import csv,json,numpy as np
from investigate import profile

rows=list(csv.DictReader(open('diagnostics.csv')))
out={}
for var in ['raw','lnfold']:
    r=[z for z in rows if z['var']==var]
    x=lambda k:np.array([float(z[k]) for z in r])
    delta=x('a_minus_b')-x('block_a_minus_b')+x('offtrace')
    out[var]=dict(positive_a_minus_b=int(sum(x('a_minus_b')>0)),
        corr_q_ab=float(np.corrcoef(x('offtrace'),x('a_minus_b'))[0,1]),
        corr_qabs_err1=float(np.corrcoef(abs(x('offtrace')),x('err1'))[0,1]),
        corr_blockab_minus_q_ab=float(np.corrcoef(x('block_a_minus_b')-x('offtrace'),x('a_minus_b'))[0,1]),
        correction_mae=float(np.mean(abs(delta))),correction_abs_p90=float(np.quantile(abs(delta),.9)),
        block_cd_mae=float(np.mean(abs(x('c_minus_d')-x('block_c_minus_d')))),
        quantiles={k:np.quantile(x(k),[.1,.5,.9]).tolist() for k in ['err1','block_err1','a_minus_b','block_a_minus_b','offtrace','recip','snorm']})
    identity=2*x('a')+x('tbar')**2+x('tstd')**2+x('offtrace')-1
    out[var]['energy_identity_max_error']=float(np.max(abs(identity)))
print(json.dumps(out,indent=2))
with open('diagnostic_summary.json','w') as f:json.dump(out,f,indent=2)

# Independent direct-matrix check of the compressed profile calculation.
rng=np.random.default_rng(913)
n=7;N=23
K=rng.normal(size=(n,N));Q=rng.normal(size=(n,N));L=K.T@Q
u,s,v=np.linalg.svd(L,full_matrices=False);s=s[:n];W=u[:,:n].T@v[:n].T
z=profile(s,W)
ev=np.linalg.eigvalsh((L+L.T)/2);lp=ev[-n:][::-1];lm=-ev[:n]
sv=np.linalg.svd((L-L.T)/2,compute_uv=False)[:2*n:2]
direct=np.linalg.norm(sv-np.sqrt(lp*lm))/np.linalg.norm(sv)
assert abs(z['err1']-direct)<1e-12
print('Independent direct-matrix check passed; err1 discrepancy',abs(z['err1']-direct))
