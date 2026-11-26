import os,sys
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['VECLIB_MAXIMUM_THREADS']='1'
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
import numpy as np,json,csv
from safetensors.numpy import load_file
from scipy.linalg import eigh
from extract import profile,PATH
from ensemble import fit,draw

def direct(L,n):
 S=(L+L.T)/2;T=(L-L.T)/2;ev=eigh(S,eigvals_only=True);lp=ev[-n:][::-1];lm=-ev[:n];sv=np.linalg.svd(T,compute_uv=False)[:2*n:2];F=np.sum(L*L)
 a=np.sum(T*T)/F;b=2*lp@lm/F;dif=lp-lm;c=np.maximum(dif,0)@np.maximum(dif,0)/F;d=np.minimum(dif,0)@np.minimum(dif,0)/F
 return dict(err1=np.linalg.norm(sv-np.sqrt(np.maximum(lp*lm,0)))/np.linalg.norm(sv),amb=a-b,cmd=c-d,mincd=min(c,d),a=a,b=b,c=c,d=d)

weights=load_file(PATH);data=np.load('heads.npz');rng=np.random.default_rng(77224);report={};maxdif=0;maxframe=0
for h in [3,7,36,69,143]:
 l=h//12;j=h%12;A=weights[f'h.{l}.attn.c_attn.weight'].astype(float);Q=A[:,64*j:64*(j+1)].T;K=A[:,768+64*j:768+64*(j+1)].T
 d=direct(K.T@Q,64);r=profile(data['s'][h],data['W'][h]);maxdif=max(maxdif,max(abs(d[k]-r[k]) for k in d))
report['max_direct_raw_difference']=maxdif
maxdif=0
for h in [3,36,69,143]:
 par=fit(data['s'][h],data['W'][h]);s,W,_,_=draw(par,rng,9/2016,.53996028,variant='shot');O,_=np.linalg.qr(rng.standard_normal((768,128)));U=O[:,:64]
 ev,B=eigh(np.eye(64)-W.T@W);V=U@W+O[:,64:]@((B*np.sqrt(ev))@B.T);K=np.sqrt(s)[:,None]*U.T;Q=np.sqrt(s)[:,None]*V.T
 maxframe=max(maxframe,np.max(abs(U.T@V-W)),np.max(abs(V.T@V-np.eye(64))))
 d=direct(K.T@Q,64);r=profile(s,W);maxdif=max(maxdif,max(abs(d[k]-r[k]) for k in d))
report['max_generated_frame_error']=maxframe;report['max_generated_direct_difference']=maxdif
for sign in [1,-1]:
 r=.3;W=np.array([[0,r],[sign*r,0]]);R=np.sqrt(1-r*r)*np.eye(2);L=np.zeros((4,4));L[:2,:2]=W.T;L[:2,2:]=R
 d=direct(L,2);report['symmetric_block' if sign==1 else 'skew_block']=d
rows=list(csv.DictReader(open('actual.csv')));report['max_logmean_error']=max(abs(float(r['logerr'])) for r in rows)
pars=[fit(s,W) for s,W in zip(data['s'],data['W'])];report['f_floor_heads']=int(sum(p['f']<=.001 for p in pars));report['f_ceiling_heads']=int(sum(p['f']>=.999 for p in pars))
with open('validation.json','w') as f:json.dump(report,f,indent=2)
print(json.dumps(report,indent=2))
