import os,sys
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['VECLIB_MAXIMUM_THREADS']='1'
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
import numpy as np,csv,json
from extract import profile
d=np.load('heads.npz');iu=np.triu_indices(64,1);rows=[];diag=[]
for h,(s,W) in enumerate(zip(d['s'],d['W'])):
 t=np.diag(W);D=np.diag(t);E=W-D;S=(E+E.T)/2;A=(E-E.T)/2
 de=dict(layer=h//12,head=h%12)
 de['S_kurt']=np.mean(S[iu]**4)/np.mean(S[iu]**2)**2
 de['A_kurt']=np.mean(A[iu]**4)/np.mean(A[iu]**2)**2
 de['A_fourth_share']=np.sum(A**4)/np.sum(S**4+6*S*S*A*A+A**4)
 for frac in [.05,.01,.005,.001]:
  x=E[iu];y=E.T[iu];m=np.maximum(abs(x),abs(y));take=m>=np.quantile(m,1-frac)
  de['symtop'+str(frac)]=np.mean(abs(x[take]+y[take])/(abs(x[take])+abs(y[take])))
 diag.append(de)
 for name,B in [('actual',W),('diagonal',D),('symmetric',D+S),('skew',D+A)]:
  u,v,vt=np.linalg.svd(B);B=(u*np.minimum(v,.999))@vt
  rows.append(dict(layer=h//12,head=h%12,model=name,**profile(s,B)))
for name,rr in [('ablation_predictions.csv',rows),('fourth_moments.csv',diag)]:
 with open(name,'w') as f:
  wr=csv.DictWriter(f,fieldnames=rr[0]);wr.writeheader();wr.writerows(rr)
print('diagnostics',json.dumps({k:np.quantile([r[k] for r in diag],[.1,.5,.9]).tolist() for k in diag[0]},indent=2))
for name in ['actual','diagonal','symmetric','skew']:
 rr=[r for r in rows if r['model']==name]
 print(name,{k:np.quantile([r[k] for r in rr],[.1,.5,.9]).tolist() for k in ['err1','amb','kurt','symtop']})
