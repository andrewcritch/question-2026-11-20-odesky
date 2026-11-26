"""Global constants use overlap statistics, not spectral relation errors."""
import numpy as np,csv,json
from scipy.optimize import brentq
d=np.load('heads.npz');iu=np.triu_indices(64,1);alphas=[];kurt=[]
for s,W in zip(d['s'],d['W']):
 E=W-np.diag(np.diag(W));S=(E+E.T)[iu]/2;v=(s[:,None]*s[None,:])[iu];lv=np.log(v);target=np.sum(v*S*S)/np.sum(S*S)
 def fun(a):
  r=np.exp(a*lv-np.max(a*lv));return r@v/r.sum()-target
 alphas.append(brentq(fun,-300,300));z=np.r_[E[iu],E.T[iu]];kurt.append(np.mean(z**4)/np.mean(z*z)**2)
pred8=np.array([float(r['kurt']) for r in csv.DictReader(open('shot8_predictions.csv'))]);pred16=np.array([float(r['kurt']) for r in csv.DictReader(open('shot_predictions.csv'))])
out={}
for label,take in [('all',np.ones(144,dtype=bool)),('even',np.arange(144)%2==0),('odd',np.arange(144)%2==1)]:
 # Moment normalization of m Gaussian impulses gives approximately 1/(m+2).
 k8=np.median(pred8[take]);k16=np.median(pred16[take]);target=np.median(np.array(kurt)[take]);a=(k8-k16)/(1/10-1/18);c=k8-a/10;mf=a/(target-c)-2
 out[label]=dict(alpha=float(np.median(np.array(alphas)[take])),m_interpolated=float(mf),m=int(round(mf)),kurt_target=float(target),pilot_kurt8=float(k8),pilot_kurt16=float(k16))
with open('calibration.json','w') as f:json.dump(out,f,indent=2)
print(json.dumps(out,indent=2))
