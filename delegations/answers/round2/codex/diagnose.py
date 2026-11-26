import os
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['VECLIB_MAXIMUM_THREADS']='1'
import numpy as np
d=np.load('heads.npz');ss=d['s'];WW=d['W'];n=64;iu=np.triu_indices(n,1)
rows=[]
for s,W in zip(ss,WW):
 t=np.diag(W);E=W-np.diag(t);S=(E+E.T)/2;A=(E-E.T)/2;v=s[:,None]*s[None,:];gap=abs(np.arange(n)[:,None]-np.arange(n)[None,:]); z=np.log(s);wt=s*s/(s@s)
 r=[]
 for B in [S,A]:
  p=B*B/np.sum(B*B);r.extend([np.sum(p*v)/(np.mean(v[iu])),np.sum(p*gap),np.sum(B**4)*4032/np.sum(B*B)**2,np.sum(p[:8,:8])])
 r.extend([np.corrcoef(t,z)[0,1],wt@t,np.mean(t),np.sqrt(wt@((t-wt@t)**2)),np.std(t),np.linalg.norm(W,2)])
 rows.append(r)
r=np.array(rows)
for j,name in enumerate(['S-weight','S-gap','S-kurt','S-top8','A-weight','A-gap','A-kurt','A-top8','t-logscorr','tweighted','tmean','twstd','tstd','Wnorm']):print(name,np.quantile(r[:,j],[.1,.5,.9]))
print('positive ab heads top8 S,A',r[[3,4,7,16,22],:8])
print('layer aggregate S/A variance by i,j bins')
for label,fn in [('S',lambda e:(e+e.T)/2),('A',lambda e:(e-e.T)/2)]:
 B=np.array([fn(W-np.diag(np.diag(W)))**2 for W in WW]);B/=B.sum((1,2))[:,None,None]
 print(label,np.round(B.mean(0).reshape(8,8,8,8).sum((1,3)),3))
