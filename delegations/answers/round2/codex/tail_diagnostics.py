import numpy as np
d=np.load('heads.npz'); iu=np.triu_indices(64,1)
rs=[]
for s,W in zip(d['s'],d['W']):
 E=W-np.diag(np.diag(W));A=(E-E.T)[iu]/2;v=(s[:,None]*s[None,:])[iu];v/=v.mean()
 vtot=np.mean(A*A);bg=(np.median(abs(A))/.67448975)**2;f=max(1-bg/vtot,0)
 ku=np.mean(A**4)/vtot**2;p=3*f*f/max(ku-3+3*f*f,1e-10)
 target=(np.mean(v*A*A)-(1-f)*vtot)/(f*vtot) if f>0 else 0
 rs.append([f,p,target,np.mean(v*A*A)/vtot])
r=np.array(rs)
print('f,p,target,total-target',np.quantile(r,[.1,.5,.9],axis=0)); print('out-of-range residual targets',(r[:,2]<0).sum());np.save('tail_diagnostics.npy',r)
