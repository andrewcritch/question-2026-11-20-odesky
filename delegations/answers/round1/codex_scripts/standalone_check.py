"""Check the three-parameter overlap ensemble with a shared Gamma spectrum.
This is separate from the conditional-Sigma test in fit_ensemble.py.
"""
import os,sys
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['VECLIB_MAXIMUM_THREADS']='1'
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
import numpy as np,csv,json
from investigate import profile,summaries
from fit_ensemble import draw_t,noise,project,eta,actual
from fit_ensemble import rng

def main():
    shape=(np.median([r['PR'] for r in actual])-1)/(64-np.median([r['PR'] for r in actual]))
    pars=list(csv.DictReader(open('ensemble_parameters.csv'))); rows=[]; allpr=[]
    for h,(p,real) in enumerate(zip(pars,actual)):
        trials=[]
        for j in range(32):
            s=np.sqrt(rng.gamma(shape,1/shape,64)); s.sort();s=s[::-1]
            tt=draw_t(real['tbar'],real['tstd'],real['PR'])
            W,_=project(np.diag(tt)+eta*noise(float(p['rhoq'])))
            r=dict(profile(s,W),**summaries(s,W));trials.append(r);allpr.append(r['PR'])
        rows.append(dict(layer=h//12,head=h%12,**{k:float(np.mean([r[k] for r in trials])) for k in trials[0]}))
    with open('standalone_predictions.csv','w') as f:
        wr=csv.DictWriter(f,fieldnames=rows[0]);wr.writeheader();wr.writerows(rows)
    out=dict(shape=float(shape),sample_PR_quantiles=np.quantile(allpr,[.1,.5,.9]).tolist())
    for k in actual[0]:
        a=np.array([r[k] for r in actual]);b=np.array([r[k] for r in rows]);out[k]=dict(quantiles=np.quantile(b,[.1,.5,.9]).tolist(),mae=float(np.mean(abs(a-b))),corr=float(np.corrcoef(a,b)[0,1]))
    with open('standalone_summary.json','w') as f:json.dump(out,f,indent=2)
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
