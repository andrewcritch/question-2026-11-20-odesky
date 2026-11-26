import csv,json,numpy as np
actual=list(csv.DictReader(open('actual.csv')));pred=list(csv.DictReader(open('final_predictions.csv')));pars=list(csv.DictReader(open('final_parameters.csv')))
ks=['err1','amb','cmd','mincd','diag','offrms','kurt','PR','symtop','tbar','tstd','q']
def vec(rows,k):return np.array([float(r[k]) for r in rows])
def fmt(x):return f'{x:.5g}'
lines=['| Statistic | Actual median [P10, P90] | Predicted median [P10, P90] | Pearson r | MAE |','|---|---:|---:|---:|---:|']
for k in ks:
 a=vec(actual,k);p=vec(pred,k);aq=np.quantile(a,[.5,.1,.9]);pq=np.quantile(p,[.5,.1,.9]);show=lambda q:f'{fmt(q[0])} [{fmt(q[1])}, {fmt(q[2])}]'
 lines.append(f'| {k} | {show(aq)} | {show(pq)} | {np.corrcoef(a,p)[0,1]:.4f} | {fmt(np.mean(abs(a-p)))} |')
out={};amb=vec(actual,'amb');pamb=vec(pred,'amb')
out['positive_actual']=int(np.sum(amb>0));out['positive_predicted_mean']=int(np.sum(pamb>0));out['sign_matches']=int(np.sum((amb>0)==(pamb>0)))
out['positive_sensitivity']=float(np.mean(pamb[amb>0]>0));out['negative_specificity']=float(np.mean(pamb[amb<0]<0))
for label,take in [('positive',amb>0),('negative',amb<0)]:
 a=vec(actual,'err1')[take];p=vec(pred,'err1')[take];out[label]=dict(n=int(take.sum()),actual=np.quantile(a,[.1,.5,.9]).tolist(),pred=np.quantile(p,[.1,.5,.9]).tolist(),corr=float(np.corrcoef(a,p)[0,1]),mae=float(np.mean(abs(a-p))))
out['worst_err1']=[]
for i in np.argsort(abs(vec(actual,'err1')-vec(pred,'err1')))[::-1][:12]:
 out['worst_err1'].append(dict(head=f'L{i//12}H{i%12}',err1_actual=float(actual[i]['err1']),err1_pred=float(pred[i]['err1']),amb_actual=float(actual[i]['amb']),amb_pred=float(pred[i]['amb']),q_actual=float(actual[i]['q']),q_pred=float(pred[i]['q']),err1_sd=float(pred[i]['err1_sd']),clipped=float(pred[i]['clipped'])))
for k in ['cmd','diag','mincd','kurt']:
 inds=np.argsort(abs(vec(actual,k)-vec(pred,k)))[::-1][:5];out['worst_'+k]=[dict(head=f'L{i//12}H{i%12}',actual=float(actual[i][k]),pred=float(pred[i][k])) for i in inds]
out['parameter_quantiles']={k:np.quantile(vec(pars,k),[.1,.5,.9]).tolist() for k in ['theta','mu','slope','sd','etaS','etaA','f','beta']}
out['overall_clip_fraction']=float(np.mean(vec(pred,'clipped')))
out['median_MC_standard_error_err1']=float(np.median(vec(pred,'err1_sd')/np.sqrt(128)))
out['max_MC_standard_error_err1']=float(np.max(vec(pred,'err1_sd')/np.sqrt(128)))
with open('tables.md','w') as f:f.write('\n'.join(lines)+'\n')
with open('diagnostic_summary.json','w') as f:json.dump(out,f,indent=2)
print('\n'.join(lines));print(json.dumps(out,indent=2))
