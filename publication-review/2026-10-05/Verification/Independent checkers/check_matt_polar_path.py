"""Independent numerical sanity check of the stated generic polar-path theorem.

Uses NumPy linear algebra, not the entrant's code. This is not a proof, a
Lean replay, a circuit-cost test or a historical-novelty determination.
"""
from pathlib import Path
import json,math
import numpy as np

HERE=Path(__file__).resolve().parent
L=2*math.pi

def polar(a):
    u,_,vh=np.linalg.svd(a)
    return u@vh

def branch(z,sign):
    return np.angle(-1j*z)+math.pi/2 if sign>0 else np.angle(1j*z)-math.pi/2

def normalized(c,sigma):
    values=np.sort(np.mod(np.angle(np.linalg.eigvals(c)),L))
    difference=(sigma-values.sum())/L
    k=round(float(difference))
    assert abs(difference-k)<1e-9
    h,r=divmod(k,len(values))
    return np.concatenate((values[r:],values[:r]+L))+L*h

records=[]
for dimension in [4,8,12]:
    for seed in [17,41,103]:
        rng=np.random.default_rng(seed+dimension*1000)
        x=rng.normal(size=(dimension,dimension))+1j*rng.normal(size=(dimension,dimension))
        y=rng.normal(size=(dimension,dimension))+1j*rng.normal(size=(dimension,dimension))
        eigenvalues=np.linalg.eigvals(np.linalg.solve(x,y))
        crossings=np.sort(np.mod(-np.angle(eigenvalues),math.pi))
        assert min(np.diff(np.concatenate((crossings,crossings[:1]+math.pi))))>1e-8
        alpha=None
        for left,right in zip(crossings,np.concatenate((crossings[1:],crossings[:1]+math.pi))):
            candidate=(left+right)/2
            trial=eigenvalues*np.exp(1j*candidate)
            if np.count_nonzero(trial.imag>0)==dimension//2:
                alpha=float(candidate);break
        assert alpha is not None
        tau=eigenvalues*np.exp(1j*alpha)
        signs=np.sign(tau.imag)
        assert abs(signs.sum())==0 and min(abs(tau.imag))>1e-8
        beta_values=np.linspace(0,math.pi,129)
        matrices=[];lifts=[];imbalance=[];worst_unitary=0.;worst_det=0.;smallest_singular=math.inf
        for beta in beta_values:
            c,s=math.cos(beta/2),math.sin(beta/2)
            xb=np.exp(-1j*alpha/2)*c*x+np.exp(1j*alpha/2)*s*y
            yb=-np.exp(-1j*alpha/2)*s*x+np.exp(1j*alpha/2)*c*y
            smallest_singular=min(smallest_singular,float(np.linalg.svd(xb,compute_uv=False)[-1]),float(np.linalg.svd(yb,compute_uv=False)[-1]))
            cb=-1j*polar(xb).conj().T@polar(yb)
            sigma=sum(branch(c*t-s,sign)-branch(c+s*t,sign) for t,sign in zip(tau,signs))
            nu=normalized(cb,sigma)
            p=dimension//4
            value=float(nu[p:3*p].sum()-(nu[:p].sum()+nu[3*p:].sum()))
            worst_unitary=max(worst_unitary,float(np.max(abs(cb@cb.conj().T-np.eye(dimension)))))
            worst_det=max(worst_det,float(abs(np.linalg.det(cb)-np.exp(1j*sigma))))
            matrices.append(cb);lifts.append(nu);imbalance.append(value)
        adjoint_error=float(np.max(abs(matrices[-1]-matrices[0].conj().T)))
        reversal_error=float(np.max(abs(lifts[-1]+lifts[0][::-1])))
        sign_error=abs(imbalance[-1]+imbalance[0])
        assert max(worst_unitary,worst_det,adjoint_error,reversal_error,sign_error)<1e-8
        assert smallest_singular>0 and min(imbalance)<=0<=max(imbalance)
        records.append({'dimension':dimension,'seed':seed,'alpha':alpha,
                        'sampled_beta_count':len(beta_values),'min_sampled_block_singular_value':smallest_singular,
                        'worst_unitarity_error':worst_unitary,'worst_determinant_phase_error':worst_det,
                        'adjoint_endpoint_error':adjoint_error,'normalized_reversal_error':reversal_error,
                        'walsh_endpoint_values':[imbalance[0],imbalance[-1]],'all_checks_pass':True})
out={'scope':'Independent floating-point sanity checks of generic block invertibility, actual polar path, determinant phase, normalized-lift endpoint reversal and Walsh sign change. Not a proof or Lean replay; no circuit bound is tested.',
     'entrant_code_executed':False,'cases':records,'all_pass':True}
path=HERE/'matt_polar_path_sanity_check.json'
path.write_text(json.dumps(out,indent=2),encoding='utf8')
print(json.dumps({'cases':len(records),'dimensions':[4,8,12],'all_pass':True,
                  'largest_error':max(max(x['worst_unitarity_error'],x['worst_determinant_phase_error'],x['normalized_reversal_error']) for x in records)},indent=2))
