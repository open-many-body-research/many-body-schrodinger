"""A/E decision experiment. Decimal selection; separate exact interval audit.

No published energy enters selection, acceptance, or certification.
The fixed shift is -5; the regularized objective is (Q+10H+25S+tau I)/S.
Each dictionary has exact rational power-of-two diagonal scaling.
"""
import argparse
from decimal import Decimal as D, localcontext
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import platform
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE.parent / 'helium-ground-state'))
from hylleraas import basis, h_action, inner, rational, scale, add
from check_trial import log2_bounds, reject_float
from certified_interval import Interval, pi, set_precision

SIGMA = F(-5)
TAU = F(1, 2**160)
ADDITIVE = F(1, 10**16)

def dec(q):
    return D(q.numerator) / D(q.denominator)

def dump(path, data):
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(data, indent=2) + '\n')
    tmp.replace(path)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def code_hashes():
    return {str(p.relative_to(ROOT)): sha(p) for p in
            (Path(__file__), HERE.parent/'helium-ground-state/hylleraas.py',
             HERE.parent/'helium-ground-state/check_trial.py', HERE.parent/'helium-ground-state/certified_interval.py')}

def dictionary(candidate, n):
    entries = []
    js = range(n//2+1) if candidate == 'E' else range(1)
    for j in js:
        alpha = F(2 * 2**j)
        order = n-2*j
        for index, polynomial in basis(order):
            norm = rational(inner(polynomial, polynomial, 2*alpha))
            coefficient = F(1)
            while norm*coefficient**2 < F(1,2):
                coefficient *= 2
            while norm*coefficient**2 > 2:
                coefficient /= 2
            polynomial = {key: val*coefficient for key,val in polynomial.items()}
            entries.append((alpha, index, coefficient, polynomial))
    return entries

def matrices(candidate, n):
    path = HERE/f'matrices_{candidate}_{n}.json'
    if path.exists():
        data = json.loads(path.read_text(), parse_float=reject_float)
        return data, [[[F(t) for t in cell] for cell in row]
                      for row in data['Q']], [[F(t) for t in row] for row in data['S']], [[F(t) for t in row] for row in data['H']]
    started = time.monotonic()
    entries = dictionary(candidate, n)
    dimension = len(entries)
    S = [[F(0)]*dimension for _ in entries]
    H = [[F(0)]*dimension for _ in entries]
    Q = [[None]*dimension for _ in entries]
    actions = [h_action(p, alpha, F(2)) for alpha,_,_,p in entries]
    for i, (alpha,_,_,p) in enumerate(entries):
        for j in range(i+1):
            beta,_,_,r = entries[j]
            kappa = alpha+beta
            S[i][j] = S[j][i] = rational(inner(p,r,kappa))
            Hij = rational(inner(p, actions[j], kappa))
            assert Hij == rational(inner(actions[i],r,kappa))
            H[i][j] = H[j][i] = Hij
            Q[i][j] = Q[j][i] = inner(actions[i], actions[j], kappa)
        if i % 10 == 0:
            print('moment row',candidate,n,i+1,dimension,flush=True)
    data = {'candidate':candidate,'n':n,'dimension':dimension,
            'definition':'A: degree<=n at exponent2; E: exponent 2*2^j and degree<=n-2j, 0<=j<=floor(n/2)',
            'entries':[{'alpha':str(a),'index':list(e),'rational_scale':str(c)} for a,e,c,_ in entries],
            'S':[[str(x) for x in row] for row in S],
            'H':[[str(x) for x in row] for row in H],
            'Q':[[[str(x) for x in cell] for cell in row] for row in Q],
            'field':'Q + Q log2 + Q pi^2','Z':'2',
            'code_sha256':code_hashes(),
            'moment_seconds_metadata':str(time.monotonic()-started)}
    dump(path,data)
    return data,Q,S,H

def matvec(A,x):
    return [sum((a*b for a,b in zip(row,x)),D(0)) for row in A]

def quad(A,x):
    return sum((a*b for a,b in zip(x,matvec(A,x))),D(0))

def ldl(A):
    n=len(A); L=[[D(0)]*n for _ in A]; pivots=[]
    for i in range(n):
        L[i][i]=D(1)
        for j in range(i):
            L[i][j]=(A[i][j]-sum((L[i][k]*pivots[k]*L[j][k] for k in range(j)),D(0)))/pivots[j]
        pivot=A[i][i]-sum((L[i][k]**2*pivots[k] for k in range(i)),D(0))
        if pivot<=0:
            raise ArithmeticError(('nonpositive Decimal pivot',i,str(pivot)))
        pivots.append(pivot)
    return L,pivots

def solve(L,pivots,rhs):
    n=len(rhs); y=[]
    for i in range(n):
        y.append(rhs[i]-sum((L[i][j]*y[j] for j in range(i)),D(0)))
    y=[y[i]/pivots[i] for i in range(n)]
    for i in reversed(range(n)):
        y[i]-=sum((L[j][i]*y[j] for j in range(i+1,n)),D(0))
    return y

def screen(candidate,n,precision=80,iterations=160):
    started=time.monotonic()
    data,Q,S,H=matrices(candidate,n)
    dim=len(S)
    with localcontext() as ctx:
        ctx.prec=precision
        ln=log2_bounds(precision*4)
        l2=dec(sum(ln,F(0))/2)
        pc=pi(bits=precision*4)
        p2=dec(pc.midpoint)**2
        sd=[[dec(x) for x in row] for row in S]
        hd=[[dec(x) for x in row] for row in H]
        qd=[[dec(x[0])+dec(x[1])*l2+dec(x[2])*p2 for x in row] for row in Q]
        wd=[[qd[i][j]+10*hd[i][j]+25*sd[i][j]+(dec(TAU) if i==j else D(0)) for j in range(dim)] for i in range(dim)]
        L,pivots=ldl(wd)
        _,spivots=ldl(sd)
        v=[D(1)]+[D(0)]*(dim-1)
        previous=None
        for iteration in range(iterations):
            v=solve(L,pivots,matvec(sd,v))
            vmax=max(abs(x) for x in v)
            v=[x/vmax for x in v]
            objective=quad(wd,v)/quad(sd,v)
            change=abs(objective-previous) if previous is not None else None
            previous=objective
        norm=quad(sd,v)
        mean=quad(hd,v)/norm
        variance=quad(qd,v)/norm-mean**2
        physical=objective-dec(TAU)*sum((x*x for x in v),D(0))/norm
        residualvec=[x-objective*y for x,y in zip(matvec(wd,v),matvec(sd,v))]
        residualmax=max(abs(x) for x in residualvec)
        coeffs=[str(F(str(x))) for x in v]
        result={'status':'EMPIRICAL','candidate':candidate,'n':n,'m_n':dim,
                'sigma':str(SIGMA),'regularization_tau':str(TAU),'additive_target':str(ADDITIVE),
                'coefficients':coeffs,'basis_matrix_file':f'matrices_{candidate}_{n}.json',
                'matrix_sha256':sha(HERE/f'matrices_{candidate}_{n}.json'),
                'shifted_regularized_objective':str(objective),
                'shifted_physical_objective':str(physical),'mean':str(mean),
                'variance':str(variance),'rayleigh_residual':str(variance.sqrt()),
                'temple_width':str(variance/(D('-2.5')-mean)),
                'acceptance_mean_le_minus_11_over_4':mean<=D('-2.75'),
                'last_objective_change':str(change),'pencil_residual_max':str(residualmax),
                'S_smallest_LDL_pivot':str(min(spivots)),
                'W_smallest_LDL_pivot':str(min(pivots)),
                'pivot_ratio_proxy_not_condition_number':str(max(spivots)/min(spivots)),
                'precision_decimal_digits':precision,'iterations':iterations,
                'coefficient_max_bit_height':max(max(abs(F(c).numerator).bit_length(),F(c).denominator.bit_length()) for c in coeffs),
                'alpha_max_bit_height':max(F(e['alpha']).numerator.bit_length() for e in data['entries']),
                'runtime':{'python':platform.python_version(),'machine':platform.machine()},
                'wall_seconds_metadata':str(time.monotonic()-started),'code_sha256':code_hashes()}
    dump(HERE/f'screen_{candidate}_{n}.json',result)
    print(json.dumps({k:result[k] for k in ('candidate','n','m_n','mean','temple_width','shifted_regularized_objective','pencil_residual_max','wall_seconds_metadata')}),flush=True)
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('candidate',choices=['A','E'])
    parser.add_argument('orders',nargs='+',type=int)
    parser.add_argument('--precision',type=int,default=80)
    parser.add_argument('--iterations',type=int,default=160)
    args=parser.parse_args()
    for n in args.orders:
        screen(args.candidate,n,args.precision,args.iterations)
