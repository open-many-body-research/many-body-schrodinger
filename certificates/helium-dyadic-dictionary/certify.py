"""Rational/interval certificate and independent contraction audit for A/E.

The certified moments are recomputed by grouped polynomial H-actions, while the
finite pencil is supplied by pairwise matrices. Equality of the exact symbolic
quadratic forms is asserted before the interval certificate is emitted.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
import platform
import time
from pathlib import Path

from run import HERE, ROOT, TAU, ADDITIVE, dictionary, matrices, dump, sha, code_hashes
from hylleraas import add_shift, h_action, inner, rational, add, scale, ZERO
from check_trial import log2_bounds, outward_decimal, reject_float
from certified_interval import Interval, pi, set_precision
from fixed_shift import certify_additive


def exact_bilinear(A,c,field=False):
    value=ZERO if field else F(0)
    for i in range(len(c)):
        for j in range(i+1):
            coeff=c[i]*c[j]*(1 if i==j else 2)
            value=add(value,scale(A[i][j],coeff)) if field else value+coeff*A[i][j]
    return value


def direct_grouped(entries,c):
    grouped={}
    for (alpha,index,scaling,poly),coefficient in zip(entries,c):
        add_shift(grouped.setdefault(alpha,{}),poly,factor=coefficient)
    actions={alpha:h_action(poly,alpha,F(2)) for alpha,poly in grouped.items()}
    norm=F(0); numerator=F(0); second=ZERO
    for a,p in grouped.items():
        for b,q in grouped.items():
            norm+=rational(inner(p,q,a+b))
            numerator+=rational(inner(p,actions[b],a+b))
            second=add(second,inner(actions[a],actions[b],a+b))
    return norm,numerator,second


def certify(candidate,n,bits=512):
    started=time.monotonic()
    set_precision(bits)
    trialpath=HERE/f'screen_{candidate}_{n}.json'
    trial=json.loads(trialpath.read_text(),parse_float=reject_float)
    data,Q,S,H=matrices(candidate,n)
    assert trial['matrix_sha256']==sha(HERE/f'matrices_{candidate}_{n}.json')
    assert F(trial['sigma'])==-5 and F(trial['regularization_tau'])==TAU
    c=[F(x) for x in trial['coefficients']]
    entries=dictionary(candidate,n)
    assert len(c)==len(entries)==len(S)
    norm=exact_bilinear(S,c); numerator=exact_bilinear(H,c)
    second=exact_bilinear(Q,c,True)
    direct=direct_grouped(entries,c)
    assert direct==(norm,numerator,second), 'pairwise/grouped exact audit mismatch'
    print('exact grouped/pairwise moment audit passed',candidate,n,flush=True)
    assert norm>0
    mean=numerator/norm
    assert mean<=-F(11,4), 'strict acceptance filter failed'
    lnlo,lnhi=log2_bounds(bits)
    ln=Interval(lnlo,lnhi,bits=bits)
    pp=pi(bits=bits).square()
    def evaluate(expr):
        return Interval(expr[0],bits=bits)+expr[1]*ln+expr[2]*pp
    variance_expression=add(scale(second,1/norm),(-mean**2,F(0),F(0)))
    variance=evaluate(variance_expression)
    vlo=max(F(0),variance.lo); vhi=variance.hi
    assert vhi>=vlo
    beta=-F(5,2)
    lowerraw=mean-vhi/(beta-mean)
    ell=outward_decimal(lowerraw,24)
    upper=outward_decimal(mean,24,True)
    width=upper-ell
    # E is enclosed by this very certificate; no external energy is an input.
    graph_squared=[vlo,vhi+(mean-ell)**2]
    shifted_expression=add(scale(second,1/norm),(10*mean+25,F(0),F(0)))
    shifted=evaluate(shifted_expression)
    assert ell+5>0
    shifted_excess=[max(F(0),shifted.lo-(upper+5)**2),shifted.hi-(ell+5)**2]
    SI=[[Interval(q,bits=bits) for q in row] for row in S]
    WI=[[evaluate(Q[i][j])+10*H[i][j]+25*S[i][j]+(TAU if i==j else 0)
         for j in range(len(S))] for i in range(len(S))]
    def progress(i,pivot):
        if i%10==0:
            print('interval LDL row',candidate,n,i+1,len(S),flush=True)
    additive=certify_additive(SI,WI,c,ADDITIVE,progress)
    result={'status':'PROVEN (this session): rational interval arithmetic, existing paper continuum proof',
            'candidate':candidate,'n':n,'m_n':len(c),'Z':'2','sigma':'-5',
            'regularization_tau':str(TAU),'trial_sha256':sha(trialpath),
            'matrix_sha256':sha(HERE/f'matrices_{candidate}_{n}.json'),
            'exact_grouped_vs_pairwise_moment_audit':True,
            'mean':str(mean),'norm_without_common_8pi2':str(norm),
            'H_squared_numerator_Q_log2_pi2':[str(x) for x in second],
            'variance_expression_Q_log2_pi2':[str(x) for x in variance_expression],
            'variance_interval':[str(vlo),str(vhi)],
            'spectral_separator':str(beta),'separator_minus_mean':str(beta-mean),
            'acceptance_mean_le_minus_11_over_4':True,
            'ell':str(ell),'u':str(upper),'width':str(width),
            'graph_residual_squared_interval':[str(x) for x in graph_squared],
            'shifted_objective_interval':[str(shifted.lo),str(shifted.hi)],
            'shifted_objective_excess_interval':[str(x) for x in shifted_excess],
            'finite_pencil_additive_certificate':additive,
            'runtime':{'python':platform.python_version(),'machine':platform.machine()},
            'interval_settings':{'fractional_bits':bits,'rounding':'every operation outward dyadic',
              'log2_remainder':'9/[4(2b+1)3^(2b+1)], b=bits',
              'pi_remainder':'Machin arctangent alternating next-term bounds'},
            'code_sha256':dict(code_hashes(),**{str(p.relative_to(ROOT)):sha(p) for p in
                                               (Path(__file__),HERE/'fixed_shift.py')}),
            'wall_seconds_metadata':str(time.monotonic()-started)}
    path=HERE/f'certificate_{candidate}_{n}_{bits}.json'
    dump(path,result)
    path.with_suffix('.json.sha256').write_text(sha(path)+'  '+path.name+'\n')
    print('certificate',candidate,n,'width',str(width),'seconds',str(time.monotonic()-started),flush=True)
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('candidate',choices=['A','E'])
    parser.add_argument('orders',nargs='+',type=int)
    parser.add_argument('--bits',type=int,default=512)
    args=parser.parse_args()
    for n in args.orders:
        certify(args.candidate,n,args.bits)
