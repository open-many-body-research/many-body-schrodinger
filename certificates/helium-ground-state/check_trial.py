"""Rational/interval verification of an arbitrary supplied helium trial state.

Candidate selection, eigenvalue fitting, and the published reference are not
trusted.  Norm, Rayleigh mean, full continuum residual, and Temple interval are
recomputed from the supplied rational coefficients.  No floating-point value
enters any certificate inequality.
"""
import argparse,hashlib,json,sys,time
from fractions import Fraction as F
from pathlib import Path
from hylleraas import basis,combine,h_action,inner,rational,scale,add

sys.path.insert(0,str(Path(__file__).resolve().parent))
from certified_interval import Interval,pi,set_precision

def log2_bounds(terms):
    partial=2*sum((F(1,(2*n+1)*3**(2*n+1)) for n in range(terms)),F(0))
    tail=F(9,4*(2*terms+1)*3**(2*terms+1))
    return partial,partial+tail

def reject_float(value):
    raise TypeError('JSON floating-point numbers are forbidden in a trial certificate input')

def exact_fraction(value):
    if type(value) not in (str,int):
        raise TypeError('exact trial parameters must be rational strings or integers')
    return F(value)

def evaluate(expression,bits):
    l,u=log2_bounds(bits)
    ln2=Interval(l,u,bits=bits)
    pic=pi()
    return Interval(expression[0],bits=bits)+expression[1]*ln2+expression[2]*pic*pic

def outward_decimal(q,places,upper=False):
    power=10**places
    v=q*power
    rounded=-((-v.numerator)//v.denominator) if upper else v.numerator//v.denominator
    return F(rounded,power)

def decimal_exact(q,places):
    assert (q*10**places).denominator==1
    n=int(q*10**places)
    return ('-' if n<0 else '')+str(abs(n)//10**places)+'.'+str(abs(n)%10**places).zfill(places)

def check(path,bits=512):
    set_precision(bits)
    started=time.monotonic()
    trial_bytes=path.read_bytes()
    data=json.loads(trial_bytes,parse_float=reject_float)
    order=data['order'];alpha=exact_fraction(data['alpha']);Z=exact_fraction(data['Z'])
    assert type(order) is int and order>=0
    assert Z==2 and alpha>0
    entries=basis(order)
    assert [list(e) for e,_ in entries]==data['indices']
    coeffs=[exact_fraction(c) for c in data['coefficients']]
    assert len(coeffs)==len(entries)
    p=combine(entries,coeffs)
    hp=h_action(p,alpha,Z)
    norm=rational(inner(p,p,2*alpha))
    numerator=rational(inner(p,hp,2*alpha))
    assert norm>0
    mean=numerator/norm
    h2=inner(hp,hp,2*alpha)
    variance_expression=add(scale(h2,1/norm),(-mean**2,F(0),F(0)))
    variance=evaluate(variance_expression,bits)
    variance_lo=max(F(0),variance.lo)
    variance_hi=variance.hi
    assert variance_hi>=variance_lo
    beta=-F(5,2)
    assert mean<beta
    lower_raw=mean-variance_hi/(beta-mean)
    lower=outward_decimal(lower_raw,12)
    upper=outward_decimal(mean,12,True)
    assert lower<=lower_raw<=mean<=upper
    # Reference is for comparison only; it appears nowhere in the bound above.
    reference=F('-2.9037243770341195983111592451944044466969253105')
    certificate={
        'status':'CERTIFIED by rational arithmetic plus paper continuum proof',
        'trial_file':path.name,'order':order,'dimension':len(entries),
        'trial_sha256':hashlib.sha256(trial_bytes).hexdigest(),
        'alpha':str(alpha),'Z':str(Z),'interval_bits':bits,
        'norm_without_common_8pi2':str(norm),
        'energy_numerator_without_common_8pi2':str(numerator),
        'mean':str(mean),
        'h2_without_common_8pi2_Q_log2_pi2':[str(c) for c in h2],
        'variance_Q_log2_pi2':[str(c) for c in variance_expression],
        'variance_interval':[str(variance_lo),str(variance_hi)],
        'spectral_separator':str(beta),'separator_minus_mean':str(beta-mean),
        'temple_lower_raw':str(lower_raw),
        'ell':str(lower),'u':str(upper),'width':str(upper-lower),
        'ell_decimal':decimal_exact(lower,12),'u_decimal':decimal_exact(upper,12),
        'width_decimal':decimal_exact(upper-lower,12),
        'width_at_most_1e_minus_6':upper-lower<=F(1,10**6),
        'published_reference_not_used_for_certification':str(reference),
        'reference_source':'Schwartz math-ph/0605018 p.3 extrapolation, numerical not certified',
        'mean_minus_reference':str(mean-reference),
    }
    output=path.parent/f'certificate_{order}_{bits}.json'
    output.write_text(json.dumps(certificate,indent=2)+'\n')
    print(json.dumps({k:certificate[k] for k in ['order','dimension','ell_decimal','u_decimal','width_decimal','width_at_most_1e_minus_6']},indent=2),flush=True)
    print('verification wall seconds (log only):',time.monotonic()-started,flush=True)
    return certificate

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('trial',type=Path);p.add_argument('--bits',type=int,default=512)
    a=p.parse_args();check(a.trial,a.bits)
