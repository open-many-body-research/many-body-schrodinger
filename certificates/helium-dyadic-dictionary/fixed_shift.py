"""Reusable finite-pencil selection and directed-rounding additive audit.

select_decimal accepts Decimal matrices in the caller's current precision.
certify_additive accepts symmetric Interval matrices and rational coefficients.
The continuum domain and moment formula proofs are obligations of each caller.
"""
from decimal import Decimal as D
from fractions import Fraction as F
from run import ldl, matvec, quad, solve
from certified_interval import Interval


def select_decimal(S,H,Q,tau,iterations=160):
    """EMPIRICAL fixed shift -5; no physical energy value or spectral fitting."""
    dimension=len(S)
    W=[[Q[i][j]+10*H[i][j]+25*S[i][j]+(tau if i==j else D(0))
        for j in range(dimension)] for i in range(dimension)]
    L,pivots=ldl(W)
    _,spivots=ldl(S)
    c=[D(1)]+[D(0)]*(dimension-1)
    old=None
    for _ in range(iterations):
        c=solve(L,pivots,matvec(S,c))
        vmax=max(abs(x) for x in c)
        c=[x/vmax for x in c]
        objective=quad(W,c)/quad(S,c)
        change=abs(objective-old) if old is not None else None
        old=objective
    norm=quad(S,c)
    mean=quad(H,c)/norm
    variance=quad(Q,c)/norm-mean**2
    return dict(coefficients=c,norm=norm,mean=mean,variance=variance,
                shifted_regularized_objective=objective,
                last_objective_change=change,
                S_smallest_LDL_pivot=min(spivots),
                W_smallest_LDL_pivot=min(pivots),
                pivot_ratio_proxy_not_condition_number=max(spivots)/min(spivots),
                pencil_residual_max=max(abs(x-objective*y)
                    for x,y in zip(matvec(W,c),matvec(S,c))))


def interval_quadratic(A,c):
    bits=A[0][0].bits
    value=Interval(0,bits=bits)
    for i in range(len(c)):
        value+=c[i]**2*A[i][i]
        for j in range(i):
            value+=2*c[i]*c[j]*A[i][j]
    return value


def interval_ldl_positive(A,progress=None):
    """Enclose LDL recurrence; strictly positive pivots prove A positive definite.

    By induction each exact pivot/entry lies in its returned interval, and every
    division uses a strictly positive exact pivot. This is also valid when A's
    input entries are independent interval enclosures, because it proves the
    recurrence for every consistent point symmetric matrix in the input box.
    """
    n=len(A); bits=A[0][0].bits
    L=[[Interval(0,bits=bits) for _ in A] for _ in A]
    pivots=[]
    for i in range(n):
        L[i][i]=Interval(1,bits=bits)
        for j in range(i):
            total=Interval(0,bits=bits)
            for k in range(j):
                total+=L[i][k]*pivots[k]*L[j][k]
            L[i][j]=(A[i][j]-total)/pivots[j]
        total=Interval(0,bits=bits)
        for k in range(i):
            total+=L[i][k].square()*pivots[k]
        pivot=A[i][i]-total
        if pivot.lo<=0:
            raise ArithmeticError(('interval pivot positivity failed',i,str(pivot.lo),str(pivot.hi)))
        pivots.append(pivot)
        if progress is not None:
            progress(i,pivot)
    return pivots


def certify_additive(S,W,c,delta,progress=None):
    """Prove trial quotient ≤ generalized λ_min(W,S)+delta.

    S must be the Gram matrix of a linearly independent dictionary (or itself
    separately certified positive definite). This routine checks S via LDL too.
    It asserts all tolerance comparisons as exact Fraction comparisons.
    """
    if not isinstance(delta,F) or delta<=0:
        raise ValueError('delta must be a positive exact Fraction')
    norm=interval_quadratic(S,c)
    if norm.lo<=0:
        raise ArithmeticError('trial normalization not certified positive')
    quotient=interval_quadratic(W,c)/norm
    lower=quotient.lo-delta/2
    actualgap=quotient.hi-lower
    assert actualgap<=delta, ('insufficient interval precision',str(actualgap),str(delta))
    spivots=interval_ldl_positive(S)
    shifted=[[W[i][j]-lower*S[i][j] for j in range(len(S))] for i in range(len(S))]
    pivots=interval_ldl_positive(shifted,progress=progress)
    return {'trial_norm_interval':[str(norm.lo),str(norm.hi)],
            'trial_regularized_objective_interval':[str(quotient.lo),str(quotient.hi)],
            'generalized_minimum_lower':str(lower),
            'additive_tolerance':str(delta),'proved_additive_gap':str(actualgap),
            'S_LDL_pivot_intervals':[[str(p.lo),str(p.hi)] for p in spivots],
            'W_minus_lower_S_LDL_pivot_intervals':[[str(p.lo),str(p.hi)] for p in pivots],
            'proof':'Outward interval LDL: S positive definite and W-lower*S positive definite.'}
