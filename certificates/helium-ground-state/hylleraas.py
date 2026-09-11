"""Exact Hylleraas polynomial algebra and moments for infinite-mass helium.

No floating-point arithmetic is used in this module.  Common angular factor
8*pi**2 is omitted from every integral, and cancels in normalized quotients.
Moment values are represented exactly in Q + Q*log(2) + Q*pi**2.
See THEORY.md for the change of variables and endpoint-safe recurrence proof.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial

ZERO = (F(0), F(0), F(0))

def add(x, y):
    return tuple(a+b for a,b in zip(x,y))

def scale(x, c):
    return tuple(a*c for a in x)

def rational(x):
    assert x[1] == x[2] == 0, x
    return x[0]

@lru_cache(None)
def angular_B(n, c):
    assert n >= 0 and n % 2 == 0 and c >= -1
    if c == -1:
        return (-sum((F(1,(2*l+1)**2) for l in range(n//2)),F(0)), F(0),F(1,8))
    q = c+1
    h = q//2
    a = sum((F(1,n+2*l+1) for l in range(h)),F(0))
    if q % 2 == 0:
        return (a/q,F(0),F(0))
    m = n+2*h
    a -= sum((F(1,(2*l+1)*(2*l+2)) for l in range(m//2)),F(0))
    return (a/q,F(1,q),F(0))

@lru_cache(None)
def moment(a,b,c,kappa):
    """Integral exp(-kappa*(r+s))*r^a*s^b*u^c over the triangle."""
    assert min(a,b,c) >= -1 and a+b+c > -3 and kappa > 0, (a,b,c)
    if a > b:
        return moment(b,a,c,kappa)
    if a == -1:
        angular = ZERO
        m = b
        for j in range((m+1)//2+1):
            angular=add(angular,scale(angular_B(2*j,c),2*comb(m+1,2*j)))
    else:
        poly = [0]*(a+b+1)
        for i in range(a+1):
            for j in range(b+1):
                poly[i+j] += comb(a,i)*comb(b,j)*((-1)**j+(-1)**i)
        if c == -1:
            angular=(sum((F(w,(n+1)**2) for n,w in enumerate(poly)),F(0)),F(0),F(0))
        else:
            angular=(sum((F(w,(n+1)*(n+c+2)) for n,w in enumerate(poly)),F(0)),F(0),F(0))
    radial = F(2)**(-a-b-1)*factorial(a+b+c+2)/kappa**(a+b+c+3)
    return scale(angular,radial)

def accumulate(out, exponents, coefficient):
    if coefficient:
        out[exponents]=out.get(exponents,F(0))+coefficient
        if not out[exponents]: del out[exponents]

def derivative(poly,index):
    out={}
    for e,c in poly.items():
        if e[index]:
            t=list(e);t[index]-=1
            accumulate(out,tuple(t),c*e[index])
    return out

def add_shift(out,poly,shift=(0,0,0),factor=F(1)):
    for e,c in poly.items():
        accumulate(out,tuple(x+y for x,y in zip(e,shift)),c*factor)

def h_action(poly,alpha=F(2),Z=F(2)):
    """Returns e^(alpha(r+s)) H[e^(-alpha(r+s))*poly] as Laurent polynomial."""
    out={}
    dr,ds,du=(derivative(poly,i) for i in range(3))
    add_shift(out,derivative(dr,0),factor=-F(1,2))
    add_shift(out,derivative(ds,1),factor=-F(1,2))
    add_shift(out,derivative(du,2),factor=-F(1))
    add_shift(out,dr,factor=alpha);add_shift(out,ds,factor=alpha)
    add_shift(out,dr,(-1,0,0),-F(1));add_shift(out,ds,(0,-1,0),-F(1))
    add_shift(out,du,(0,0,-1),-F(2))
    # C_r=(r^2+u^2-s^2)/(r*u), C_s=(s^2+u^2-r^2)/(s*u).
    Cr=[((1,0,-1),1),((-1,0,1),1),((-1,2,-1),-1)]
    Cs=[((0,1,-1),1),((0,-1,1),1),((2,-1,-1),-1)]
    for factors,first in [(Cr,dr),(Cs,ds)]:
        cross=derivative(first,2)
        for shift,sign in factors:
            add_shift(out,cross,shift,-F(sign,2))
            add_shift(out,du,shift,alpha*F(sign,2))
    add_shift(out,poly,factor=-alpha**2)
    add_shift(out,poly,(-1,0,0),alpha-Z)
    add_shift(out,poly,(0,-1,0),alpha-Z)
    add_shift(out,poly,(0,0,-1),F(1))
    return out

def polynomial_product(a,b):
    out={}
    for e,c in a.items():
        for f,d in b.items():
            accumulate(out,tuple(i+j for i,j in zip(e,f)),c*d)
    return out

def integrate(poly,kappa):
    out=ZERO
    for (i,j,k),c in poly.items():
        out=add(out,scale(moment(i+1,j+1,k+1,kappa),c))
    return out

def inner(a,b,kappa):
    return integrate(polynomial_product(a,b),kappa)

def basis(order):
    """Symmetric r^i*s^j*u^k, i>=j>=0, i+j+k<=order, divided by degree!."""
    out=[]
    for degree in range(order+1):
        for k in range(degree+1):
            for j in range((degree-k)//2+1):
                i=degree-k-j
                coefficient=F(1,factorial(degree))
                terms={(i,j,k):coefficient}
                if i!=j: terms[(j,i,k)]=coefficient
                out.append(((i,j,k),terms))
    return out

def assemble(order,alpha=F(2),Z=F(2)):
    entries=basis(order)
    polys=[p for _,p in entries]
    hs=[h_action(p,alpha,Z) for p in polys]
    d=len(polys)
    S=[[F(0)]*d for _ in range(d)]
    H=[[F(0)]*d for _ in range(d)]
    for i in range(d):
        for j in range(i+1):
            S[i][j]=S[j][i]=rational(inner(polys[i],polys[j],2*alpha))
            h1=rational(inner(polys[i],hs[j],2*alpha))
            h2=rational(inner(hs[i],polys[j],2*alpha))
            assert h1==h2,(i,j,h1,h2)
            H[i][j]=H[j][i]=h1
    return entries,S,H

def combine(entries,coeffs):
    out={}
    for (_,p),c in zip(entries,coeffs): add_shift(out,p,factor=c)
    return out
