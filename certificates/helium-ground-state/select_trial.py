"""Candidate selection ONLY: decimal inverse iteration, followed by rational output.

This is deliberately outside the certificate.  check_trial.py treats its output
as arbitrary rational trial coefficients and independently certifies the result.
"""
import argparse,json,time
from decimal import Decimal as D,localcontext
from fractions import Fraction as F
from pathlib import Path
from hylleraas import assemble

def dec(f): return D(f.numerator)/D(f.denominator)

def matvec(A,v): return [sum((a*b for a,b in zip(row,v)),D(0)) for row in A]

def select(order,precision,iterations):
    started=time.monotonic()
    entries,S,H=assemble(order)
    n=len(entries)
    print('assembled',order,n,'seconds',time.monotonic()-started,flush=True)
    with localcontext() as ctx:
        ctx.prec=precision
        ds=[dec(S[i][i]).sqrt() for i in range(n)]
        sm=[[dec(S[i][j])/(ds[i]*ds[j]) for j in range(n)] for i in range(n)]
        hm=[[dec(H[i][j])/(ds[i]*ds[j]) for j in range(n)] for i in range(n)]
        shift=D('-2.91')
        A=[[hm[i][j]-shift*sm[i][j] for j in range(n)] for i in range(n)]
        # LDL^T factorization is used only for selecting a candidate.
        L=[[D(0)]*n for _ in range(n)];diagonal=[D(0)]*n
        for i in range(n):
            L[i][i]=D(1)
            for j in range(i):
                L[i][j]=(A[i][j]-sum((L[i][k]*diagonal[k]*L[j][k] for k in range(j)),D(0)))/diagonal[j]
            diagonal[i]=A[i][i]-sum((L[i][k]**2*diagonal[k] for k in range(i)),D(0))
            if diagonal[i]<=0: raise ArithmeticError(('nonpositive candidate pivot',i,diagonal[i]))
        v=[D(1)]+[D(0)]*(n-1)
        for iteration in range(iterations):
            rhs=matvec(sm,v)
            y=[]
            for i in range(n): y.append(rhs[i]-sum((L[i][j]*y[j] for j in range(i)),D(0)))
            y=[y[i]/diagonal[i] for i in range(n)]
            for i in reversed(range(n)): y[i]-=sum((L[j][i]*y[j] for j in range(i+1,n)),D(0))
            size=max(abs(x) for x in y)
            v=[x/size for x in y]
        hv=matvec(hm,v);sv=matvec(sm,v)
        mean=sum((x*y for x,y in zip(v,hv)),D(0))/sum((x*y for x,y in zip(v,sv)),D(0))
        coefficients=[v[i]/ds[i] for i in range(n)]
        coefficients=[c/coefficients[0] for c in coefficients]
        rational_coefficients=[F(str(c)) for c in coefficients]
        data={'order':order,'dimension':n,'alpha':'2','Z':'2','basis':'symmetric r^i s^j u^k / (i+j+k)!; i>=j',
              'indices':[list(e) for e,_ in entries],
              'coefficients':[str(c) for c in rational_coefficients],
              'candidate_decimal_precision':precision,'candidate_iterations':iterations,
              'candidate_mean_display':str(mean),'candidate_seconds':str(time.monotonic()-started)}
    dest=Path(__file__).parent/f'trial_{order}.json'
    dest.write_text(json.dumps(data,indent=2)+'\n')
    print('candidate mean',mean,'seconds',time.monotonic()-started,'output',dest,flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('order',type=int);p.add_argument('--precision',type=int,default=90);p.add_argument('--iterations',type=int,default=8)
    a=p.parse_args();select(a.order,a.precision,a.iterations)
