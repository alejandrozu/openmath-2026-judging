"""Exact symbolic checks of the ordinary quartic appendix, independent of Lean."""
from pathlib import Path
import json
from fractions import Fraction

# A small exact Laurent-polynomial implementation avoids optional packages.
class Poly:
    def __init__(self, terms):
        if not isinstance(terms, dict):
            terms={(0,)*7:Fraction(terms)}
        self.terms={k:Fraction(v) for k,v in terms.items() if v}
    def __add__(self, other):
        other=poly(other); out=dict(self.terms)
        for k,v in other.terms.items():out[k]=out.get(k,0)+v
        return Poly(out)
    __radd__=__add__
    def __neg__(self):return Poly({k:-v for k,v in self.terms.items()})
    def __sub__(self,other):return self+-poly(other)
    def __rsub__(self,other):return poly(other)+-self
    def __mul__(self,other):
        out={}
        for k,v in self.terms.items():
            for l,w in poly(other).terms.items():
                m=tuple(x+y for x,y in zip(k,l));out[m]=out.get(m,0)+v*w
        return Poly(out)
    __rmul__=__mul__
    def __truediv__(self,other):
        other=poly(other);assert len(other.terms)==1
        k,v=next(iter(other.terms.items()))
        return self*Poly({tuple(-x for x in k):1/v})
    def __pow__(self,n):
        if n<0:
            assert len(self.terms)==1
            k,v=next(iter(self.terms.items()))
            return Poly({tuple(x*n for x in k):v**n})
        out=Poly(1)
        for _ in range(n):out=out*self
        return out
    def __eq__(self,other):return self.terms==poly(other).terms
    def __hash__(self):return hash(tuple(sorted(self.terms.items())))
    def subs(self,replacements):
        out=Poly(0)
        for k,v in self.terms.items():
            term=Poly(v)
            for i,power in enumerate(k):
                variable=Poly({tuple(int(j==i) for j in range(7)):1})
                term*=replacements.get(variable,variable)**power
            out+=term
        return out
def poly(x):return x if isinstance(x,Poly) else Poly(x)
class Exact:
    def symbols(self,names,**kwargs):
        return tuple(Poly({tuple(int(j==i) for j in range(7)):1}) for i,_ in enumerate(names.split()))
    def chebyshevt(self,n,x):
        if n==0:return Poly(1)
        if n==1:return x
        return 2*x*self.chebyshevt(n-1,x)-self.chebyshevt(n-2,x)
    def cancel(self,x):return x
    Rational=staticmethod(Fraction)
sp=Exact()

r,s,c,a,b,d,e=sp.symbols('r s c a b d e', real=True)
q=1+4*r-s*r**2+4*r**3+r**4
A1=4*r-2*s*r**2+12*r**3+4*r**4
A2=4*r-4*s*r**2+36*r**3+16*r**4
P=1-s*r+(9-s)*r**2+20*r**3+(9-s)*r**4-s*r**5+r**6
coeff=[1,4,-s,4,1]
norm=sum(coeff[i]**2*r**(2*i) for i in range(5))+2*sum(
    coeff[i]*coeff[j]*r**(i+j)*sp.chebyshevt(j-i,c)
    for i in range(5) for j in range(i+1,5))
F=8+16*a+4*a**2+d
K=2+2*a+b+2*a*(a+2)*b
J=2*(a**2*(4*a+12-2*b)+4*a*((b-1)**2+1)+b**2*(2+b))
T=8*r-4*s*r**2*(1+c)+8*r**3*(2*c+1)**2+16*r**4*c**2*(1+c)-8*s*r**3+64*r**4*(1+c)+8*r**5*(2*c+1)**2-8*s*r**5-4*s*r**6*(1+c)+8*r**7
E=8*r-16*r**2-16*r**3-16*r**5-16*r**6
subs={a:(1-r)**2/(2*r),b:1+c,d:2-s}
checks={
    'variance_numerator':q*A2-A1**2-4*r*P,
    'radius_F':q-r**2*F.subs(subs),
    'boundary_squared_modulus':q**2-norm-8*r**4*((2-b)*(J+d*K)).subs(subs),
    'small_radius_squared_modulus':q**2-norm-(1-c)*T,
    'q_positive_certificate':q-1-(2*r*(2-r)+(2-s)*r**2+4*r**3+r**4),
    'P_positive_certificate':2*P-1-((2*r-1)**2+10*r**2+40*r**3+2*r**4*((r-1)**2+6)+2*(2-s)*(r+r**2+r**4+r**5)),
    'A1_positive_certificate':A1-2*r-(2*r*(1-r)**2+10*r**3+4*r**4+2*(2-s)*r**2),
    'J_spatial_certificate':J-8*a-4*b**2-(2*a**2*(4*a+12-2*b)+8*a*(b-1)**2+2*b**3),
    'sharp_delta_coefficient':(16-8*e)-(sp.Rational(1,4)-4*e)*(8+21*e)**2-(164*e+sp.Rational(4935,4)*e**2+1764*e**3),
    'small_radius_angular_certificate':T-E-(4*r**2*(4-s*(1+c))+8*r**3*(2-s)+8*r**3*(2*c+1)**2+16*r**4*c**2*(1+c)+64*r**4*(1+c)+8*r**5*(2-s)+8*r**5*(2*c+1)**2+4*r**6*(4-s*(1+c))+8*r**7),
    'small_radius_E_certificate':E-4*r-4*r*(1-4*r-4*r**2-4*r**4-4*r**5),
}
result={name:sp.cancel(expr)==0 for name,expr in checks.items()}
assert all(result.values()),result
receipt={'scope':'Exact symbolic identities only; not a fresh Lean replay or numerical asymptotic test.','arithmetic':'Standard-library Fraction coefficients with exact Laurent-polynomial expansion','checks':result,'all_pass':all(result.values())}
out=Path(__file__).with_name('quartic_ordinary_identity_audit.json')
tmp=out.with_suffix('.tmp');tmp.write_text(json.dumps(receipt,indent=2),encoding='utf-8');tmp.replace(out)
print(json.dumps(receipt,indent=2))
