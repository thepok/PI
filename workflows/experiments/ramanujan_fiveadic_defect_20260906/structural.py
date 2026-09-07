#!/usr/bin/env python3
"""Exact rational checks for the five-adic block-transfer proof.

Requires SymPy.  No p-adic precision, cutoff scan, or pi digits are used.
This checks algebraic identities in the accompanying proof; it does not
mechanically verify the cited uniqueness theorem for Frobenius structures
or the foundational properties of crystalline cohomology.
"""
from fractions import Fraction
from math import comb
import sys

try:
    import sympy as s
except ImportError as exc:
    raise SystemExit("This script requires SymPy (python -m pip install sympy).") from exc

x, z = s.symbols("x z")
R = s.Rational

def zero(expr, label):
    value = s.cancel(expr)
    if value != 0:
        raise AssertionError(f"{label}: nonzero residual {value}")

# 1. The normalized coefficient ratio used by the five-block transfer.
G_ratio = s.prod(10*x+j for j in (1, 2, 3, 4, 6, 7, 8, 9))
G_ratio /= s.prod(5*x+j for j in (1, 2, 3, 4))**2
K_ratio = G_ratio**3 / 64**4
Q5 = s.prod((5*x+j+R(1,2))/(5*x+j+1) for j in range(5))**3
zero(K_ratio*(x+R(1,2))**3-Q5*(x+1)**3,
     "coefficient boundary identity")

# 2. Explicit Gauss-Manin calculation on E_z.
A = R(16,3)*(z-4)*(1-z)
B = R(128,27)*(z+8)*(1-z)**2
F = x**3+A*x+B
zero(-16*(4*A**3+27*B**2)-2**18*z**2*(1-z)**3,
     "elliptic discriminant")
a = -(5*z-2)/(12*(z-1))
b = -1/(16*(z-1))
c = (z-4)/9
d = (5*z-2)/(12*(z-1))
Romega = -4*(z-4)/9-(5*z-2)*x/(6*(z-1))+x**2/(8*(z-1))
Rxi = -16*(z-1)*(z+8)/27+2*(z-4)*x/9-(5*z-2)*x**2/(6*(z-1))
# theta(omega) = (a+b*x)*dx/y + d_x(Romega/y), and similarly xi.
for j, u, v, correction in ((0,a,b,Romega), (1,c,d,Rxi)):
    zero(-z*s.diff(F,z)*x**j/2
         - ((u+v*x)*F+s.diff(correction,x)*F-correction*s.diff(F,x)/2),
         f"Gauss-Manin exact differential, column {j}")
N = s.Matrix([[2*a,c,0],[2*b,a+d,2*c],[0,b,2*d]])
N -= z/(2*(1-z))*s.eye(3)  # the Kummer line r^2=1-z
N = N.applyfunc(s.factor)

def theta(v):
    return (z*v.diff(z)+N*v).applyfunc(s.cancel)

h = s.Matrix([1,0,0])
vectors = [h]
for _ in range(3):
    vectors.append(theta(vectors[-1]))
residual = vectors[3]-z*(vectors[3]+R(3,2)*vectors[2]
                        +R(3,4)*vectors[1]+R(1,8)*vectors[0])
for entry in residual:
    zero(entry, "hypergeometric differential equation")
zero(s.Matrix.hstack(*vectors[:3]).det()+1/(1024*(z-1)**3),
     "cyclic comparison determinant")
if (vectors[0]+6*vectors[1]).subs(z,R(1,4)) != s.Matrix([-1,1,0]):
    raise AssertionError("Distinguished class is not r*omega*(xi-omega)")

# 3. Determinant differential equation and rational branch normalization.
kappa = (1-z**5)/(1-z)**5
zero(kappa-1-5*z*(1-z+z**2)/(1-z)**4, "kappa near-one expression")
trace = 3*z/(2*(1-z))
log_derivative = -6*z/(1-z)+R(3,2)*z*s.diff(kappa,z)/kappa
zero(log_derivative-(trace-5*trace.subs(z,z**5)),
     "transfer determinant differential equation")
a0 = R(1,4)
w0 = a0**5
delta = (1-a0)/(1-w0)
zero(kappa.subs(z,a0)-R(341,81), "kappa value")
zero(delta-R(256,341), "Taylor determinant argument")
root_near_one = -R(16,9)
zero(root_near_one**2-kappa.subs(z,a0)*delta, "square root for determinant")
assert (int(s.numer(root_near_one))*pow(int(s.denom(root_near_one)),-1,5)) % 5 == 1
zero(125*(1-a0)**6*root_near_one**3+125, "exact determinant -125")

# 4. Explicit CM 3-isogeny and action on de Rham classes.
F0 = x**3-15*x+22
X = x+24/(x-3)+16/(x-3)**2
Xp = s.diff(X,x)
zero(F0*Xp**2-(X**3-135*X-594), "degree-three isogeny")
# With Y=y*X', dX/Y=dx/y identically.  For the second differential:
exact_derivative = s.diff(F0,x)/(2*(x-3))-F0/(x-3)**2
zero(exact_derivative-(x/R(2)-R(3,2)-6/(x-3)-4/(x-3)**2),
     "d(y/(x-3))")
zero(X-(3*x-6-4*exact_derivative), "CM second-kind differential reduction")
# s^2=-3: E' has coefficients s^4*(-15), s^6*22.
zero(-135-(-3)**2*(-15), "CM twist coefficient A")
zero(-594-(-3)**3*22, "CM twist coefficient B")

# 5. Actual selected initial value, computed as an exact rational.
def bj(j):
    return Fraction(comb(2*j,j)**3, 256**j)
S5 = sum((6*j+1)*bj(j) for j in range(5))
U1 = (S5-5)/(125*bj(1))
if U1 != Fraction(-16008833,16777216):
    raise AssertionError(f"Unexpected U_1={U1}")

print("PASS: normalized five-block coefficient boundary identity")
print("PASS: both Gauss-Manin exact-differential identities")
print("PASS: hypergeometric equation and invertible cyclic comparison")
print("PASS: 1+6*theta maps to r*omega*(xi-omega) at z=1/4")
print("PASS: transfer determinant equation and exact branch value -125")
print("PASS: explicit degree-three isogeny and CM differential reduction")
print(f"PASS: actual initial value U_1={U1}")
print("No p-adic precision or numerical cutoff testing was used.")

