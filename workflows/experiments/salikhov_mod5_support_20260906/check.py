#!/usr/bin/env python3
"""Exact finite-field certificate for the pi-multiplier's nonzero support mod 5.
Standard library only. No values or decimal digits of pi are used.

If A_n=[w^(3*n)](w-1)^(2*n) H(w)^(2*n)/(2-w)^(3*n+1),
H=25(w-1)^4+6(w-1)^2+1, then the normalized integer pi multiplier
q_n=(-1)^n 2^(1-floor(5*n/2)) A_n has the same nonzero support mod 5.
The script constructs all Cartier states, not a finite sample of coefficients.
"""
from collections import deque

P = 5

def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return tuple(a)

def mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] = (c[i+j] + x*y) % P
    return trim(c)

def power(a, k):
    z = (1,)
    for _ in range(k):
        z = mul(z, a)
    return z

# F=(w-1)^2 H^2, D=(2-w)^3, S0=(2-w)^2, reduced mod 5.
F = mul(power((4,1), 2), power((2,3,1), 2))
D = power((2,4), 3)
S0 = power((2,4), 2)
# (-1)^a * binomial(4,a) == 1 mod 5 for every a in {0,...,4}.
B = [mul(power(F,a), power(D,4-a)) for a in range(5)]

def section(S, a, b):
    return trim(mul(S, B[a])[b::5] or [0])

start = (S0, 0)
states, index, queue, edges = [start], {start:0}, deque([start]), []
while queue:
    S, carry = queue.popleft()
    row = []
    for a in range(5):
        b, newcarry = (3*a+carry) % 5, (3*a+carry) // 5
        new = (section(S,a,b), newcarry)
        if new not in index:
            index[new] = len(states)
            states.append(new)
            queue.append(new)
        row.append(index[new])
    edges.append(row)
assert len(states) == 27
assert edges[0][0] == edges[0][1] == 0

def output(i):
    S, carry = states[i]
    while carry:
        S = section(S, 0, carry % 5)
        carry //= 5
    return 2*S[0] % 5  # D(0)^(-1) = 8^(-1) = 2 mod 5.

def apply_M(v):
    return [sum(v[j] for j in row) for row in edges]

v0 = [int(output(i) != 0) for i in range(len(states))]
v1 = apply_M(v0)
v2 = apply_M(v1)
v3 = apply_M(v2)
v4 = apply_M(v3)
# This vector identity proves the scalar counting recurrence at EVERY length.
assert all(v4[i]-5*v3[i]+3*v2[i]+3*v1[i]-2*v0[i] == 0
           for i in range(len(states)))
assert [v0[0], v1[0], v2[0], v3[0]] == [1,4,16,65]

# Check coefficient values against the first published rational pi multipliers.
def coefficient_mod5(n):
    i = 0
    while n:
        i = edges[i][n % 5]
        n //= 5
    return output(i)
assert [coefficient_mod5(n) for n in range(3)] == [3,3,2]

print('All Cartier states exhausted:', len(states))
print('Two distinct one-digit loops at the initial nonzero state: 0 and 1')
print('Certified generating function for h_L = #{0<=n<5^L: 5 does not divide q_n}:')
print('(1-z-z^2)/(1-5*z+3*z^2+3*z^3-2*z^4)')
print('Equivalently h_(L+3)=4*h_(L+2)+h_(L+1)-2*h_L-1.')
v = v0
counts = []
for _ in range(12):
    counts.append(v[0])
    v = apply_M(v)
print('Initial exact counts:', counts)
print('This certificate proves no statement about decimal digits of pi.')
