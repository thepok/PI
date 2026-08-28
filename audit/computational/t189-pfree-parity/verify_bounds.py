#!/usr/bin/env python3
from decimal import Decimal, getcontext
from pathlib import Path
import re
getcontext().prec=50
HERE=Path(__file__).resolve().parent

def interval(text,name):
    m=re.search(rf'^{re.escape(name)}=\[([^,]+), ([^\]]+)\]$',text,re.M)
    if not m: raise AssertionError(f'missing {name}')
    return Decimal(m.group(1)),Decimal(m.group(2))

def rows(text):
    out={}
    pat=re.compile(r'^(\d) G=\[([^,]+), ([^\]]+)\] D=\[([^,]+), ([^\]]+)\] Hdef=\[([^,]+), ([^\]]+)\] Y=\[([^,]+), ([^\]]+)\]$',re.M)
    for m in pat.finditer(text):
        out[int(m.group(1))]=tuple(Decimal(m.group(i)) for i in range(2,10))
    return out

root=(HERE/'rootall_interval_output.txt').read_text()
B=interval(root,'B_parent_q1000_A334_N1000')
assert B[0]>0
rr=rows(root)
assert set(rr)==set(range(10))
# tuple order Glo,Ghi,Dlo,Dhi,Hlo,Hhi,Ylo,Yhi
fmr={d for d,v in rr.items() if v[2]>0 and v[6]>0}
assert fmr=={0,1,2,3,4,8,9},fmr
for d in {5,6,7}:
    assert rr[d][3]<0

As=[334,1334,2334,3334,4334,8334,9334]
print('claim=checked_interval_sign_summary')
print('root_B_lower',B[0])
print('root_exact_FMR_digits',','.join(map(str,sorted(fmr))))
print('A max_parity_upper C_interval V_interval')
worst=Decimal('-Infinity')
for A in As:
    t=(HERE/f'node_A{A}.txt').read_text()
    assert 'reduction_fallbacks=0' in t
    me=interval(t,'M_even'); mo=interval(t,'M_odd')
    c=interval(t,'C_common_including_deficit')
    v=interval(t,'qR5_minus_deltaH')
    assert me[1]<0 and mo[1]<0
    u=max(me[1],mo[1]); worst=max(worst,u)
    print(A,u,f'[{c[0]},{c[1]}]',f'[{v[0]},{v[1]}]')
assert worst<Decimal('-8424')
# At the sector-5 bottleneck, literal FMR nevertheless holds uniquely at d=5.
t=(HERE/'node_A1334.txt').read_text(); nr=rows(t)
unique={d for d,x in nr.items() if x[2]>0 and x[6]>0}
assert unique=={5},unique
for d in set(range(10))-{5}: assert nr[d][3]<0
print('uniform_all_reached_nodes_max_parity_upper',worst)
print('uniform_integer_gap_eta',8424)
print('A1334_unique_literal_FMR_digit',5)
