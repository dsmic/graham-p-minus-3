#!/usr/bin/env python3
"""Data of example.md: p = 43 in full; p = 2^127 - 1 (start of the ordering), with a Lucas-Lehmer test."""
from construction import Z, ordering

# p = 43
p, r = 43, 20
a = ordering(r); s, ps = 0, []
for x in a:
    s = (s + x) % p; ps.append(s)
assert sorted(a) == list(range(2, p - 1)) and len(set(ps)) == len(ps) and ps[-1] == 0
print("p = 43, ordering of {2, ..., 41}:", a)
print("partial sums:", ps)
print("never visited:", sorted(set(range(p)) - set(ps)))

# p = 2^127 - 1: Mersenne prime (Lucas-Lehmer test), r = (p - 3)/2 even, h = r/2
q = 127; P = 2**q - 1
t = 4
for _ in range(q - 2):
    t = (t * t - 2) % P
assert t == 0, "not prime"
R = (P - 3) // 2
first = [5, P - 4, 3, R - 3, R + 8, R - 6, R + 10, R - 8, R + 12, R - 10]     # = 5, -4, 3, r-3, r+8, ...
# the vertices of Z_R at positions 0..10 (Z1 and the start of Z2), from the formulas of proof.md
verts = [0, 5, 1, 4, R + 1, 6, R, 7, R - 1, 8, R - 2]
assert all((verts[i + 1] - verts[i]) % P == first[i] for i in range(10))
print("p = 2^127 - 1 =", P, "(prime: Lucas-Lehmer)")
print("r =", R)
print("partial sums of the first 10 elements:", verts[1:])
# consistency with the general construction for a smaller r of the same parity class
rr = 40; c = Z(rr)
assert c[:11] == [0, 5, 1, 4, rr + 1, 6, rr, 7, rr - 1, 8, rr - 2]
