#!/usr/bin/env python3
"""The explicit cycle Z_r of proof.md and the resulting orderings.

Z_r is a Hamiltonian cycle on {0, ..., 2r-1} (r >= 9) whose steps are +-2, ..., +-(r+1), each exactly
once. Lifted to Z_m, m = 2r + 3, every rotation of its step sequence is an ordering of
Z_m \\ {0, 1, -1} with pairwise distinct partial sums; multiplying by a unit x gives Z_m \\ {0, x, -x}.

Usage: python3 construction.py [r_max]     (checks r = 9 .. r_max, default 2000)
"""
import sys
from math import gcd


def Z(r):
    """Vertices of the cycle Z_r in cyclic order (parts Z1, ..., Z5 of proof.md)."""
    if r % 2 == 0:
        h = r // 2
        Z2 = [v for i in range(h - 4) for v in (6 + i, r - i)]
        Z4 = [v for i in range(h - 5) for v in (3*h + 4 + i, 3*h - 2 - i)] + [4*h - 1, r + 3]
        return ([0, 5, 1, 4, r + 1] + Z2 + [3*h + 1, 3*h - 1, h + 2, 3*h, 3*h + 2, h + 4, 3*h + 3, h + 3]
                + Z4 + [2, r + 2, 3])
    s = (r - 1) // 2
    Z2 = [v for i in range(s - 4) for v in (6 + i, 2*s + 1 - i)]
    Z4 = [v for i in range(s - 3) for v in (3*s + 5 + i, 3*s - i)]
    return ([0, r + 1] + Z2 + [s + 4, 3*s + 4, s + 2, 3*s + 3, s + 5, 3*s + 2, s + 3, 3*s + 1]
            + Z4 + [4, r + 2, 2, 5, 1, 3])


def is_valid_cycle(r):
    """Every point once, and the steps are exactly +-2, ..., +-(r+1)."""
    c = Z(r); n = 2 * r
    if sorted(c) != list(range(n)):
        return False
    st = [c[(i + 1) % n] - c[i] for i in range(n)]
    want = list(range(2, r + 2))
    return sorted(d for d in st if d > 0) == want and sorted(-d for d in st if d < 0) == want


def ordering(r, x=1):
    """Ordering of Z_m \\ {0, x, -x}, m = 2r + 3, with pairwise distinct partial sums."""
    c = Z(r); n = 2 * r; m = 2 * r + 3
    return [((c[(i + 1) % n] - c[i]) * x) % m for i in range(n)]


def is_valid_ordering(order, m, x):
    if sorted(order) != sorted(set(range(1, m)) - {x % m, (-x) % m}):
        return False
    s, seen = 0, set()
    for a in order:
        s = (s + a) % m
        if s in seen:
            return False
        seen.add(s)
    return True


if __name__ == "__main__":
    rmax = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    bad = [r for r in range(9, rmax + 1) if not is_valid_cycle(r)]
    print(f"Z_r valid for all r = 9..{rmax}: {not bad}" + (f", exceptions {bad[:10]}" if bad else ""))
    bad2 = 0
    for r in range(9, min(rmax, 300) + 1):
        m = 2 * r + 3
        for x in range(1, m // 2 + 1):
            if gcd(x, m) == 1 and not is_valid_ordering(ordering(r, x), m, x):
                bad2 += 1
    print(f"orderings in Z_m (m = 21..{2 * min(rmax, 300) + 3}, all units x): errors {bad2}")
