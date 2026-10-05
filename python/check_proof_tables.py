#!/usr/bin/env python3
"""Checks the statements of Section 3 of proof.md literally, for r = 11 .. R:
(1) the arcs of Z_r are exactly: zigzag Z2 + zigzag Z4 (formulas of Section 3b) + the 18 further arcs of
    the table in Section 3c;
(2) the zigzags give the stated sets of lengths, the 18 arcs give 9 lengths to the right and 9 to the
    left, and together every length 2, ..., r+1 occurs exactly once in each direction.
Usage: python3 check_proof_tables.py [R]   (default 2000)
"""
import sys
from collections import Counter
from construction import Z


def claims(r):
    if r % 2 == 0:
        h = r // 2
        z2 = [(6+i, r-i) for i in range(h-4)] + [(r-i, 7+i) for i in range(h-5)]
        z4 = ([(3*h+4+i, 3*h-2-i) for i in range(h-5)] + [(3*h-2-i, 3*h+5+i) for i in range(h-6)]
              + [(2*h+4, 4*h-1), (4*h-1, r+3)])
        z2R, z2L = set(range(4, r-5, 2)), set(range(5, r-6, 2))
        z4R, z4L = set(range(7, r-4, 2)), set(range(6, r-3, 2))
        extra = [(0, 5), (1, 4), (4, r+1), (h+5, 3*h+1), (h+2, 3*h), (3*h, 3*h+2), (h+4, 3*h+3), (h+3, 3*h+4),
                 (2, r+2), (5, 1), (r+1, 6), (3*h+1, 3*h-1), (3*h-1, h+2), (3*h+2, h+4), (3*h+3, h+3), (r+3, 2),
                 (r+2, 3), (3, 0)]
    else:
        s = (r - 1) // 2
        z2 = [(6+i, 2*s+1-i) for i in range(s-4)] + [(2*s+1-i, 7+i) for i in range(s-5)]
        z4 = [(3*s+5+i, 3*s-i) for i in range(s-3)] + [(3*s-i, 3*s+6+i) for i in range(s-4)]
        z2R, z2L = set(range(5, r-5, 2)), set(range(6, r-6, 2))
        z4R, z4L = set(range(6, r-4, 2)), set(range(5, r-3, 2))
        extra = [(0, r+1), (s+4, 3*s+4), (s+2, 3*s+3), (s+5, 3*s+2), (s+3, 3*s+1), (3*s+1, 3*s+5), (4, 2*s+3),
                 (2, 5), (1, 3), (r+1, 6), (s+6, s+4), (3*s+4, s+2), (3*s+3, s+5), (3*s+2, s+3), (2*s+4, 4),
                 (2*s+3, 2), (5, 1), (3, 0)]
    return z2, z4, z2R, z2L, z4R, z4L, extra


def lengths(E, sign):
    return sorted(abs(b - a) for a, b in E if (b - a) * sign > 0)


if __name__ == "__main__":
    R = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    bad = []
    for r in range(11, R + 1):
        c = Z(r); n = 2 * r
        arcs = Counter((c[i], c[(i + 1) % n]) for i in range(n))
        z2, z4, z2R, z2L, z4R, z4L, extra = claims(r)
        full = list(range(2, r + 2))
        ok = (Counter(z2 + z4 + extra) == arcs and len(extra) == 18
              and lengths(z2, 1) == sorted(z2R) and lengths(z2, -1) == sorted(z2L)
              and lengths(z4, 1) == sorted(z4R) and lengths(z4, -1) == sorted(z4L)
              and len(lengths(extra, 1)) == 9 and len(lengths(extra, -1)) == 9
              and sorted(list(z2R | z4R) + lengths(extra, 1)) == full
              and sorted(list(z2L | z4L) + lengths(extra, -1)) == full)
        if not ok:
            bad.append(r)
    print(f"statements of proof.md, Section 3, for r = 11..{R}: exceptions {bad if bad else 'none'}")
