#!/usr/bin/env python3
"""Orderings of A = {2, ..., m-2} = Z_m \\ {0, 1, -1} with pairwise distinct partial sums for the odd
m = 5, ..., 23 (table in Section 4 of proof.md), found by depth-first search and checked."""


def find(m):
    A = list(range(2, m - 1)); k = len(A); used = set(); sums = set(); seq = []

    def dfs(s):
        if len(seq) == k:
            return s == 0
        for a in A:
            if a in used:
                continue
            t = (s + a) % m
            if len(seq) == k - 1:
                if t != 0:
                    continue
            elif t == 0 or t in sums:
                continue
            used.add(a); seq.append(a); sums.add(t)
            if dfs(t):
                return True
            used.discard(a); seq.pop(); sums.discard(t)
        return False
    return seq if dfs(0) else None


def check(m, seq):
    if sorted(seq) != list(range(2, m - 1)):
        return False
    s, ps = 0, []
    for a in seq:
        s = (s + a) % m; ps.append(s)
    return len(set(ps)) == len(ps) and ps[-1] == 0


if __name__ == "__main__":
    for m in range(5, 24, 2):
        seq = find(m)
        print(f"m = {m:2d}: {', '.join(map(str, seq))}   (checked: {check(m, seq)})")
