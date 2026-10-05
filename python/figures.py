#!/usr/bin/env python3
"""Draws the figures of proof.md and example.md (needs matplotlib):
  ../figures/cycle.svg       the cycle Z_r for r = 20 and r = 21 (arc diagram)
  ../figures/example_p43.svg the frog's path for p = 43
"""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Arc, Circle
from matplotlib.lines import Line2D
from construction import Z, ordering

BLUE, ORANGE, INK, MUTED, FAINT, SURF = "#2a78d6", "#eb6834", "#0b0b0b", "#52514e", "#b9b8b3", "#fcfcfb"


def parts(r):
    """(vertex, part) in cyclic order; parts Z1..Z5 as in proof.md."""
    if r % 2 == 0:
        h = r // 2
        P = [("Z1", [0, 5, 1, 4, r + 1]), ("Z2", [v for i in range(h - 4) for v in (6 + i, r - i)]),
             ("Z3", [3*h + 1, 3*h - 1, h + 2, 3*h, 3*h + 2, h + 4, 3*h + 3, h + 3]),
             ("Z4", [v for i in range(h - 5) for v in (3*h + 4 + i, 3*h - 2 - i)] + [4*h - 1, r + 3]),
             ("Z5", [2, r + 2, 3])]
    else:
        s = (r - 1) // 2
        P = [("Z1", [0, r + 1]), ("Z2", [v for i in range(s - 4) for v in (6 + i, 2*s + 1 - i)]),
             ("Z3", [s + 4, 3*s + 4, s + 2, 3*s + 3, s + 5, 3*s + 2, s + 3, 3*s + 1]),
             ("Z4", [v for i in range(s - 3) for v in (3*s + 5 + i, 3*s - i)]),
             ("Z5", [4, r + 2, 2, 5, 1, 3])]
    out = [(v, t) for t, B in P for v in B]
    assert [v for v, _ in out] == Z(r)
    return out


def arc(ax, u, v, col, lw):
    c, rad = (u + v) / 2, abs(v - u) / 2
    th = (0, 180) if v > u else (180, 360)
    ax.add_patch(Arc((c, 0), 2 * rad, 2 * rad, theta1=th[0], theta2=th[1], color=col, lw=lw, zorder=1))


def cycle_figure():
    fig, axes = plt.subplots(2, 1, figsize=(12, 9.4), facecolor=SURF)
    for ax, r in zip(axes, (20, 21)):
        ax.set_facecolor(SURF)
        seq = parts(r); n = 2 * r
        for i in range(n):
            (u, tu), (v, tv) = seq[i], seq[(i + 1) % n]
            arc(ax, u, v, BLUE if (tu == tv and tu in ("Z2", "Z4")) else ORANGE, 1.4)
        for x in range(n):
            ax.add_patch(Circle((x, 0), 0.17, facecolor=SURF, edgecolor=MUTED, lw=0.8, zorder=2))
        for x in range(0, n, 5):
            ax.text(x, 0.45, str(x), ha="center", va="bottom", fontsize=8, color=MUTED, zorder=3,
                    bbox=dict(facecolor=SURF, edgecolor="none", pad=0.6))
        ax.set_xlim(-0.8, n - 0.2); ax.set_ylim(-(r + 2) / 2 - 0.3, (r + 2) / 2 + 0.3)
        ax.set_aspect("equal"); ax.axis("off")
        ax.text(-0.8, (r + 2) / 2, f"r = {r} ({'even' if r % 2 == 0 else 'odd'}),  m = {2*r+3}",
                fontsize=11, color=INK, va="top")
        ax.text(n - 0.2, (r + 2) / 2, "steps to the right", fontsize=9, color=MUTED, ha="right", va="top")
        ax.text(n - 0.2, -(r + 2) / 2, "steps to the left", fontsize=9, color=MUTED, ha="right", va="bottom")
    fig.legend(handles=[Line2D([], [], color=BLUE, lw=2, label="arcs inside the zigzags Z2, Z4"),
                        Line2D([], [], color=ORANGE, lw=2, label="the 18 further arcs (boundary, core, junctions)")],
               loc="lower center", ncol=2, frameon=False, fontsize=10, labelcolor=INK)
    fig.suptitle("The cycle Z_r: every length 2, …, r+1 exactly once to the right and once to the left",
                 fontsize=12, color=INK, y=0.985)
    fig.tight_layout(rect=(0, 0.04, 1, 0.97))
    fig.savefig("../figures/cycle.svg")


def example_figure():
    p, r = 43, 20
    a = ordering(r); pos, s = [0], 0
    for x in a:
        s = (s + x) % p; pos.append(s)
    fig, ax = plt.subplots(figsize=(13, 6.4), facecolor=SURF)
    ax.set_facecolor(SURF)
    for i, x in enumerate(a):
        arc(ax, pos[i], pos[i + 1], BLUE if x <= r + 1 else ORANGE, 1.4)
    for k in range(p):
        vis = k < 2 * r
        ax.add_patch(Circle((k, 0), 0.38, facecolor=SURF if vis else "#efeee9",
                            edgecolor=MUTED if vis else FAINT, lw=0.9, zorder=2, ls="-" if vis else "--"))
        ax.text(k, 0, str(k), ha="center", va="center", fontsize=7, color=INK if vis else FAINT, zorder=3)
    ax.annotate("start and end: 0", xy=(0, -0.45), xytext=(0, -6.5), ha="center", fontsize=9, color=MUTED,
                arrowprops=dict(arrowstyle="-", color=MUTED, lw=0.8))
    ax.annotate("never visited: 40, 41, 42", xy=(41, -0.45), xytext=(41, -6.5), ha="center", fontsize=9,
                color=MUTED, arrowprops=dict(arrowstyle="-", color=MUTED, lw=0.8))
    ax.set_xlim(-1, p); ax.set_ylim(-(r + 3) / 2, (r + 3) / 2); ax.set_aspect("equal"); ax.axis("off")
    ax.legend(handles=[Line2D([], [], color=BLUE, lw=2, label="jump a ≤ 21 (to the right)"),
                       Line2D([], [], color=ORANGE, lw=2, label="jump a ≥ 22 (= to the left by 43 − a)")],
              loc="upper right", frameon=False, fontsize=9, labelcolor=INK)
    ax.set_title("p = 43: the 40 numbers 2, …, 41 as jumps – the frog never lands on the same stone twice",
                 fontsize=11, color=INK, loc="left")
    fig.tight_layout()
    fig.savefig("../figures/example_p43.svg")


if __name__ == "__main__":
    cycle_figure(); example_figure()
    print("written: ../figures/cycle.svg, ../figures/example_p43.svg")
