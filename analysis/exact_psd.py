"""Exact positive-semidefiniteness certificates over the rationals.

`psd_certificate(M)` runs symmetric Gaussian elimination with diagonal pivoting on a real symmetric
matrix of Fractions. It returns (True, None, pivots) when every pivot is positive and the remainder
vanishes exactly, a proof that M >= 0 (M = L D L^T with D >= 0); or (False, w, pivots) with a
rational vector w such that w^T M w < 0 exactly.
"""
from __future__ import annotations

from fractions import Fraction


def quadratic_form(M, w):
    n = len(M)
    return sum(w[i] * M[i][j] * w[j] for i in range(n) if w[i] for j in range(n) if w[j])


def psd_certificate(M):
    n = len(M)
    S = [list(map(Fraction, row)) for row in M]
    active = list(range(n))
    pivots, history = [], []          # history: (pivot index, {j: S[p][j] / S[p][p]})

    def lift(tail):
        x = [Fraction(0)] * n
        for j, v in tail.items():
            x[j] = Fraction(v)
        for p, coeffs in reversed(history):
            x[p] = -sum(c * x[j] for j, c in coeffs.items())
        return x

    while active:
        neg = [i for i in active if S[i][i] < 0]
        if neg:
            return False, lift({neg[0]: 1}), pivots
        pos = [i for i in active if S[i][i] > 0]
        if not pos:
            for a in active:
                for b in active:
                    if a != b and S[a][b] != 0:
                        return False, lift({a: 1, b: -1 if S[a][b] > 0 else 1}), pivots
            return True, None, pivots
        p = max(pos, key=lambda i: S[i][i])
        d = S[p][p]
        pivots.append(d)
        active.remove(p)
        coeffs = {j: S[p][j] / d for j in active if S[p][j] != 0}
        history.append((p, coeffs))
        for i in active:
            if S[p][i] != 0:
                f = S[p][i] / d
                row_i, row_p = S[i], S[p]
                for j in active:
                    if row_p[j] != 0:
                        row_i[j] -= f * row_p[j]
    return True, None, pivots


def rank(M):
    A = [list(map(Fraction, row)) for row in M]
    r, cols = 0, len(A[0]) if A else 0
    for c in range(cols):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        for i in range(r + 1, len(A)):
            if A[i][c] != 0:
                f = A[i][c] / A[r][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        r += 1
    return r
