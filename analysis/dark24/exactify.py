"""Exact rationalization of the certified 2x4 witness (b = 3/5 Horodecki state)."""
import pickle
import sys
from fractions import Fraction as Fr

import numpy as np

from cert import m1, m2, m3, conj_mono, mono, add, idx

W = np.load('W_interior.npy')
Gn = [np.load(f'G{i}_interior.npy') for i in (1, 2, 3)]
b, s = Fr(3, 5), Fr(4, 5)
R = [[Fr(0)] * 8 for _ in range(8)]
for i in range(3):
    R[i][i] = b; R[i][5 + i] = R[5 + i][i] = b; R[5 + i][5 + i] = b
R[3][3] = b; R[4][4] = (1 + b) / 2; R[7][7] = (1 + b) / 2; R[4][7] = R[7][4] = s / 2
rho = [[x / (7 * b + 1) for x in row] for row in R]


def ldl(M):
    n = len(M)
    L = [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
    D = [Fr(0)] * n
    for j in range(n):
        D[j] = M[j][j] - sum(L[j][k] ** 2 * D[k] for k in range(j))
        if D[j] <= 0:
            return None
        for i in range(j + 1, n):
            L[i][j] = (M[i][j] - sum(L[i][k] * L[j][k] * D[k] for k in range(j))) / D[j]
    return L, D


def system():
    unk = []
    for t, ms in enumerate((m1, m2, m3)):
        for p in range(len(ms)):
            for q in range(p, len(ms)):
                unk.append((t, p, q))
    col = {u: i for i, u in enumerate(unk)}
    rows = {}
    for t, ms in enumerate((m1, m2, m3)):
        for p, mp in enumerate(ms):
            _, cpm = conj_mono(mp)
            for q, mq in enumerate(ms):
                mqv, _ = conj_mono(mq)
                key = add(cpm, mqv)
                u = (t, min(p, q), max(p, q))
                rows.setdefault(key, {})
                # G symmetric: entry (p,q) and (q,p) both equal the unknown u
                rows[key][col[u]] = rows[key].get(col[u], 0) + 1
    return unk, rows


def lhs_coeffs(Wq):
    rhs = {}
    for p, (a, k) in enumerate(idx):
        for q, (b2, l) in enumerate(idx):
            base = mono(eb=(a,), fb=(k,), e=(b2,), f=(l,))
            for c in range(2):
                key = add(base, mono(eb=(c,), e=(c,)))
                rhs[key] = rhs.get(key, Fr(0)) + Wq[p][q]
    return rhs


def attempt(scale, gden):
    Wq = [[Fr(round(W[p][q] * scale)) for q in range(8)] for p in range(8)]
    for p in range(8):
        for q in range(p):
            Wq[p][q] = Wq[q][p]
    tr = sum(rho[p][q] * Wq[q][p] for p in range(8) for q in range(8))
    if tr >= 0:
        return 'trace not negative', tr
    unk, rows = system()
    rhs = lhs_coeffs(Wq)
    keys = sorted(set(rows) | set(rhs))
    g = [Fr(round(float(Gn[t][p][q]) * scale * gden), gden) for (t, p, q) in unk]
    A = [rows.get(k, {}) for k in keys]
    r = [rhs.get(k, Fr(0)) - sum(c * g[i] for i, c in A[m].items()) for m, k in enumerate(keys)]
    n = len(keys)
    AAt = [[sum(c * A[j].get(i, 0) for i, c in A[m].items()) for j in range(n)] for m in range(n)]
    M = [row[:] + [r[i]] for i, row in enumerate(AAt)]
    piv, rr = [], 0
    for c in range(n):
        pr = next((i for i in range(rr, n) if M[i][c] != 0), None)
        if pr is None:
            continue
        M[rr], M[pr] = M[pr], M[rr]
        inv = 1 / M[rr][c]
        M[rr] = [x * inv for x in M[rr]]
        for i in range(n):
            if i != rr and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[rr])]
        piv.append(c)
        rr += 1
    if any(M[i][n] != 0 for i in range(rr, n)):
        return 'inconsistent', None
    y = [Fr(0)] * n
    for i, c in enumerate(piv):
        y[c] = M[i][n]
    dg = [Fr(0)] * len(unk)
    for m in range(n):
        if y[m] != 0:
            for i, c in A[m].items():
                dg[i] += c * y[m]
    gex = [a + d for a, d in zip(g, dg)]
    assert all(sum(c * gex[i] for i, c in A[m].items()) == rhs.get(k, Fr(0)) for m, k in enumerate(keys))
    blocks = []
    for t, ms in enumerate((m1, m2, m3)):
        n_ = len(ms)
        G = [[Fr(0)] * n_ for _ in range(n_)]
        for (tt, p, q), v in zip(unk, gex):
            if tt == t:
                G[p][q] = v
                G[q][p] = v
        dec = ldl(G)
        if dec is None:
            return 'G block not PD', t
        blocks.append((G, dec))
    return 'ok', (Wq, tr, blocks, max(abs(x) for x in dg))


for scale in (() if __name__ != '__main__' else (1000, 2000, 5000)):
    for gden in (10 ** 3, 10 ** 4, 10 ** 6):
        st, res = attempt(scale, gden)
        print(scale, gden, st, float(res[1]) if st == 'ok' else res, flush=True)
        if st == 'ok':
            with open(f'exact_{scale}_{gden}.pkl', 'wb') as fh:
                pickle.Pickler(fh).save if False else fh.write(pickle.dumps(res))
            Wq = res[0]
            print('   W integer range', min(min(r) for r in Wq), max(max(r) for r in Wq),
                  ' max correction', float(res[3]))
            sys.exit(0)
