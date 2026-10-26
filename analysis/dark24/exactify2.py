"""Exact rationalization, version 2: first put the rounded W on the subspace of certifiable witnesses."""
import pickle
import sys
from fractions import Fraction as Fr

import numpy as np

from exactify import system, lhs_coeffs, ldl, rho, Gn, W

unk, rows = system()
# W unknowns: upper-triangular entries (p <= q); W[p][q] = W[q][p] = w_(p,q)
wunk = [(p, q) for p in range(8) for q in range(p, 8)]


def w_rows():
    """Monomial -> {w index: coeff} for the left side, with W symmetric."""
    from cert import idx, mono, add
    out = {}
    for p, (a, k) in enumerate(idx):
        for q, (b2, l) in enumerate(idx):
            base = mono(eb=(a,), fb=(k,), e=(b2,), f=(l,))
            for c in range(2):
                key = add(base, mono(eb=(c,), e=(c,)))
                i = wunk.index((min(p, q), max(p, q)))
                out.setdefault(key, {})
                out[key][i] = out[key].get(i, 0) + 1
    return out


WR = w_rows()
keys = sorted(set(rows) | set(WR))
ng, nw = len(unk), len(wunk)


def rref(M, ncols):
    M = [r[:] for r in M]
    piv, rr = [], 0
    for c in range(ncols):
        pr = next((i for i in range(rr, len(M)) if M[i][c] != 0), None)
        if pr is None:
            continue
        M[rr], M[pr] = M[pr], M[rr]
        inv = 1 / M[rr][c]
        M[rr] = [x * inv for x in M[rr]]
        for i in range(len(M)):
            if i != rr and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[rr])]
        piv.append(c)
        rr += 1
    return M, piv, rr


# Joint system [A_G | -A_W] [g; w] = 0. Eliminate G columns first: rows of the RREF with no G pivot give W constraints.
joint = [[Fr(rows.get(k, {}).get(i, 0)) for i in range(ng)] + [Fr(-WR.get(k, {}).get(j, 0)) for j in range(nw)]
         for k in keys]
Mj, pivj, rrj = rref(joint, ng + nw)
wcons = [row[ng:] for row, pc in zip(Mj[:rrj], pivj) if pc >= ng]
print('monomials', len(keys), 'G unknowns', ng, 'W unknowns', nw, 'W-only constraints', len(wcons), flush=True)
# Parameterize W: RREF of the W constraints; pivot coordinates are determined by the free ones.
Mw, pivw, rrw = rref(wcons, nw)
free = [j for j in range(nw) if j not in pivw]
print('free W coordinates', len(free))

for scale in (() if __name__ != '__main__' else (1000, 2000, 4000, 10000)):
    w0 = [Fr(round(W[p][q] * scale)) for (p, q) in wunk]
    w = w0[:]
    for row, pc in zip(Mw[:rrw], pivw):
        w[pc] = -sum(row[j] * w[j] for j in free)
    Wq = [[Fr(0)] * 8 for _ in range(8)]
    for (p, q), v in zip(wunk, w):
        Wq[p][q] = Wq[q][p] = v
    tr = sum(rho[p][q] * Wq[q][p] for p in range(8) for q in range(8))
    if tr >= 0:
        print(scale, 'trace not negative', float(tr))
        continue
    # Solve for g: rows A_G g = A_W w, exactly; take the particular solution closest to the numerical G.
    rhs = lhs_coeffs(Wq)
    for gden in (10 ** 2, 10 ** 3, 10 ** 4, 10 ** 6):
        g0 = [Fr(round(float(Gn[t][p][q]) * scale * gden), gden) for (t, p, q) in unk]
        A = [rows.get(k, {}) for k in keys]
        r = [rhs.get(k, Fr(0)) - sum(c * g0[i] for i, c in A[m].items()) for m, k in enumerate(keys)]
        # minimal-norm correction: dg = A^T y, (A A^T) y = r
        n = len(keys)
        AAt = [[Fr(sum(c * A[j].get(i, 0) for i, c in A[m].items())) for j in range(n)] for m in range(n)]
        Ma, piva, rra = rref([row + [r[i]] for i, row in enumerate(AAt)], n)
        if any(Ma[i][n] != 0 for i in range(rra, n)):
            print(scale, gden, 'inconsistent G system')
            continue
        y = [Fr(0)] * n
        for i, c in enumerate(piva):
            y[c] = Ma[i][n]
        g = g0[:]
        for m in range(n):
            if y[m] != 0:
                for i, c in A[m].items():
                    g[i] += c * y[m]
        ok = all(sum(c * g[i] for i, c in A[m].items()) == rhs.get(k, Fr(0)) for m, k in enumerate(keys))
        blocks, good = [], ok
        from cert import m1, m2, m3
        for t, ms in enumerate((m1, m2, m3)):
            G = [[Fr(0)] * len(ms) for _ in ms]
            for (tt, p, q), v in zip(unk, g):
                if tt == t:
                    G[p][q] = G[q][p] = v
            dec = ldl(G)
            if dec is None:
                good = False
                break
            blocks.append((G, dec))
        print(scale, gden, 'identity exact:', ok, ' blocks PD:', good, ' tr(rho W) =', float(tr), flush=True)
        if good:
            with open('exact_certificate.pkl', 'wb') as fh:
                fh.write(pickle.dumps({'W': Wq, 'tr': tr, 'blocks': blocks, 'scale': scale, 'gden': gden}))
            print('W entries:', sorted({str(x) for row in Wq for x in row})[:40])
            sys.exit(0)
