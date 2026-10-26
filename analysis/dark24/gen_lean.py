"""Generate the Lean source for the (2,4) darkness proof from the exact certificate."""
import math
import pickle
from fractions import Fraction as Fr

from cert import m1, m2, m3

d = pickle.loads(open('exact_certificate.pkl', 'rb').read())
W = d['W']
blocks = d['blocks']
idx = [(a, k) for a in range(2) for k in range(4)]


def q(x):
    """A rational as a Lean ℚ literal."""
    x = Fr(x)
    return f'({x.numerator} : ℚ)' if x.denominator == 1 else f'({x.numerator} / {x.denominator} : ℚ)'


def zc(n):
    """An integer as a cast into ℂ (so that star simplifies by star_intCast)."""
    return f'(({n} : ℤ) : ℂ)'


# ---- the map Φ₂₄(X)_{kl} = Σ_{a,b} X_ab W[(a,k)][(b,l)]
def phi_entry(k, l):
    terms = []
    for a in range(2):
        for b in range(2):
            c = W[4 * a + k][4 * b + l]
            if c != 0:
                terms.append(f'{zc(int(c))} * X {a} {b}')
    return ' + '.join(terms) if terms else '0'


rows = []
for k in range(4):
    rows.append(', '.join(phi_entry(k, l) for l in range(4)))
phi_def = ('/-- The (2,4) map: `Φ₂₄(X)_kl = Σ_ab X_ab W((a,k),(b,l))` with the integer witness `W` below. -/\n'
           'def phi24 (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=\n  !![' + ';\n    '.join(rows) + ']')


# ---- monomials in v (input) and w (output): e = star v, f = w
def mono_lean(m):
    (t, (i, j)), k = m
    if t == 'e':      # e_i e_j f_k = star v_i star v_j w_k
        return f'star (v {i}) * star (v {j}) * w {k}'
    if t == 'm':      # star e_i e_j f_k = v_i star v_j w_k
        return f'v {i} * star (v {j}) * w {k}'
    return f'v {i} * v {j} * w {k}'   # star e_i star e_j f_k


sos_terms = []
for (G, (L, D)), ms in zip(blocks, (m1, m2, m3)):
    n = len(ms)
    for k in range(n):
        col = [L[p][k] for p in range(n)]
        den = 1
        for c in col:
            den = den * c.denominator // math.gcd(den, c.denominator)
        ints = [int(c * den) for c in col]
        g = 0
        for v in ints:
            g = math.gcd(g, abs(v))
        ints = [v // g for v in ints]
        scale = Fr(den, g)                       # ℓ = (1/scale) * Σ ints * m
        coeff = D[k] / scale ** 2
        lin = ' + '.join(f'{zc(c)} * ({mono_lean(ms[p])})' for p, c in enumerate(ints) if c != 0)
        sos_terms.append((coeff, lin))

lhs_terms = []
for x, (a, k) in enumerate(idx):
    for y, (b, l) in enumerate(idx):
        c = W[x][y]
        if c != 0:
            lhs_terms.append(f'{zc(int(c))} * (v {a} * star (w {k}) * star (v {b}) * w {l})')
lhs = '(v 0 * star (v 0) + v 1 * star (v 1)) * (' + ' + '.join(lhs_terms) + ')'
rhs = ' + '.join(f'({q(c)} : ℂ) * (({lin}) * star ({lin}))' for c, lin in sos_terms)


# ---- the witness state ρ (Horodecki 2x4, b = 3/5) and its partial transpose, as nonnegative rank-one sums
b, s = Fr(3, 5), Fr(4, 5)
R = [[Fr(0)] * 8 for _ in range(8)]
for i in range(3):
    R[i][i] = b; R[i][5 + i] = R[5 + i][i] = b; R[5 + i][5 + i] = b
R[3][3] = b; R[4][4] = (1 + b) / 2; R[7][7] = (1 + b) / 2; R[4][7] = R[7][4] = s / 2
rho = [[x / (7 * b + 1) for x in row] for row in R]
pt = [[Fr(0)] * 8 for _ in range(8)]
for x, (a, k) in enumerate(idx):
    for y, (bb, l) in enumerate(idx):
        pt[4 * a + l][4 * bb + k] = rho[x][y]    # ρ^Γ((a,l),(b,k)) = ρ((a,k),(b,l))


def psd_terms(M):
    M = [row[:] for row in M]
    out = []
    while True:
        diag = [(M[i][i], i) for i in range(8) if M[i][i] > 0]
        if not diag:
            assert all(M[i][j] == 0 for i in range(8) for j in range(8)), 'not PSD'
            return out
        _, p = max(diag)
        c = M[p][p]
        u = [M[i][p] / c for i in range(8)]
        out.append((c, u))
        for i in range(8):
            for j in range(8):
                M[i][j] -= c * u[i] * u[j]


def vec_lean(u):
    return '![' + ', '.join(q(x) for x in u) + ']'


rt, ptt = psd_terms(rho), psd_terms(pt)
assert all(c > 0 for c, _ in rt + ptt)

out = []
out.append(phi_def)
out.append('')
out.append('/-- The sum-of-squares certificate: `‖v‖² · w†Φ₂₄(vv†)w` is a nonnegative combination of squared moduli. -/')
out.append('theorem phi24_certificate (v : Fin 2 → ℂ) (w : Fin 4 → ℂ) :\n    ' + lhs + '\n      = ' + rhs + ' := by')
out.append('  simp only [star_add, star_mul\', star_star, star_intCast]')
out.append('  ring')
out.append('')
out.append(f'/-- The {len(rt)} rank-one terms of the witness state ρ (Horodecki, b = 3/5), index `4a + k`. -/')
out.append(f'def rho24Wt : Fin {len(rt)} → ℚ := ![' + ', '.join(q(c) for c, _ in rt) + ']')
out.append(f'def rho24Vec : Fin {len(rt)} → Fin 8 → ℚ := ![' + ',\n  '.join(vec_lean(u) for _, u in rt) + ']')
out.append(f'/-- The {len(ptt)} rank-one terms of its partial transpose. -/')
out.append(f'def pt24Wt : Fin {len(ptt)} → ℚ := ![' + ', '.join(q(c) for c, _ in ptt) + ']')
out.append(f'def pt24Vec : Fin {len(ptt)} → Fin 8 → ℚ := ![' + ',\n  '.join(vec_lean(u) for _, u in ptt) + ']')
out.append('/-- The witness integer matrix `W` (the Choi matrix of `phi24`), index `4a + k`. -/')
out.append('def W24 : Fin 8 → Fin 8 → ℚ := ![' + ',\n  '.join('![' + ', '.join(q(x) for x in row) + ']' for row in W) + ']')
open('generated.lean', 'w').write('\n'.join(out) + '\n')
print('sos terms', len(sos_terms), 'lhs terms', len(lhs_terms), 'rho terms', len(rt), 'pt terms', len(ptt))
print('trace check:', sum(rho[i][i] for i in range(8)), ' tr(rho W) =', sum(rho[y][x] * W[x][y] for x in range(8) for y in range(8)))
