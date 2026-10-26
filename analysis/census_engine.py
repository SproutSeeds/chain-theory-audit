"""A line-by-line Python port of Part 1 of ChainAlpha.lean, with a switch for every definitional
alternative the author lists.

Ground truth for the port is the author's own Lean file: `papers/alpha/lean/mutations.py` in
github.com/alexwg/chain-theory perturbs the definitions one at a time and prints the readout.
`analysis/trials_census.py` checks this port against those readouts (singly and in pairs) before
using it.

A readout is returned exactly, as ({radicand: count}, denominator), meaning
sum(count * sqrt(radicand)) / denominator.

Switches (defaults reproduce the Letter):
  read_end      'rule' | 'swapped'                 reads_at_qubit
  wx            'read' | 'far'                     X_at_far_end
  kof           'std' | 'letters_sit' | 'swapped'  X_where_letters_sit, X_Y_factors_swapped
  wy            'moved' | 'center'                 Y_at_center
  moved         'set' | 'per_letter'               moved_per_letter
  copies        'one' | 'separate'                 copies_separate
  survival      'own_sign' | 'ignore_sign'         survival_ignores_own_sign
  comm          'diff' | 'sum' | 'both' | 'none'   commutators_keep_sums / _keep_both, no_commutator_records
  comm_reads    'carry' | 'none'                   commutator_records_carry_no_reads
  unread        'traceless' | 'full'               register_full_unread
  recset        'all' | 'drop_fixed' | 'drop_even' drop_fixed, drop_even
  weight        'sqrt' | 'born' | 'none'           born_weights; Letter Table S5 "no weights"
  norm          'N' | 'records'                    Letter Table S5 "normalized by the 172 records"
  exch          2 | 1                              exch_shift1 (slot s -> s+exch mod 4)
Configuration: center dimension c, far dimension e of the two read links, and the far dimensions
of the unread links (Letter Table S2).
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache

DEFAULTS = dict(read_end="rule", wx="read", kof="std", wy="moved", moved="set", copies="one",
                survival="own_sign", comm="diff", comm_reads="carry", unread="traceless",
                recset="all", weight="sqrt", norm="N", exch=2)

# ------------------------------------------------------------------ Part 0: exact arithmetic
def rank(rows):
    rows = [list(r) for r in rows]
    rk = 0
    while True:
        rows = [r for r in rows if any(r)]
        if not rows:
            return rk
        r, rest = rows[0], rows[1:]
        c = next(i for i, x in enumerate(r) if x)
        a = r[c]
        rows = [[a * x - s[c] * y for x, y in zip(s, r)] for s in rest]
        rk += 1


def mmul(a, b):
    k = len(b[0])
    return [[sum(row[i] * b[i][j] for i in range(len(row))) for j in range(k)] for row in a]


def msub(a, b):
    return [[x - y for x, y in zip(r, s)] for r, s in zip(a, b)]


def pair(a, b):  # trace(a^T b)
    return sum(a[i][j] * b[i][j] for i in range(len(a)) for j in range(len(a[0])))


# ------------------------------------------------------------------ Part 1: the definitions
def pair_ket(dA, dB, i, j):
    return 1 if (i == j and i < min(dA, dB)) else 0


def fixes_far(dA, dB):
    return rank([[pair_ket(dA, dB, i, j) for j in range(dB)] for i in range(dA)]) == dB


def read_end(dA, dB, mode):
    if mode == "rule":
        return dA if fixes_far(dA, dB) else dB
    return dB if fixes_far(dA, dB) else dA


def far_end(dA, dB, mode):
    if mode == "rule":
        return dB if fixes_far(dA, dB) else dA
    return dA if fixes_far(dA, dB) else dB


@lru_cache(maxsize=None)
def traceless_basis(d):
    pairs = [(i, j) for i in range(d) for j in range(d) if i < j]
    sym = [[[1 if (a, b) in ((p, q), (q, p)) else 0 for b in range(d)] for a in range(d)] for p, q in pairs]
    anti = [[[1 if (a, b) == (p, q) else -1 if (a, b) == (q, p) else 0 for b in range(d)] for a in range(d)]
            for p, q in pairs]
    diag = [[[1 if (a == b and a < k) else -k if (a == b and a == k) else 0 for b in range(d)] for a in range(d)]
            for k in range(1, d)]
    return tuple(tuple(tuple(r) for r in m) for m in sym + anti + diag)


def slot_end(s):
    return s % 2


def slot_basis(dA, dB, s):
    return traceless_basis(dA if slot_end(s) == 0 else dB)


def exch_slot(s, e):
    return (s + e) % 4


def exch_assign(a, e):
    return tuple(a[exch_slot(s, e)] for s in range(4))


def key(a):
    acc = 0
    for s in range(4):
        acc = acc * 100 + (0 if a[s] is None else a[s] + 1)
    return acc


def letter_slots(a):
    return [s for s in range(4) if a[s] is not None]


def products(dA, dB):
    out = []
    for s1 in range(4):
        for s2 in range(s1 + 1, 4):
            for i1 in range(len(slot_basis(dA, dB, s1))):
                for i2 in range(len(slot_basis(dA, dB, s2))):
                    out.append(tuple(i1 if t == s1 else i2 if t == s2 else None for t in range(4)))
    return out


def coeff_of(f, a):
    return sum(c for c, b in f if b == a)


def parity(f, e):
    if all(coeff_of(f, exch_assign(a, e)) == c for c, a in f):
        return 1
    if all(coeff_of(f, exch_assign(a, e)) == -c for c, a in f):
        return -1
    return 0


def weyl_is_sign(d):
    return all(((2 * j) + (2 * d) - (2 * ((j + 1) % d))) % (2 * d) == d for j in range(d))


def order_sign(d):
    return -1 if weyl_is_sign(d) else 1


def coeff_on(basis, m, k):
    return pair(basis[k], m) // pair(basis[k], basis[k])


def comm_at(dA, dB, i, j, s):
    b = slot_basis(dA, dB, s)
    c = msub(mmul(b[i], b[j]), mmul(b[j], b[i]))
    return [(coeff_on(b, c, k), tuple(k if t == s else None for t in range(4)))
            for k in range(len(b)) if coeff_on(b, c, k) != 0]


def comm_candidates(dA, dB, i, j):
    c1, c3 = comm_at(dA, dB, i, j, 1), comm_at(dA, dB, i, j, 3)
    return [c1 + c3, c1 + [(-c, a) for c, a in c3]]


def same_end(f):
    s = letter_slots(f[0][1])
    return len(s) == 2 and slot_end(s[0]) == slot_end(s[1])


@dataclass(frozen=True)
class Rec:
    form: tuple
    sign: int
    reads: tuple | None


def commutator_recs(dA, dB, e, comm, comm_reads):
    if comm == "none" or not weyl_is_sign(dB):
        return []
    nb = len(slot_basis(dA, dB, 1))
    out = []
    for i in range(nb):
        for j in range(i + 1, nb):
            for f, g in zip(comm_candidates(dA, dB, i, j), comm_candidates(dA, dB, j, i)):
                p = parity(f, e)
                keep = {"diff": p == order_sign(dB), "sum": p == -order_sign(dB), "both": True}[comm]
                if keep:
                    out.append(Rec(tuple(f), order_sign(dB), tuple(g) if comm_reads == "carry" else None))
    return out


@lru_cache(maxsize=None)
def recs(dA, dB, e, comm, comm_reads, recset):
    ps = products(dA, dB)

    def mk(f):
        return Rec(tuple(f), 1, tuple((c, exch_assign(a, e)) for c, a in f) if same_end(f) else None)

    fixed = [mk([(1, p)]) for p in ps if exch_assign(p, e) == p]
    reps = [p for p in ps if key(p) < key(exch_assign(p, e))]
    odd = [mk([(1, p), (-1, exch_assign(p, e))]) for p in reps]
    even = [mk([(1, p), (1, exch_assign(p, e))]) for p in reps]
    if recset == "drop_fixed":
        fixed = []
    if recset == "drop_even":
        even = []
    return tuple(odd + even + fixed + commutator_recs(dA, dB, e, comm, comm_reads))


# ------------------------------------------------------------------ the two exchanges
# Qudits: the center 0 (or copies 100, 101 when the copies are separate qudits), far ends 1 and 2.
def slot_qudit(s, copies):
    if slot_end(s) == 0:
        return 0 if copies == "one" else 100 + s // 2
    return 1 if s // 2 == 0 else 2


def link_swap(q, copies):
    if q == 1: return 2
    if q == 2: return 1
    if copies == "separate":
        if q == 100: return 101
        if q == 101: return 100
    return q  # the shared center is fixed (read1.1 = read2.1 = 0)


def occupies(a, copies):
    return [slot_qudit(s, copies) for s in letter_slots(a)]


def same_set(xs, ys):
    return all(x in ys for x in xs) and all(y in xs for y in ys)


def moved(f, copies, mode):
    a = f[0][1]
    occ = occupies(a, copies)
    if mode == "set":
        return not same_set([link_swap(q, copies) for q in occ], occ)
    return any(link_swap(q, copies) != q for q in occ)


def same_form(f, g):
    return all(coeff_of(g, a) == c for c, a in f) and all(coeff_of(f, a) == c for c, a in g)


def survives(r, image, survival):
    if image is None:
        return False
    target = r.form if survival == "ignore_sign" else tuple((r.sign * c, a) for c, a in r.form)
    return same_form(image, target)


def sig_x(r, survival):
    return -1 if survives(r, r.reads, survival) else 1


def sig_y(r, e, copies, moved_mode, survival):
    image = tuple((c, exch_assign(a, e)) for c, a in r.form) if moved(r.form, copies, moved_mode) else None
    return -1 if survives(r, image, survival) else 1


# ------------------------------------------------------------------ the weight law
def w_y(r, copies, dim_center, dim_far, wy):
    a = r.form[0][1]

    def dim(q):
        return dim_center if (q == 0 or q >= 100) else dim_far

    def at(e):
        for s in letter_slots(a):
            if slot_end(s) == e and link_swap(slot_qudit(s, copies), copies) != slot_qudit(s, copies):
                return dim_center if wy == "center" else dim(slot_qudit(s, copies))
        return 1
    return at(0) * at(1)


def k_of(r, x, sw, dim_center, dim_far):
    sx = sig_x(r, sw["survival"]) == -1
    sy = sig_y(r, sw["exch"], sw["copies"], sw["moved"], sw["survival"]) == -1
    if sw["kof"] == "swapped":
        return (2 if sx else 1) * (x if sy else 1)
    if sw["kof"] == "letters_sit":
        xf = (2 if all(slot_end(s) == 1 for s in letter_slots(r.form[0][1])) else x) if sx else 1
    else:
        xf = x if sx else 1
    return xf * (w_y(r, sw["copies"], dim_center, dim_far, sw["wy"]) if sy else 1)


# ------------------------------------------------------------------ the readout
def readout_dim(c, e, unread_far, unread_mode):
    n = (c * e) ** 2 * (c * e) ** 2
    for f in unread_far:
        n *= (c * f) ** 2 if unread_mode == "full" else (c * c - 1) * (f * f - 1)
    return n


def numerator(c, e, **switches):
    """The trace of the dressed insertion, as {radicand: count}, and the record count."""
    sw = dict(DEFAULTS, **switches)
    dA, dB = read_end(c, e, sw["read_end"]), far_end(c, e, sw["read_end"])
    x = read_end(c, e, sw["read_end"]) if sw["wx"] == "read" else far_end(c, e, sw["read_end"])
    counts: dict[int, int] = {}
    rs = recs(dA, dB, sw["exch"], sw["comm"], sw["comm_reads"], sw["recset"])
    for r in rs:
        k = k_of(r, x, sw, c, e)
        k = {"sqrt": k, "born": k * k, "none": 1}[sw["weight"]]
        counts[k] = counts.get(k, 0) + 1
    return counts, len(rs)


def readout(c=3, e=2, unread_far=(2,), **switches):
    sw = dict(DEFAULTS, **switches)
    counts, nrec = numerator(c, e, **switches)
    den = readout_dim(c, e, unread_far, sw["unread"]) if sw["norm"] == "N" else nrec
    return dict(sorted(counts.items())), den


def value(counts, den):
    return sum(n * k ** 0.5 for k, n in counts.items()) / den


if __name__ == "__main__":
    print(readout())   # expect ({1: 79, 2: 48, 3: 42, 6: 3}, 31104)
