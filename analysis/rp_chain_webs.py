"""Track B: exact reflection-positivity certificates for small Chain Theory webs.

A web is a set of qudits, each the end of one maximally entangled pair (a shared qudit is carried
as one copy per pair, as in the alpha Letter), acted on by distillations (projections onto the
pair ket of two qudits) and local maps. A mirror pairs left qudits with right qudits of equal
dimension; every other qudit is a spectator and is traced out.

For a left observable F and the reflection theta(F (x) 1) = 1 (x) conj(F), the
Osterwalder-Schrader form of the reduced state rho on L (x) R is

    <theta(F) F>_rho = sum rho[(k,l),(i,j)] F[i,k] conj(F[j,l]) = f^dag G f,   f = vec(F),

with G[(j,l),(i,k)] = rho[(k,l),(i,j)]. Reflection positivity is: G Hermitian and G >= 0.
Every entry is an exact Gaussian rational. G >= 0 is certified by an exact LDL^T
(analysis/exact_psd.py) on the real form [[A, -B], [B, A]] of G = A + iB, which returns either
positive pivots with a vanishing remainder (a proof) or a rational witness; each witness is turned
back into a left observable F and re-checked from rho directly.

Run: python3 analysis/rp_chain_webs.py   (standard library only)
"""
from __future__ import annotations

import itertools
import json
import random
import sys
from dataclasses import dataclass, field
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from exact_psd import psd_certificate, rank  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results" / "rp_chain_webs.json"


# ---------------------------------------------------------------- exact Gaussian rationals
@dataclass(frozen=True)
class G:
    re: Fraction = Fraction(0)
    im: Fraction = Fraction(0)

    def __add__(self, o): return G(self.re + o.re, self.im + o.im)
    def __sub__(self, o): return G(self.re - o.re, self.im - o.im)
    def __mul__(self, o): return G(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)
    def conj(self): return G(self.re, -self.im)
    def __bool__(self): return bool(self.re) or bool(self.im)
    def text(self):
        if not self.im: return str(self.re)
        return f"{self.re}{'+' if self.im >= 0 else ''}{self.im}i"


ZERO, ONE, I = G(), G(Fraction(1)), G(Fraction(0), Fraction(1))
def gq(x, y=0): return G(Fraction(x), Fraction(y))


# ---------------------------------------------------------------- sparse exact webs
class Web:
    """A pure state on named qudits, stored sparsely as {basis tuple: amplitude}."""

    def __init__(self):
        self.names: list[str] = []
        self.dims: dict[str, int] = {}
        self.amp: dict[tuple, G] = {(): ONE}
        self.log: list[str] = []

    def _extend(self, pairs, ket: dict[tuple, G]):
        new = {}
        for x, a in self.amp.items():
            for y, b in ket.items():
                new[x + y] = a * b
        self.amp = new
        for n, d in pairs:
            self.names.append(n)
            self.dims[n] = d

    def link(self, a, da, b, db, twist=None):
        """A maximally entangled pair (unnormalized) on the common support; `twist` is a local
        matrix applied at end b afterwards (e.g. i sigma_y for the singlet)."""
        m = min(da, db)
        self._extend([(a, da), (b, db)], {(i, i): ONE for i in range(m)})
        self.log.append(f"link {a}({da})-{b}({db})")
        if twist is not None:
            self.local(b, twist, record=False)
            self.log.append(f"twist at {b}")
        return self

    def apply(self, qudits, M: dict[tuple, dict[tuple, G]]):
        """Apply an operator on the listed qudits, M[out][in]."""
        idx = [self.names.index(q) for q in qudits]
        cols: dict[tuple, list] = {}
        for out, row in M.items():
            for inp, v in row.items():
                if v:
                    cols.setdefault(inp, []).append((out, v))
        new: dict[tuple, G] = {}
        for x, a in self.amp.items():
            t = tuple(x[i] for i in idx)
            for out, v in cols.get(t, []):
                y = list(x)
                for i, s in zip(idx, out):
                    y[i] = s
                y = tuple(y)
                new[y] = new.get(y, ZERO) + v * a
        self.amp = {k: v for k, v in new.items() if v}
        return self

    def distill(self, a, b):
        """Projection onto the (unnormalized) pair ket of a and b on their common support."""
        m = min(self.dims[a], self.dims[b])
        P = {(i, i): {(j, j): ONE for j in range(m)} for i in range(m)}
        self.log.append(f"distill {a},{b}")
        return self.apply([a, b], P)

    def local(self, a, A: list[list[G]], record=True):
        M = {(i,): {(k,): A[i][k] for k in range(len(A[i]))} for i in range(len(A))}
        if record:
            self.log.append(f"local at {a}")
        return self.apply([a], M)


def conjm(A): return [[x.conj() for x in row] for row in A]


# ---------------------------------------------------------------- the OS Gram matrix
def radix_index(vals, dims):
    k = 0
    for v, d in zip(vals, dims):
        k = k * d + v
    return k


def reduced_lr(web: Web, mirror: list[tuple[str, str]]):
    """rho on L (x) R, R in mirror order, as {(row, col): value}, row = (k_L, l_R)."""
    L = [a for a, _ in mirror]
    R = [b for _, b in mirror]
    for a, b in mirror:
        assert web.dims[a] == web.dims[b], f"mirror pairs need equal dimensions: {a},{b}"
    dims = [web.dims[a] for a in L]
    iL = [web.names.index(a) for a in L]
    iR = [web.names.index(b) for b in R]
    iS = [i for i, n in enumerate(web.names) if n not in L and n not in R]
    groups: dict[tuple, dict[tuple, G]] = {}
    for x, a in web.amp.items():
        s = tuple(x[i] for i in iS)
        key = (radix_index([x[i] for i in iL], dims), radix_index([x[i] for i in iR], dims))
        groups.setdefault(s, {})[key] = a
    rho: dict[tuple, G] = {}
    for vec in groups.values():
        items = list(vec.items())
        for r, a in items:
            for c, b in items:
                rho[(r, c)] = rho.get((r, c), ZERO) + a * b.conj()
    D = 1
    for d in dims:
        D *= d
    return rho, D


def gram_from_rho(rho, D):
    """G[(j,l),(i,k)] = rho[(k,l),(i,j)], flattened as row j*D+l, column i*D+k."""
    Gm: dict[tuple, G] = {}
    for ((k, l), (i, j)), v in rho.items():
        if v:
            Gm[(j * D + l, i * D + k)] = v
    return Gm, D * D


def rp_form_from_rho(rho, F):
    """Independent evaluation of sum rho[(k,l),(i,j)] F[i][k] conj(F[j][l])."""
    acc = ZERO
    for ((k, l), (i, j)), v in rho.items():
        acc = acc + v * F[i][k] * F[j][l].conj()
    return acc


def certify(Gm, N, rho, D):
    """Exact RP verdict for the Gram matrix Gm (N x N)."""
    nonherm = [(r, c) for (r, c), v in Gm.items() if v != Gm.get((c, r), ZERO).conj()]
    out = {"gram_size": N}
    if nonherm:
        # the form is not real for some F: find a basis or two-term witness with nonzero imaginary part
        r, c = nonherm[0]
        for coeffs in ([(r, ONE)], [(r, ONE), (c, ONE)], [(r, ONE), (c, I)]):
            F = [[ZERO] * D for _ in range(D)]
            for idx, w in coeffs:
                F[idx // D][idx % D] = F[idx // D][idx % D] + w
            val = rp_form_from_rho(rho, F)
            if val.im:
                break
        out.update(hermitian=False, rp=False, witness_form=val.text(),
                   witness_support=[[idx // D, idx % D] for idx, _ in coeffs])
        return out
    R = [[Fraction(0)] * (2 * N) for _ in range(2 * N)]
    for (r, c), v in Gm.items():
        R[r][c] = v.re
        R[r + N][c + N] = v.re
        R[r + N][c] = v.im
        R[r][c + N] = -v.im
    psd, w, pivots = psd_certificate(R)
    os_dim = rank(R) // 2
    out.update(hermitian=True, rp=bool(psd), os_hilbert_dim=os_dim)
    if psd:
        out["certificate"] = f"LDL^T with {len(pivots)} positive pivots, remainder exactly zero"
    else:
        f = [G(w[q], w[q + N]) for q in range(N)]
        F = [[f[i * D + k] for k in range(D)] for i in range(D)]
        val = rp_form_from_rho(rho, F)
        assert not val.im and val.re < 0, "witness failed independent re-check"
        out.update(witness_form=val.text(),
                   witness_support=sum(1 for x in f if x))
    return out


def analyse(name, web, mirror, expect=None, note=""):
    rho, D = reduced_lr(web, mirror)
    Gm, N = gram_from_rho(rho, D)
    res = certify(Gm, N, rho, D)
    res.update(case=name, mirror=[f"{a}<->{b}" for a, b in mirror], left_dim=D,
               construction=web.log, expected_rp=expect, note=note)
    res["matches_expectation"] = None if expect is None else (res["rp"] == expect)
    return res


def analyse_rho(name, rho, D, expect=None, note=""):
    Gm, N = gram_from_rho(rho, D)
    res = certify(Gm, N, rho, D)
    res.update(case=name, left_dim=D, expected_rp=expect, note=note)
    res["matches_expectation"] = None if expect is None else (res["rp"] == expect)
    return res


# ---------------------------------------------------------------- cases
SIGMA_Y_I = [[ZERO, ONE], [gq(-1), ZERO]]          # i sigma_y = [[0,1],[-1,0]]
PHASE = [[ONE, ZERO], [ZERO, I]]                    # diag(1, i), a fourth-root matching


def single_links():
    out = []
    for d in (2, 3, 4):
        w = Web().link("a", d, "b", d)
        genre = {2: "(2,2) spacetime, readable", 3: "(3,3) strong, dark", 4: "(4,4) Higgs, dark"}[d]
        out.append(analyse(f"pair straight across, {genre}", w, [("a", "b")], True))
    return out


def alpha_object():
    def base():
        w = Web()
        w.link("Q1", 3, "q1", 2).link("Q2", 3, "q2", 2).link("Q3", 3, "f", 2)
        return w
    mirror = [("Q1", "Q2"), ("q1", "q2")]
    cases = [
        analyse("alpha object before the join, mirror = exchange of read links", base(), mirror, True,
                "the unread link Q3-f is a spectator"),
        analyse("alpha object after the join (Q1,Q2 distilled; straddles the mirror)",
                base().distill("Q1", "Q2"), mirror, True),
        analyse("control: join of Q1 with the unread copy Q3 (not mirror-symmetric)",
                base().distill("Q1", "Q3"), mirror, None,
                "breaks the mirror; positivity not predicted either way"),
        analyse("control: alpha object after the join, a matching at q1 only",
                base().distill("Q1", "Q2").local("q1", PHASE), mirror, None,
                "diag(1,i) at q1 without its conjugate at q2"),
        analyse("alpha object after the join, mirrored matching (diag(1,i) at q1, conjugate at q2)",
                base().distill("Q1", "Q2").local("q1", PHASE).local("q2", conjm(PHASE)), mirror, True),
    ]
    return cases


def failures():
    out = [analyse("singlet: qubit pair twisted by i sigma_y", Web().link("a", 2, "b", 2, twist=SIGMA_Y_I),
                   [("a", "b")], False)]
    w = Web().link("La", 2, "Rb", 2).link("Lb", 2, "Ra", 2)
    out.append(analyse("crossed pairs: La-Rb and Lb-Ra", w, [("La", "Ra"), ("Lb", "Rb")], False,
                       "mirror-symmetric as a set of links; coefficient matrix is the swap"))
    w = Web().link("a", 2, "b", 2).local("a", PHASE).local("b", PHASE)
    out.append(analyse("matching U (x) U instead of U (x) conj(U) on a straight pair", w, [("a", "b")], False,
                       "U = diag(1,i): coefficient U U^T = diag(1,-1)"))
    return out


def washed_links():
    """Isotropic (twirled) states rho_F = F P + (1-F)(1-P)/(d^2-1), P the normalized pair projector."""
    out = []
    for d in (2, 3, 4):
        thr = Fraction(1, d * d)
        for Fv, label in [(thr - thr / 10, "just below 1/d^2"), (thr, "at 1/d^2"),
                          (Fraction(1, d), "at 1/d (separability edge)"), (Fraction(1), "pure pair")]:
            rho = {}
            for k, l, i, j in itertools.product(range(d), repeat=4):
                P = Fraction(1, d) if (k == l and i == j) else Fraction(0)
                Id = Fraction(1) if (k == i and l == j) else Fraction(0)
                v = Fv * P + (1 - Fv) * (Id - P) / (d * d - 1)
                if v:
                    rho[(k * d + l, i * d + j)] = G(v)
            # reindex rho to the ((k_L, l_R), (i_L, j_R)) keys used by gram_from_rho
            rho2 = {((r // d, r % d), (c // d, c % d)): v for (r, c), v in rho.items()}
            out.append(analyse_rho(f"washed pair d={d}, F={Fv} ({label})", rho2, d, Fv >= thr,
                                   "predicted: reflection positive iff F >= 1/d^2"))
    return out


def random_webs(seed=20261025, trials=60):
    """Random mirror-symmetric webs, and controls that break the symmetry in one step."""
    rng = random.Random(seed)

    def rand_matrix(d):
        return [[gq(rng.randint(-2, 2), rng.randint(-2, 2)) for _ in range(d)] for _ in range(d)]

    def build(break_kind=None):
        k = 2 if break_kind == "one_sided_distill" else rng.choice([1, 2])  # left qudits in the mirror
        dims = [rng.choice([2, 3]) for _ in range(k)]
        while k == 2 and dims[0] * dims[1] > 9:
            dims = [rng.choice([2, 3]) for _ in range(k)]
        w = Web()
        mirror = []
        # each mirrored qudit pair: either a pair straight across, or each linked to a mirrored spectator
        for a in range(k):
            L, R = f"L{a}", f"R{a}"
            mirror.append((L, R))
            if rng.random() < 0.5:
                w.link(L, dims[a], R, dims[a])
            else:
                ds = rng.choice([2, 3])
                w.link(L, dims[a], f"SL{a}", ds).link(R, dims[a], f"SR{a}", ds)
        # mirrored or straddling acts
        for _ in range(rng.randint(1, 3)):
            kind = rng.choice(["local", "straddle", "pair"])
            a = rng.randrange(k)
            if kind == "local":
                A = rand_matrix(dims[a])
                w.local(f"L{a}", A).local(f"R{a}", conjm(A))
            elif kind == "straddle":
                w.distill(f"L{a}", f"R{a}")
            elif kind == "pair" and k == 2:
                w.distill("L0", "L1").distill("R0", "R1")
        if break_kind == "unmirrored_local":
            a = rng.randrange(k)
            A = rand_matrix(dims[a])
            w.local(f"L{a}", A).local(f"R{a}", A)
        elif break_kind == "one_sided_distill" and k == 2:
            w.distill("L0", "L1")
        elif break_kind == "one_sided_local":
            a = rng.randrange(k)
            w.local(f"L{a}", rand_matrix(dims[a]))
        return w, mirror

    mirrored, controls = [], []
    for t in range(trials):
        w, m = build()
        if not w.amp:
            continue
        mirrored.append(analyse(f"random mirrored web {t}", w, m, True))
    for t in range(trials):
        kind = ["unmirrored_local", "one_sided_distill", "one_sided_local"][t % 3]
        w, m = build(kind)
        if not w.amp:
            continue
        controls.append(analyse(f"control {t}: {kind}", w, m, None))
    return mirrored, controls


def main():
    sections = {
        "single_links": single_links(),
        "alpha_object": alpha_object(),
        "failures": failures(),
        "washed_links": washed_links(),
    }
    mirrored, controls = random_webs()
    sections["random_mirrored"] = mirrored
    sections["random_controls"] = controls
    summary = {
        "random_mirrored_total": len(mirrored),
        "random_mirrored_rp": sum(r["rp"] for r in mirrored),
        "random_controls_total": len(controls),
        "random_controls_rp": sum(r["rp"] for r in controls),
        "random_controls_violations_by_kind": {
            k: [sum(1 for r in controls if k in r["case"] and not r["rp"]),
                sum(1 for r in controls if k in r["case"])]
            for k in ("unmirrored_local", "one_sided_distill", "one_sided_local")},
        "expectation_mismatches": [r["case"] for sec in sections.values() for r in sec
                                   if r.get("matches_expectation") is False],
    }
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text(json.JSONEncoder(indent=1).encode({"summary": summary, **sections}) + "\n")
    for name in ("single_links", "alpha_object", "failures", "washed_links"):
        print(f"== {name}")
        for r in sections[name]:
            tag = "RP " if r["rp"] else "NOT"
            extra = (f"OS dim {r['os_hilbert_dim']}" if r.get("os_hilbert_dim") is not None else "") + \
                    (f"  witness form {r['witness_form']}" if "witness_form" in r else "")
            ok = {True: "ok", False: "MISMATCH", None: "-"}[r["matches_expectation"]]
            print(f"  [{tag}] [{ok:>8}] {r['case']}  (Gram {r['gram_size']})  {extra}")
    print("== summary")
    print(json.JSONEncoder(indent=1).encode(summary))


if __name__ == "__main__":
    main()
