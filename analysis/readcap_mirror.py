"""Step 1: does "readable" mean "passes the mirror test"?

Three parts, each written to results/readcap_mirror.json.

A. The dictionary (Exact; checked numerically here, proved in the note).
   Vectorize an operator W on C^d1 (x) C^d2 as a state on (ket a, ket k | bra b, bra l).
   Mirror M1 reflects the kets onto the bras. Mirror M2 instead puts (ket a, bra l) on the left and
   (bra b, ket k) on the right. The Osterwalder-Schrader form of a coefficient matrix C is
   rpForm(C, F) = tr(C^H F C F^H) (lean/ChainRP.lean, rpForm_eq_trace). For Hermitian C its form
   matrix has eigenvalues lambda_i lambda_j, so the form is nonnegative for every F exactly when C is
   semidefinite (C >= 0 or C <= 0). The M1 coefficient matrix is W and the M2 one is W^Gamma.
   Hence: W >= 0 <=> M1-reflection positive with tr W >= 0; W^Gamma >= 0 <=> the same for M2; and a map
   is decomposable <=> its Choi matrix splits as an M1-positive plus an M2-positive part.

B. Two naive versions of the conjecture.
   B1. State level: mirrored reads (Phi (x) conj Phi) keep every RP state RP, for every linear Phi,
       dark or not (so state-level RP cannot see the read cap; this explains Track B).
   B2. A single read as a coupling across the mirror: Hilbert-Schmidt positivity <X, Phi(X)> >= 0
       fails even for completely positive reads such as X -> s_x X s_x.

C. A darkness atlas. For each link type, random boundary positive maps W = H - mu(H) 1, with H from the
   Gaussian unitary ensemble and mu(H) the minimum of <x (x) y|H|x (x) y> over unit product vectors. The
   darkness margin delta(W) = min{tr(rho W) : rho >= 0, rho^Gamma >= 0, tr rho = 1}, normalized by
   tr W, is 0 for decomposable boundary maps and negative exactly for dark ones (cone duality).
   Also the margins of the explicit dark maps (Choi, extended Choi, Phi_24).

Run: <venv with cvxpy and Clarabel>/bin/python analysis/readcap_mirror.py
"""
from __future__ import annotations

import json
import time
from datetime import datetime, timezone
from pathlib import Path

import cvxpy as cp
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
RNG = np.random.default_rng(20261026)


# ---------- basic objects ----------

def ptranspose(W, d1, d2):
    """Partial transpose on the second factor: W^G[(a,l),(b,k)] = W[(a,k),(b,l)]."""
    return W.reshape(d1, d2, d1, d2).transpose(0, 3, 2, 1).reshape(d1 * d2, d1 * d2)


def choi(phi, d1, d2):
    """Choi matrix C[(a,k),(b,l)] = Phi(E_ab)[k,l]."""
    C = np.zeros((d1 * d2, d1 * d2), dtype=complex)
    for a in range(d1):
        for b in range(d1):
            E = np.zeros((d1, d1), dtype=complex)
            E[a, b] = 1
            C.reshape(d1, d2, d1, d2)[a, :, b, :] = phi(E)
    return C


def gue(n):
    A = RNG.normal(size=(n, n)) + 1j * RNG.normal(size=(n, n))
    return (A + A.conj().T) / 2


def rp_form_matrix(C):
    """Hermitian matrix G with rpForm(C, F) = vec(F)^H G vec(F), rpForm = tr(C^H F C F^H)."""
    n = C.shape[0]
    G = np.zeros((n * n, n * n), dtype=complex)
    for p in range(n * n):
        Fp = np.zeros((n, n), dtype=complex)
        Fp.flat[p] = 1
        for q in range(n * n):
            Fq = np.zeros((n, n), dtype=complex)
            Fq.flat[q] = 1
            # sesquilinear form B(F, F') = tr(C^H F' C F^H), conjugate-linear in F
            G[p, q] = np.trace(C.conj().T @ Fq @ C @ Fp.conj().T)
    return G


# ---------- Part A ----------

def part_a(samples=40):
    rows = []
    for d1, d2 in [(2, 2), (2, 3), (3, 2)]:
        for _ in range(samples // 3):
            kind = RNG.integers(3)
            if kind == 0:     # positive semidefinite
                B = RNG.normal(size=(d1 * d2, d1 * d2)) + 1j * RNG.normal(size=(d1 * d2, d1 * d2))
                W = B @ B.conj().T
            elif kind == 1:   # PPT-type: partial transpose of a PSD matrix
                B = RNG.normal(size=(d1 * d2, d1 * d2)) + 1j * RNG.normal(size=(d1 * d2, d1 * d2))
                W = ptranspose(B @ B.conj().T, d1, d2)
            else:
                W = gue(d1 * d2)
            for mirror, C in (("M1", W), ("M2", ptranspose(W, d1, d2))):
                G = rp_form_matrix(C)
                herm_err = float(np.abs(G - G.conj().T).max())
                g = np.linalg.eigvalsh((G + G.conj().T) / 2)
                lam = np.linalg.eigvalsh(C)
                semidef = bool(lam.min() >= -1e-9 or lam.max() <= 1e-9)
                rp = bool(g.min() >= -1e-8 * max(1.0, abs(g).max()))
                prod = np.sort(np.outer(lam, lam).ravel())
                rows.append({"type": [d1, d2], "mirror": mirror, "kind": int(kind),
                             "semidefinite": semidef, "rp": rp, "agree": semidef == rp,
                             "form_eigs_are_products": bool(np.allclose(np.sort(g), prod, atol=1e-8 * max(1, abs(prod).max()))),
                             "form_hermitian_err": herm_err})
    return {
        "checked": len(rows),
        "rp_iff_semidefinite_all": all(r["agree"] for r in rows),
        "form_eigenvalues_are_products_all": all(r["form_eigs_are_products"] for r in rows),
        "max_form_hermiticity_error": max(r["form_hermitian_err"] for r in rows),
        "counts": {m: {"rp": sum(r["rp"] for r in rows if r["mirror"] == m),
                       "total": sum(r["mirror"] == m for r in rows)} for m in ("M1", "M2")},
    }


# ---------- Part B ----------

def mixed_rp_matrix(rho, d):
    """G with tr(rho (F (x) conj F)) = conj(vec F)^T G vec F, mirror pairs (i, i-bar)."""
    R = rho.reshape(d, d, d, d)          # R[j, l, i, k] = rho[(j,l),(i,k)]
    G = np.zeros((d * d, d * d), dtype=complex)
    for k in range(d):
        for l in range(d):
            for i in range(d):
                for j in range(d):
                    G[k * d + l, i * d + j] = R[j, l, i, k]
    return G


def choi_map(X):
    Y = -X.copy()
    for i in range(3):
        Y[i, i] = X[i, i] + X[(i + 1) % 3, (i + 1) % 3]
    return Y


def part_b():
    d = 3
    omega = np.eye(d).reshape(-1) / np.sqrt(d)
    rho0 = np.outer(omega, omega.conj()).astype(complex)

    def mirrored(phi):
        """(Phi (x) conj Phi)(rho0), conj Phi(X) = conj(Phi(conj X))."""
        out = np.zeros_like(rho0)
        R0 = rho0.reshape(d, d, d, d)
        for a in range(d):
            for b in range(d):
                for c in range(d):
                    for e in range(d):
                        coef = R0[a, c, b, e]
                        if coef == 0:
                            continue
                        Ea = np.zeros((d, d), complex); Ea[a, b] = 1
                        Ec = np.zeros((d, d), complex); Ec[c, e] = 1
                        out += coef * np.kron(phi(Ea), np.conj(phi(np.conj(Ec))))
        return out

    M = RNG.normal(size=(d * d, d * d)) + 1j * RNG.normal(size=(d * d, d * d))
    def rand_linear(X):
        return (M @ X.reshape(-1)).reshape(d, d)
    cases = {"identity": lambda X: X, "transpose": lambda X: X.T, "choi_map_dark": choi_map,
             "random_linear_not_positive": rand_linear}
    b1 = {}
    for name, phi in cases.items():
        rho = mirrored(phi)
        G = mixed_rp_matrix(rho, d)
        g = np.linalg.eigvalsh((G + G.conj().T) / 2)
        b1[name] = {"rp_min_eig": float(g.min()), "rp_hermitian_err": float(np.abs(G - G.conj().T).max()),
                    "state_min_eig": float(np.linalg.eigvalsh((rho + rho.conj().T) / 2).min()),
                    "reflection_positive": bool(g.min() >= -1e-9)}
    sx = np.array([[0, 1], [1, 0]], complex)
    sz = np.array([[1, 0], [0, -1]], complex)
    b2 = {"read": "X -> s_x X s_x (completely positive)", "X": "s_z",
          "hs_pairing": float(np.real(np.trace(sz.conj().T @ (sx @ sz @ sx))))}
    return {"B1_mirrored_reads": b1, "B2_single_coupling": b2}


# ---------- Part C ----------

def product_min(H, d1, d2, starts=48, iters=200):
    """min <x (x) y|H|x (x) y> over unit x, y by alternating eigen-steps from many starts."""
    T = H.reshape(d1, d2, d1, d2)
    best = np.inf
    for _ in range(starts):
        y = RNG.normal(size=d2) + 1j * RNG.normal(size=d2)
        y /= np.linalg.norm(y)
        val = np.inf
        for _ in range(iters):
            Mx = np.einsum("k,akbl,l->ab", y.conj(), T, y)
            w, V = np.linalg.eigh((Mx + Mx.conj().T) / 2)
            x = V[:, 0]
            My = np.einsum("a,akbl,b->kl", x.conj(), T, x)
            w2, V2 = np.linalg.eigh((My + My.conj().T) / 2)
            y = V2[:, 0]
            new = w2[0]
            if val - new < 1e-14:
                val = new
                break
            val = new
        best = min(best, val)
    return float(best)


def darkness(W, d1, d2):
    n = d1 * d2
    C = W / np.real(np.trace(W))
    rho = cp.Variable((n, n), hermitian=True)
    cons = [rho >> 0, cp.partial_transpose(rho, [d1, d2], 1) >> 0, cp.real(cp.trace(rho)) == 1]
    prob = cp.Problem(cp.Minimize(cp.real(cp.trace(rho @ C))), cons)
    prob.solve(solver="CLARABEL")
    return float(prob.value)


def part_c(samples, eps=1e-6, tol=1e-6):
    atlas = {}
    for (d1, d2), N in samples.items():
        t0 = time.time()
        raw, shifted = [], []
        for _ in range(N):
            H = gue(d1 * d2)
            H /= np.linalg.norm(H)
            mu = product_min(H, d1, d2)
            n = d1 * d2
            W = H - mu * np.eye(n)
            raw.append(darkness(W, d1, d2))
            shifted.append(darkness(W + eps * np.eye(n), d1, d2))
        raw, shifted = np.array(raw), np.array(shifted)
        dark = shifted < -tol
        atlas[f"{d1}x{d2}"] = {
            "samples": N, "dark": int(dark.sum()), "fraction_dark": float(dark.mean()),
            "delta_min": float(raw.min()), "delta_median": float(np.median(raw)),
            "delta_min_shifted": float(shifted.min()),
            "dark_deltas_quantiles": [float(q) for q in np.quantile(shifted[dark], [0, 0.5, 1])] if dark.any() else [],
            "seconds": round(time.time() - t0, 1),
        }
        print(f"{d1}x{d2}: {int(dark.sum())}/{N} dark, delta min {raw.min():.3e}", flush=True)
    return atlas


def part_c2(scales=(0.01, 0.03, 0.1, 0.3, 1.0), N=60, eps=1e-6, tol=1e-6):
    """How wide is the dark region around a known dark map? W_t = C + t ||C|| G, pushed back onto the
    boundary of the positive cone (W_t - mu(W_t) 1), for random unit GUE directions G."""
    cert = json.loads((ROOT / "results/dark24_certificate.json").read_text())
    from fractions import Fraction
    W24 = np.array([[float(Fraction(x)) for x in row] for row in cert["W"]]).astype(complex)
    bases = {"choi_3x3": (choi(choi_map, 3, 3), 3, 3), "phi24_2x4": (W24, 2, 4)}
    out = {}
    for name, (C0, d1, d2) in bases.items():
        n = d1 * d2
        C0 = C0 / np.linalg.norm(C0)
        rows = {}
        for t in scales:
            dark = 0
            for _ in range(N):
                G = gue(n)
                G /= np.linalg.norm(G)
                W = C0 + t * G
                W = W - product_min(W, d1, d2) * np.eye(n)
                if darkness(W + eps * np.eye(n), d1, d2) < -tol:
                    dark += 1
            rows[str(t)] = {"samples": N, "dark": dark, "fraction_dark": dark / N}
            print(f"{name} t={t}: {dark}/{N} dark", flush=True)
        out[name] = rows
    return out


def explicit_margins():
    out = {}
    out["choi_3x3"] = darkness(choi(choi_map, 3, 3), 3, 3)
    J = np.eye(4)[:, :3]
    out["choi_extended_3x4"] = darkness(choi(lambda X: J @ choi_map(X) @ J.T, 3, 4), 3, 4)
    out["choi_extended_4x4"] = darkness(choi(lambda X: J @ choi_map(J.T @ X @ J) @ J.T, 4, 4), 4, 4)
    cert = json.loads((ROOT / "results/dark24_certificate.json").read_text())
    from fractions import Fraction
    W24 = np.array([[float(Fraction(x)) for x in row] for row in cert["W"]])
    out["phi24_2x4"] = darkness(W24.astype(complex), 2, 4)
    return out


def main():
    t0 = time.time()
    result = {"checked_at": datetime.now(timezone.utc).isoformat(), "seed": 20261026}
    result["A_dictionary"] = part_a()
    print("A:", result["A_dictionary"]["rp_iff_semidefinite_all"], flush=True)
    result["B_naive_versions"] = part_b()
    print("B:", json.dumps(result["B_naive_versions"])[:300], flush=True)
    result["D_explicit_margins"] = explicit_margins()
    print("D:", result["D_explicit_margins"], flush=True)
    samples = {(2, 2): 300, (2, 3): 300, (3, 2): 300, (2, 4): 300, (3, 3): 300, (3, 4): 200, (4, 4): 150}
    result["C_atlas"] = part_c(samples)
    result["C2_dark_neighbourhoods"] = part_c2()
    result["C_atlas_protocol"] = ("H from the Gaussian unitary ensemble, normalized; mu(H) by alternating eigen-steps "
                                  "from 48 random starts; W = H - mu 1; delta by Clarabel on the PPT cone; a map counts "
                                  "as dark if delta(W + 1e-6 * 1) < -1e-6 (guards against an over-estimated mu).")
    result["seconds"] = round(time.time() - t0, 1)
    out = ROOT / "results/readcap_mirror.json"
    out.write_text(json.JSONEncoder(indent=1).encode(result) + "\n")
    print("written", out)


if __name__ == "__main__":
    main()
