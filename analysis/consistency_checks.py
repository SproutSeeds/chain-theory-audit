"""Lane 1c: internal consistency of the photon identification, using only the theory's own numbers.

Exact rational arithmetic throughout. Writes results/consistency_checks.json.

Setting, from the alpha Letter (Secs. S3, S10): the identification algebra of the (2,3) link is
s(u(2) + u(3)), block-diagonal on C^2 (+) C^3 (qubit indices 0,1; qutrit 2,3,4), acting on the link
C^2 (x) C^3 as xi1 (x) 1 + 1 (x) xi2. The pair ket is |00> + |11> (qubit (x) qutrit, unnormalized).
SU(2) acts at the qubit end and SU(3) at the qutrit end; Y = diag(1/2, 1/2; -1/3, -1/3, -1/3) is the
hypercharge of the SU(5) embedding; Q = 6iY is the Letter's central generator.

Checks
  1. Recompute the stabilizer of the pair ket (Letter Theorem S3): dimension 4, center the line
     of U = i diag(1, 1; -1, -1, 0).
  2. Decompose U into hypercharge, weak isospin T3 and the color direction diag(0,0;1,1,-2).
  3. Electric charge Q_em = n.T + Y (any weak-isospin direction n): does it leave the pair-ket ray
     invariant? And the electric charges of the two terms of the pair ket.
  4. The weak angle: with the compendium's cos^2(theta_W) = 1/2, alpha_em = alpha_Y cos^2(theta_W),
     the 1/alpha_em implied by reading the readout as a hypercharge-type coupling, for the standard
     normalizations of hypercharge.
  5. The running ladder alpha_cap(k) = numerator / 319^k (compendium p. 343) against the Letter's
     numerator / 31104.
"""
from __future__ import annotations

import json
from fractions import Fraction as Fr
from pathlib import Path

from mpmath import mp, mpf, sqrt

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results" / "consistency_checks.json"
mp.dps = 30
I = complex(0, 1)

# ------------------------------------------------------------------ exact Gaussian-rational matrices
# A matrix is a dict {(r, c): (re, im)} of Fractions; here every generator is real or i * real.


def E(a, b, n=5):
    return {(a, b): Fr(1)}


def comb(*terms):
    """Sum of (coefficient, matrix) with real Fraction coefficients."""
    out = {}
    for c, m in terms:
        for k, v in m.items():
            out[k] = out.get(k, Fr(0)) + c * v
    return {k: v for k, v in out.items() if v}


# The Letter's basis (Sec. S10): the real part and the imaginary part of each anti-Hermitian generator.
# Each generator is (real matrix R, imaginary matrix J), meaning R + iJ.
def gen(R=None, J=None):
    return (R or {}, J or {})


BASIS = [
    gen(R=comb((1, E(0, 1)), (-1, E(1, 0)))),                       # e1
    gen(J=comb((1, E(0, 1)), (1, E(1, 0)))),                        # e2
    gen(J=comb((1, E(0, 0)), (-1, E(1, 1)))),                       # e3
    gen(R=comb((1, E(2, 3)), (-1, E(3, 2)))),                       # e4
    gen(R=comb((1, E(2, 4)), (-1, E(4, 2)))),                       # e5
    gen(R=comb((1, E(3, 4)), (-1, E(4, 3)))),                       # e6
    gen(J=comb((1, E(2, 3)), (1, E(3, 2)))),                        # e7
    gen(J=comb((1, E(2, 4)), (1, E(4, 2)))),                        # e8
    gen(J=comb((1, E(3, 4)), (1, E(4, 3)))),                        # e9
    gen(J=comb((1, E(2, 2)), (-1, E(3, 3)))),                       # e10
    gen(J=comb((1, E(3, 3)), (-1, E(4, 4)))),                       # e11
    gen(J=comb((3, E(0, 0)), (3, E(1, 1)), (-2, E(2, 2)), (-2, E(3, 3)), (-2, E(4, 4)))),  # e12 = Q
]


def act_on_link(g, v):
    """(xi1 (x) 1 + 1 (x) xi2) v on C^2 (x) C^3, index q*3 + t; xi = R + iJ; v complex as (re, im)."""
    R, J = g
    out = [[Fr(0), Fr(0)] for _ in range(6)]
    for q in range(2):
        for t in range(3):
            re, im = v[q * 3 + t]
            if not re and not im:
                continue
            # qubit block: indices 0,1
            for q2 in range(2):
                r, j = R.get((q2, q), Fr(0)), J.get((q2, q), Fr(0))
                out[q2 * 3 + t][0] += r * re - j * im
                out[q2 * 3 + t][1] += r * im + j * re
            # qutrit block: indices 2,3,4
            for t2 in range(3):
                r, j = R.get((2 + t2, 2 + t), Fr(0)), J.get((2 + t2, 2 + t), Fr(0))
                out[q * 3 + t2][0] += r * re - j * im
                out[q * 3 + t2][1] += r * im + j * re
    return out


PAIR = [[Fr(1), Fr(0)] if k in (0, 4) else [Fr(0), Fr(0)] for k in range(6)]  # |00> + |11>


def nullspace(rows, ncols):
    """Exact null space of a list of rows (Fractions)."""
    M = [list(r) for r in rows]
    piv_cols, r = [], 0
    for c in range(ncols):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        M[r] = [x / M[r][c] for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv_cols.append(c)
        r += 1
    free = [c for c in range(ncols) if c not in piv_cols]
    basis = []
    for f in free:
        v = [Fr(0)] * ncols
        v[f] = Fr(1)
        for i, c in enumerate(piv_cols):
            v[c] = -M[i][f]
        basis.append(v)
    return basis, len(piv_cols)


def check_stabilizer():
    cols = [act_on_link(g, PAIR) for g in BASIS]          # 12 columns, each 6 complex entries
    rows = [[cols[k][e][part] for k in range(12)] for e in range(6) for part in (0, 1)]
    null, rk = nullspace(rows, 12)
    # center of the stabilizer: the diagonal (Cartan) elements in it that commute with the rest;
    # the Letter's U = i diag(1,1;-1,-1,0) = i*(diag) -> in the basis: combination of e3, e10, e11, e12.
    # U has diagonal (1,1,-1,-1,0): solve a*e3 + b*e10 + c*e11 + d*e12 = U (imag diagonals).
    # e3 -> (1,-1,0,0,0); e10 -> (0,0,1,-1,0); e11 -> (0,0,0,1,-1); e12 -> (3,3,-2,-2,-2)
    target = [Fr(1), Fr(1), Fr(-1), Fr(-1), Fr(0)]
    cart = [[Fr(1), Fr(-1), 0, 0, 0], [0, 0, Fr(1), Fr(-1), 0], [0, 0, 0, Fr(1), Fr(-1)],
            [Fr(3), Fr(3), Fr(-2), Fr(-2), Fr(-2)]]
    # least-squares not needed: exact solve on 5 equations, 4 unknowns
    A = [[Fr(cart[j][i]) for j in range(4)] + [target[i]] for i in range(5)]
    sol, _ = solve_augmented(A, 4)
    U_coeffs = [Fr(0)] * 12
    for idx, k in zip([2, 9, 10, 11], range(4)):
        U_coeffs[idx] = sol[k]
    U_in_stabilizer = all(sum(r[k] * U_coeffs[k] for k in range(12)) == 0 for r in rows)
    return {"action_rank": rk, "stabilizer_dimension": len(null),
            "U_coefficients_e3_e10_e11_e12": [str(sol[k]) for k in range(4)],
            "U_annihilates_pair_ket": U_in_stabilizer,
            "letter_says": "rank 8, dimension 4, center the line of U = i diag(1,1;-1,-1,0) (Theorem S3)"}


def solve_augmented(A, n):
    M = [list(r) for r in A]
    r = 0
    where = [-1] * n
    for c in range(n):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        M[r] = [x / M[r][c] for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        where[c] = r
        r += 1
    consistent = all(all(x == 0 for x in row[:n]) <= (row[n] == 0) for row in M)
    return [M[where[c]][n] if where[c] >= 0 else Fr(0) for c in range(n)], consistent


def decompose_U():
    """U (diagonal (1,1,-1,-1,0)) = a * (6Y) + t * T3 + b * diag(0,0;1,1,-2)."""
    six_Y = [3, 3, -2, -2, -2]
    T3 = [Fr(1, 2), Fr(-1, 2), 0, 0, 0]
    color8 = [0, 0, 1, 1, -2]
    U = [1, 1, -1, -1, 0]
    A = [[Fr(six_Y[i]), Fr(T3[i]), Fr(color8[i]), Fr(U[i])] for i in range(5)]
    (a, t, b), ok = solve_augmented(A, 3)
    return {"U = a*(6Y) + t*T3 + b*diag(0,0;1,1,-2)": {"a": str(a), "t": str(t), "b": str(b)},
            "exact": ok,
            "reading": "U has no weak-isospin component and a nonzero color component; electric charge "
                       "Q_em = T3 + Y has a weak-isospin component and no color component, so U is not Q_em "
                       "in any normalization."}


def ray_stabilizer_dims():
    """Exact: generators xi (real combinations of the 12 basis elements) with xi|pair> in span{|pair>, i|pair>},
    the symmetries of the pair-ket ray; and its intersections with weak su(2) (e1-e3) and color su(3) (e4-e11)."""
    def cols_of(idx):
        cols = [act_on_link(BASIS[k], PAIR) for k in idx]
        flat = [[c[e][p] for e in range(6) for p in (0, 1)] for c in cols]
        w = [PAIR[e][p] for e in range(6) for p in (0, 1)]
        iw = [(-PAIR[e][1] if p == 0 else PAIR[e][0]) for e in range(6) for p in (0, 1)]
        return flat + [[-x for x in w], [-x for x in iw]]

    def dim(idx):
        cols = cols_of(idx)
        rows = [[cols[j][r] for j in range(len(cols))] for r in range(12)]
        null, _ = nullspace(rows, len(cols))
        return len(null)  # the extra two columns are independent of each other, so no pure-phase null vectors
    return {"ray_stabilizer_dimension": dim(range(12)),
            "intersection_with_weak_su2": dim(range(0, 3)),
            "intersection_with_color_su3": dim(range(3, 11)),
            "reading": "an electric charge n.T + Y leaves the ray invariant only if n.T does (Y = Q/6 acts as a "
                       "scalar); the intersection with weak su(2) is zero, so no electric-charge direction does"}


def check_electric_charge():
    """Q_em(n) = n.T + Y on the link; ray invariance of the pair ket requires Q_em|pair> = lambda|pair>."""
    # On |q, t>: Q_em acts as (n.sigma/2 + 1/2) on the qubit and -1/3 on the qutrit (Y only).
    # On the support {|00>, |11>}: (xi1 (x) 1 + 1 (x) xi2)(|00>+|11>) = sum_{q,q'} (xi1)_{q'q} |q' q> - 1/3 (|00>+|11>)
    # which lies along |00>+|11> iff (xi1)_{01} = (xi1)_{10} = 0 and (xi1)_{00} = (xi1)_{11},
    # i.e. iff n.sigma has no off-diagonal part and equal diagonal entries: n.sigma = 0, impossible for |n| = 1.
    # Charges of the two terms with n along T3:
    charges = {"|qubit 0, qutrit 0>": str(Fr(1, 2) + Fr(1, 2) - Fr(1, 3)),
               "|qubit 1, qutrit 1>": str(Fr(-1, 2) + Fr(1, 2) - Fr(1, 3))}
    return {"ray_invariant_for_some_isospin_direction": False,
            "proof": "the qubit-block generator n.sigma/2 + 1/2 must act as a scalar on the 2-dim support; its "
                     "traceless part n.sigma/2 is nonzero for every unit n",
            "electric_charges_of_the_two_terms_for_n_along_T3": charges,
            "letter_assignment": "Letter Sec. S3: the link C^2 (x) C^3 carries (3, 2) with Y = 1/6, \"the quantum "
                                 "numbers of the left-handed quark doublet\""}


def weak_angle_table():
    num = 79 + 48 * sqrt(2) + 42 * sqrt(3) + 3 * sqrt(6)
    a_cand = num / 31104
    cos2 = mpf(1) / 2  # compendium Theorem 164.5, p. 386
    rows = []
    # readout read as the coupling per unit of a hypercharge-type charge X = s * Y (Q_em = T3 + Y):
    # g_Y Y = g_X X  =>  alpha_Y = s^2 alpha_X ;  alpha_em = alpha_Y cos^2
    for name, s2 in [("per unit of Y (Q_em = T3 + Y)", mpf(1)),
                     ("per unit of 2Y (Q_em = T3 + Y/2 convention)", mpf(4)),
                     ("per unit of Q = 6Y (the Letter's central generator)", mpf(36)),
                     ("GUT-normalized U(1)_1, alpha_1 = (5/3) alpha_Y", mpf(3) / 5)]:
        a_em = s2 * a_cand * cos2
        rows.append({"reading": name, "implied_inverse_alpha_em": float(1 / a_em)})
    return {"cos2_theta_W": "1/2 (compendium Theorem 164.5, p. 386)",
            "relation": "alpha_em = alpha_Y cos^2(theta_W)",
            "rows": rows,
            "needed_for_photon_conjecture": "alpha_Y = 2 alpha_cand, i.e. a charge scale sqrt(2) that no standard "
                                            "normalization of hypercharge supplies"}


def running_ladder():
    num = 79 + 48 * sqrt(2) + 42 * sqrt(3) + 3 * sqrt(6)
    ladder = [{"k": k, "inverse_alpha_cap": float(319 ** k / num)} for k in range(4)]
    return {"compendium": "alpha_cap(k) = (79 + 48 sqrt2 + 42 sqrt3 + 3 sqrt6) / 319^k, ratio 1/319 per rung (p. 343)",
            "ladder": ladder,
            "letter_value_inverse": float(31104 / num),
            "31104_is_a_power_of_319": any(319 ** k == 31104 for k in range(10)),
            "per_rung_factor_vs_QED": "QED running from q = 0 to the Z mass changes 1/alpha by about 7% "
                                      "(137.036 to about 128.9); the ladder changes it by a factor 319 per rung"}


def main():
    results = {
        "stabilizer": check_stabilizer(),
        "unbroken_generator": decompose_U(),
        "ray_symmetries": ray_stabilizer_dims(),
        "electric_charge": check_electric_charge(),
        "weak_angle": weak_angle_table(),
        "running_ladder": running_ladder(),
        "quoted_facts": [
            {"fact": "The Ward identity used for Z1 = Z2 holds for the unit functional W = (1,1,1) and fails for "
                     "Q and U", "source": "Letter Theorem S4; compendium p. 317"},
            {"fact": "Weighted by the unbroken generator U, the 172 records sum to zero over the register",
             "source": "compendium Open result 131.1, pp. 314-316"},
            {"fact": "Two objects carry the photon name: the (2,3) open link (Theorem 134.1, p. 319) and the (2,2) "
                     "pair ket at the join (chapter 151, p. 349)", "source": "compendium"},
            {"fact": "The same numerator appears over 319 ('root read' at the cap, p. 84; alpha_cap, p. 343) "
                     "and over 31104 (the Letter)", "source": "compendium pp. 84, 343; Letter Eq. (6)"},
        ],
    }
    OUT.write_text(json.JSONEncoder(indent=1).encode(results) + "\n")
    s = results["stabilizer"]
    print(f"1. stabilizer: action rank {s['action_rank']}, dimension {s['stabilizer_dimension']}, "
          f"U annihilates the pair ket: {s['U_annihilates_pair_ket']}")
    print(f"2. U = {results['unbroken_generator']['U = a*(6Y) + t*T3 + b*diag(0,0;1,1,-2)']} "
          f"(exact: {results['unbroken_generator']['exact']})")
    rs = results["ray_symmetries"]
    print(f"   ray symmetries: dimension {rs['ray_stabilizer_dimension']}; inside weak su(2): "
          f"{rs['intersection_with_weak_su2']}; inside color su(3): {rs['intersection_with_color_su3']}")
    e = results["electric_charge"]
    print(f"3. pair-ket ray invariant under some Q_em = n.T + Y: {e['ray_invariant_for_some_isospin_direction']}; "
          f"charges of its two terms: {e['electric_charges_of_the_two_terms_for_n_along_T3']}")
    print("4. implied 1/alpha_em with cos^2 = 1/2:")
    for r in results["weak_angle"]["rows"]:
        print(f"     {r['implied_inverse_alpha_em']:10.3f}  {r['reading']}")
    rl = results["running_ladder"]
    print(f"5. ladder 1/alpha_cap(k): {[round(x['inverse_alpha_cap'], 4) for x in rl['ladder']]}; "
          f"Letter 1/alpha {rl['letter_value_inverse']:.6f}; 31104 a power of 319: {rl['31104_is_a_power_of_319']}")


if __name__ == "__main__":
    main()
