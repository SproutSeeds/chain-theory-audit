"""Export the exact (2,4) certificate as JSON (rationals as strings)."""
import json
import pickle
import sys
from pathlib import Path

d = pickle.loads(open('exact_certificate.pkl', 'rb').read())
names = ('G1 (monomials e_i e_j f_k, i<=j)', 'G2 (monomials conj(e_i) e_j f_k)', 'G3 (monomials conj(e_i) conj(e_j) f_k, i<=j)')
out = {
    "description": "Exact certificate that the integer map Phi_24 : M2 -> M4 (Choi matrix W, index 4a+k) is positive "
                   "and not decomposable. Positivity: ||e||^2 <e(x)f|W|e(x)f> = sum_t m_t^dag G_t m_t with G_t = L_t D_t L_t^T, "
                   "D_t > 0. Non-decomposability: tr(rho W) = -1 for the PPT state of P. Horodecki's 2x4 family at b = 3/5.",
    "W": [[str(x) for x in row] for row in d['W']],
    "trace_rho_W": str(d['tr']),
    "blocks": [{"name": n, "G": [[str(x) for x in row] for row in G],
                "L": [[str(x) for x in row] for row in L], "D": [str(x) for x in D]}
               for n, (G, (L, D)) in zip(names, d['blocks'])],
    "lean": "lean/ChoiDark.lean, Part 7 (phi24_certificate, phi24_positive_psd, phi24_not_decomposable)",
}
Path(sys.argv[1]).write_text(json.JSONEncoder(indent=1).encode(out) + "\n")
print("written", sys.argv[1])
