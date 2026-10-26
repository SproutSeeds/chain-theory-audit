"""How surprising is a 1-sigma match inside the candidate's own algebraic family?
Family F(C,P): (n1 + n2*sqrt2 + n3*sqrt3 + n4*sqrt6) / (2^p 3^q), 0<=n_i<=C, 0<=p,q<=P.
We count members whose inverse lies within 1 sigma of CODATA 2022 (137.035999177(21))."""
import numpy as np
inv_codata, sig = 137.035999177, 0.000000021
alpha = 1/inv_codata
r2, r3, r6 = np.sqrt(2), np.sqrt(3), np.sqrt(6)
def run(C, P):
    n = np.arange(C+1, dtype=np.float64)
    n2, n3, n4 = np.meshgrid(n, n, n, indexing='ij')
    irr = (n2*r2 + n3*r3 + n4*r6).ravel()
    hits, members = [], 0
    for p in range(P+1):
        for q in range(P+1):
            N = 2.0**p * 3.0**q
            target = N*alpha - irr                      # required n1
            n1 = np.rint(target)
            ok = (n1 >= 0) & (n1 <= C)
            members += (C+1)**4
            val = (n1 + irr) / N
            inv = 1/val
            good = ok & (np.abs(inv - inv_codata) <= sig)
            for idx in np.nonzero(good)[0]:
                i2, i3, i4 = np.unravel_index(idx, n2.shape)
                hits.append((int(n1[idx]), i2, i3, i4, p, q, inv[idx]))
    return members, hits
for C, P in [(50, 8), (100, 10)]:
    members, hits = run(C, P)
    print(f'C={C} P={P}: family size {members:.3e}, members within 1 sigma: {len(hits)}')
    for h in sorted(hits, key=lambda h: abs(h[-1]-inv_codata))[:6]:
        n1,n2,n3,n4,p,q,inv = h
        print(f'   ({n1} + {n2}√2 + {n3}√3 + {n4}√6)/(2^{p}·3^{q})  1/α = {inv:.10f}')
# expected rate from local density of the paper's own nearby alternatives (Table S5)
alts = [135.894, 146.524, 127.536, 139.030, 134.485, 112.423, 139.713, 138.348, 132.739, 141.621]
spread = np.std(alts)
print(f'\nTable S5 neighbours: {len(alts)} variants, spread ~{spread:.1f} in 1/alpha around 137')
p_one = 2*sig / (np.sqrt(2*np.pi)*spread)   # chance a random nearby variant lands within +/-1 sigma
print(f'chance per variant of a 1-sigma hit ~ {p_one:.1e}; variants needed for an even-odds chance hit ~ {np.log(2)/p_one:.1e}')
