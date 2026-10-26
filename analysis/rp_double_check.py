"""Bridge check: a Chain-Theory link |omega> on H (x) Hbar is the canonical reflection-positive 'double'.
Reflection theta: A (x) 1  ->  1 (x) conj(A)  (antilinear swap). RP form: F(A) = <theta(A) A>_rho.
Claim 1: for any rho on C^d (x) C^d, F(A) = vec(A)^dag M vec(A) with M a realignment of rho,
         so rho is RP  <=>  M >= 0.
Claim 2: for rho = |omega><omega|, M = 1/d (flat): maximally RP; for separable/PPT states M need not be PSD."""
import numpy as np
rng = np.random.default_rng(0)
def rand_rho(d, rank=None):
    G = rng.normal(size=(d*d, rank or d*d)) + 1j*rng.normal(size=(d*d, rank or d*d))
    r = G @ G.conj().T; return r / np.trace(r)
def rp_form(rho, A, d):
    # theta(A) acts on factor 1 as conj(A); A acts on factor 2
    return np.trace(rho @ np.kron(A.conj(), A))
def realigned(rho, d):
    R = rho.reshape(d, d, d, d)            # R[a,b,c,d] = rho_{(ab),(cd)}
    # M_{(c a),(d b)} = rho_{(a b),(c d)}
    return np.einsum('abcd->cadb', R).reshape(d*d, d*d)
for d in (2, 3):
    worst = 0
    for _ in range(200):
        rho = rand_rho(d); A = rng.normal(size=(d, d)) + 1j*rng.normal(size=(d, d))
        v = A.reshape(-1)                   # vec(A) with index (k,l)
        M = realigned(rho, d)
        worst = max(worst, abs(rp_form(rho, A, d) - v.conj() @ M @ v))
    w = np.zeros(d*d); w[[i*d+i for i in range(d)]] = 1/np.sqrt(d)
    Mw = realigned(np.outer(w, w.conj()), d)
    print(f'd={d}: max |F(A) - vec(A)^† M vec(A)| over 200 random (rho,A) = {worst:.2e};',
          f'omega realigned == I/d: {np.allclose(Mw, np.eye(d*d)/d)}')
    # a random state is generally NOT RP under this reflection
    rho = rand_rho(d); print(f'      random rho: min eig of realigned M = {np.linalg.eigvalsh((realigned(rho,d)+realigned(rho,d).conj().T)/2).min():+.3f}')
