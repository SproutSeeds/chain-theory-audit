"""Independent rebuild of the 172-record count from the Letter's text (not from the Lean file).
Slots Q1,q1,Q2,q2 carry real traceless letters: 8 at the qutrit copies, 3 at the qubits.
E = exchange of the two reads' slots (Q1<->Q2, q1<->q2). X acts on same-end records, Y on mixed ones (Eq. S3)."""
import itertools, math
from mpmath import mp, sqrt, mpf
mp.dps = 40

def count(dQ, dq):
    a, b = dQ*dQ - 1, dq*dq - 1
    slots = {'Q1': a, 'q1': b, 'Q2': a, 'q2': b}
    end = {'Q1': 'Q', 'Q2': 'Q', 'q1': 'q', 'q2': 'q'}
    swap = {'Q1': 'Q2', 'Q2': 'Q1', 'q1': 'q2', 'q2': 'q1'}
    prods = []
    for s1, s2 in itertools.combinations(slots, 2):
        for i in range(slots[s1]):
            for j in range(slots[s2]):
                prods.append(frozenset([(s1, i), (s2, j)]))
    assert len(set(prods)) == len(prods)
    image = lambda p: frozenset((swap[s], i) for s, i in p)
    seen, sectors = set(), {}
    def add(XY, n=1): sectors[XY] = sectors.get(XY, 0) + n
    for p in prods:
        if p in seen: continue
        q = image(p); seen |= {p, q}
        same_end = len({end[s] for s, _ in p}) == 1
        parities = [+1] if p == q else [+1, -1]          # fixed product, or even/odd combos
        for par in parities:
            if same_end: add((-par, +1))                   # X = -p, Y = +1
            else:        add((+1, -par))                   # X = +1, Y = -p
    ncomm = b*(b-1)//2 if dq % 2 == 0 else 0               # anticommuting reads only at even dimension
    add((-1, -1), ncomm)
    nrec = sum(sectors.values())
    # weight sqrt(k), k = dQ^[X=-1] * dq^[Y=-1]
    val = sum(n * sqrt((dQ if X == -1 else 1) * (dq if Y == -1 else 1)) for (X, Y), n in sectors.items())
    N = (a*b) * (dQ*dq)**2 * (dQ*dq)**2
    return len(prods), nrec, sectors, val / N, N

nprod, nrec, sec, alpha, N = count(3, 2)
print('products', nprod, 'records', nrec, 'N', N)
print('sectors (X,Y):count', dict(sorted(sec.items())))
print('alpha =', alpha, ' 1/alpha =', 1/alpha)
ref = (79 + 48*sqrt(2) + 42*sqrt(3) + 3*sqrt(6)) / 31104
print('matches closed form:', abs(alpha - ref) < mpf(10)**-35)
print()
print('Same rule evaluated at other end dimensions (read end dQ, far end dq) -- illustrative only:')
for dQ, dq in [(2,2),(3,2),(3,3),(4,2),(4,3),(4,4),(5,2)]:
    _, nr, s, al, NN = count(dQ, dq)
    print(f'  ({dQ},{dq}): records={nr:4d} N={NN:>9d}  1/value={float(1/al):14.6f}')
