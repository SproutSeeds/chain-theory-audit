import numpy as np, cvxpy as cp, itertools
# variables order in exponent tuples: (eb0,eb1,e0,e1, fb0..fb3, f0..f3)   (eb = conj e)
def mono(eb=(), e=(), fb=(), f=()):
    v=[0]*12
    for i in eb: v[i]+=1
    for i in e: v[2+i]+=1
    for k in fb: v[4+k]+=1
    for k in f: v[8+k]+=1
    return tuple(v)
idx=[(a,k) for a in range(2) for k in range(4)]          # basis |a> (x) |k>, index a*4+k
def horodecki(b):
    s=np.sqrt(1-b*b)
    R=np.zeros((8,8))
    for i in range(3): R[i,i]=b; R[i,5+i]=R[5+i,i]=b; R[5+i,5+i]=b
    R[3,3]=b; R[4,4]=(1+b)/2; R[7,7]=(1+b)/2; R[4,7]=R[7,4]=s/2
    return R/(7*b+1)
def pt(M): return M.reshape(2,4,2,4).transpose(0,3,2,1).reshape(8,8)
sym=[(i,j) for i in range(2) for j in range(2) if i<=j]
m1=[(('e',(i,j)),k) for (i,j) in sym for k in range(4)]    # e_i e_j f_k
m2=[(('m',(i,j)),k) for i in range(2) for j in range(2) for k in range(4)]  # eb_i e_j f_k
m3=[(('b',(i,j)),k) for (i,j) in sym for k in range(4)]    # eb_i eb_j f_k
def conj_mono(m):   # monomial and its conjugate as exponent dicts
    (t,(i,j)),k=m
    if t=='e': return mono(e=(i,j),f=(k,)), mono(eb=(i,j),fb=(k,))
    if t=='m': return mono(eb=(i,),e=(j,),f=(k,)), mono(e=(i,),eb=(j,),fb=(k,))
    return mono(eb=(i,j),f=(k,)), mono(e=(i,j),fb=(k,))
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def build(rho, margin=None, target=None):
    W=cp.Variable((8,8),symmetric=True)
    Gs=[cp.Variable((len(m),len(m)),symmetric=True) for m in (m1,m2,m3)]
    lhs={}; rhs={}
    for p,(a,k) in enumerate(idx):
        for q,(b2,l) in enumerate(idx):
            base=mono(eb=(a,),fb=(k,),e=(b2,),f=(l,))
            for c in range(2):
                key=add(base,mono(eb=(c,),e=(c,)))
                lhs[key]=lhs.get(key,0)+W[p,q]
    for G,ms in zip(Gs,(m1,m2,m3)):
        for p,mp in enumerate(ms):
            _,cp_=conj_mono(mp)
            for q,mq in enumerate(ms):
                mqv,_=conj_mono(mq)
                key=add(cp_,mqv)
                rhs[key]=rhs.get(key,0)+G[p,q]
    keys=set(lhs)|set(rhs)
    cons=[(lhs.get(k,0)-rhs.get(k,0))==0 for k in keys]
    t=cp.Variable()
    cons+=[cp.trace(W)==1]+[G>>t*np.eye(G.shape[0]) for G in Gs]
    if target is None:
        cons+=[t>=0]; obj=cp.Minimize(cp.trace(rho@W))
    else:
        cons+=[cp.trace(rho@W)<=target]; obj=cp.Maximize(t)
    prob=cp.Problem(obj,cons); prob.solve(solver=cp.CLARABEL)
    return prob.value, W.value, [G.value for G in Gs], t.value
if __name__=='__main__':
    for b in (3/5, 0.5, 0.8):
        rho=horodecki(b)
        print(f'b={b}: rho psd {np.linalg.eigvalsh(rho).min():+.2e}, pt psd {np.linalg.eigvalsh(pt(rho)).min():+.2e}')
        v,W,Gs,t=build(rho)
        print(f'   certified min tr(rho W) = {v:+.6e}')
