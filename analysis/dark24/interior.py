import numpy as np
from cert import build, horodecki
np.set_printoptions(precision=4, suppress=True, linewidth=150)
rho=horodecki(3/5)
v,W,Gs,t=build(rho, target=-1e-3)
print('margin t =', t, ' tr(rho W) =', np.trace(rho@W))
print('W (x 1000):'); print(W*1000)
np.save('W_interior.npy', W)
for i,G in enumerate(Gs): np.save(f'G{i+1}_interior.npy', G); print(f'G{i+1} min eig', np.linalg.eigvalsh(G).min())
