import numpy as np
from scipy.optimize import linprog
x=np.linspace(-2,2,4001); f=np.exp(x)
# Y = A0(1+x) + A1 x^2 + 16 A4 x^3 + A3 x^4 + A4 x^5
B=np.stack([1+x, x**2, x**4, 16*x**3+x**5],1)
m=B.shape[1]
c=np.r_[np.zeros(m),1]
Aub=np.r_[np.c_[B,-np.ones(len(x))],np.c_[-B,-np.ones(len(x))]]
r=linprog(c,A_ub=Aub,b_ub=np.r_[f,-f],bounds=[(None,None)]*(m+1))
A0,A1,A3,A4=r.x[:4]; print('err',r.x[-1]); print('A0 A1 A3 A4',A0,A1,A3,A4,'16A4',16*A4)
