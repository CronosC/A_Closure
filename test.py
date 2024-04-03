import numpy as np
import random
import time
from itertools import chain, combinations
from os.path import exists

M = np.random.rand(5,5)
print(M)
M = np.where(M > 0.5, 0, 1)
print(M)
L=[0]
res = np.transpose(np.isin(M, L).nonzero())
print(res)