import numpy as np
from pcs import vertices_from_H
def worker(gens, q):
    q.put([list(v) for v in vertices_from_H(gens, len(gens[0]))])
