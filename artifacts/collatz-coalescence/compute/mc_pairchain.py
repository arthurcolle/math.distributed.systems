"""Monte Carlo for the neighbour pair chain of the shortcut Collatz map.

Each path starts at (d, mu) = (0, 1) and is driven by fair coins; it stops when it reaches (0, 0),
i.e. when the trajectories of x and x+1 have merged on the whole cylinder.  The fraction of paths
absorbed by step k estimates C_k / 2^k.  Arithmetic is exact (Python integers).

usage: mc_pairchain.py N K SEED NPROC   ->  one JSON line: checkpoints and the number absorbed by each
"""
import json, random, sys
from multiprocessing import Pool

def run_batch(args):
    n, K, seed = args
    rng = random.Random(seed)
    P3 = [1]
    times = []
    for _ in range(n):
        d, mu, k = 0, 1, 0
        t = K + 1
        while k < K:
            bits = rng.getrandbits(62)
            for _i in range(62):
                c = bits & 1; bits >>= 1
                if mu & 1 == 0:
                    if c == 0: mu >>= 1
                    else:
                        while len(P3) <= d: P3.append(P3[-1] * 3)
                        mu = (3 * mu + 1 - P3[d]) >> 1
                elif c == 0:
                    d += 1; mu = (3 * mu + 1) >> 1
                elif d >= 1:
                    while len(P3) <= d: P3.append(P3[-1] * 3)
                    mu = (mu - P3[d - 1]) >> 1; d -= 1
                else:
                    d = 1; mu = (1 - 3 * mu) >> 1
                k += 1
                if d == 0:
                    if mu == 0: t = k; break
                    if mu < 0: mu = -mu
                if k >= K: break
            if t <= K: break
        times.append(t)
    return times

if __name__ == "__main__":
    N, K, seed, nproc = (int(a) for a in sys.argv[1:5])
    per = max(1, N // (nproc * 8))
    jobs = [(per, K, seed * 1000003 + i) for i in range(N // per)]
    cps = sorted({int(round(10 ** (j / 4))) for j in range(4, 100) if 10 ** (j / 4) <= K * 1.0001})
    counts = [0] * len(cps); total = 0
    with Pool(nproc) as pool:
        for times in pool.imap_unordered(run_batch, jobs):
            total += len(times)
            for t in times:
                for i, cp in enumerate(cps):
                    if t <= cp: counts[i] += 1
    print(json.dumps({"paths": total, "horizon": K, "seed": seed, "checkpoints": cps, "absorbed": counts}))
