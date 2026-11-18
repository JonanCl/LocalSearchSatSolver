import argparse
import os
import random
import time

def read_cnf(path):
    num_vars, clauses, current = 0, [], []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("%"):
                break
            if line.startswith("p"):
                num_vars = int(line.split()[2])
                continue
            for tok in line.split():
                lit = int(tok)
                if lit == 0:
                    if current:
                        clauses.append(current)
                    current = []
                else:
                    current.append(lit)
    if current:
        clauses.append(current)
    clauses = clean(clauses)
    num_vars = max([num_vars] + [abs(l) for c in clauses for l in c])
    return num_vars, clauses

def clean(clauses):
    out = []
    for c in clauses:
        s = set(c)
        if any(-l in s for l in s):
            continue
        out.append(sorted(s, key=abs))
    return out

def init_all(n, clauses, occ, rng, val):
    return [0] + [val] * n

def init_random(n, clauses, occ, rng):
    return [0] + [rng.randint(0, 1) for _ in range(n)]

def init_majority(n, clauses, occ, rng):
    a = [0] * (n + 1)
    for v in range(1, n + 1):
        p, q = len(occ[v + n]), len(occ[-v + n])
        a[v] = 1 if p > q else 0 if q > p else rng.randint(0, 1)
    return a

def init_jw(n, clauses, occ, rng):
    a = [0] * (n + 1)
    for v in range(1, n + 1):
        p = sum(2.0 ** -len(clauses[c]) for c in occ[v + n])
        q = sum(2.0 ** -len(clauses[c]) for c in occ[-v + n])
        a[v] = 1 if p > q else 0 if q > p else rng.randint(0, 1)
    return a

def init_greedy(n, clauses, occ, rng):
    a = [0] * (n + 1)
    sat = [False] * len(clauses)
    order = sorted(range(1, n + 1), key=lambda v: -(len(occ[v + n]) + len(occ[-v + n])) + rng.random())
    for v in order:
        p = sum(2.0 ** -len(clauses[c]) for c in occ[v + n] if not sat[c])
        q = sum(2.0 ** -len(clauses[c]) for c in occ[-v + n] if not sat[c])
        a[v] = 1 if p > q else 0 if q > p else rng.randint(0, 1)
        for c in occ[(v if a[v] else -v) + n]:
            sat[c] = True
    return a

def init_unitprop(n, clauses, occ, rng):
    a = [None] * (n + 1)
    sat = [False] * len(clauses)
    free = [len(c) for c in clauses]
    queue = []

    def assign(lit):
        v = abs(lit)
        if a[v] is not None:
            return
        a[v] = 1 if lit > 0 else 0
        for c in occ[lit + n]:
            sat[c] = True
        for c in occ[-lit + n]:
            free[c] -= 1
            if not sat[c] and free[c] == 1:
                queue.append(c)

    def drain():
        while queue:
            c = queue.pop()
            if sat[c]:
                continue
            for l in clauses[c]:
                if a[abs(l)] is None:
                    assign(l)
                    break

    for c, cl in enumerate(clauses):
        if len(cl) == 1:
            assign(cl[0])
    drain()
    order = sorted(range(1, n + 1), key=lambda v: -(len(occ[v + n]) + len(occ[-v + n])) + rng.random())
    for v in order:
        if a[v] is not None:
            continue
        p = sum(2.0 ** -len(clauses[c]) for c in occ[v + n] if not sat[c])
        q = sum(2.0 ** -len(clauses[c]) for c in occ[-v + n] if not sat[c])
        assign(v if (p > q or (p == q and rng.random() < 0.5)) else -v)
        drain()
    return [0] + [x if x is not None else 0 for x in a[1:]]

INITS = {
    "all1": lambda n, c, o, r: init_all(n, c, o, r, 1),
    "all0": lambda n, c, o, r: init_all(n, c, o, r, 0),
    "random": init_random,
    "majority": init_majority,
    "jw": init_jw,
    "greedy": init_greedy,
    "unitprop": init_unitprop,
}

class Solver:
    def __init__(self, n, clauses):
        self.n, self.clauses = n, clauses
        self.occ = [[] for _ in range(2 * n + 1)]
        for ci, c in enumerate(clauses):
            for l in c:
                self.occ[l + n].append(ci)

    def load(self, a):
        n, clauses, occ = self.n, self.clauses, self.occ
        self.a = a[:]
        m = len(clauses)
        self.true_cnt = [0] * m
        self.true_sum = [0] * m
        self.brk = [0] * (n + 1)
        self.unsat, self.pos = [], [-1] * m
        for ci, c in enumerate(clauses):
            for l in c:
                if self.a[abs(l)] == (1 if l > 0 else 0):
                    self.true_cnt[ci] += 1
                    self.true_sum[ci] += abs(l)
            if self.true_cnt[ci] == 0:
                self._add_unsat(ci)
            elif self.true_cnt[ci] == 1:
                self.brk[self.true_sum[ci]] += 1

    def _add_unsat(self, c):
        self.pos[c] = len(self.unsat)
        self.unsat.append(c)

    def _del_unsat(self, c):
        i, last = self.pos[c], self.unsat[-1]
        self.unsat[i] = last
        self.pos[last] = i
        self.unsat.pop()
        self.pos[c] = -1

    def flip(self, v):
        n, tc, ts, brk, occ = self.n, self.true_cnt, self.true_sum, self.brk, self.occ
        new = 1 - self.a[v]
        self.a[v] = new
        gain = v if new else -v
        for c in occ[gain + n]:
            if tc[c] == 0:
                self._del_unsat(c)
                brk[v] += 1
            elif tc[c] == 1:
                brk[ts[c]] -= 1
            tc[c] += 1
            ts[c] += v
        for c in occ[-gain + n]:
            tc[c] -= 1
            ts[c] -= v
            if tc[c] == 0:
                self._add_unsat(c)
                brk[v] -= 1
            elif tc[c] == 1:
                brk[ts[c]] += 1

    def run(self, max_flips, rng, cb=2.5):
        clauses, brk = self.clauses, self.brk
        lut = [cb ** -i for i in range(64)]
        flips = 0
        while self.unsat and flips < max_flips:
            c = self.unsat[rng.randrange(len(self.unsat))]
            cl = clauses[c]
            ws = [lut[min(brk[abs(l)], 63)] for l in cl]
            v = abs(rng.choices(cl, weights=ws)[0])
            self.flip(v)
            flips += 1
        return not self.unsat, flips

def solve(n, clauses, init="greedy", max_flips=200_000, tries=10, seed=0, noise=0.02, cb=2.5):
    rng = random.Random(seed)
    s = Solver(n, clauses)
    total, t0 = 0, time.perf_counter()
    first_unsat = 0
    ok = False
    for t in range(tries):
        a = INITS[init](n, clauses, s.occ, rng)
        if t > 0 and init != "random":
            for v in range(1, n + 1):
                if rng.random() < noise:
                    a[v] ^= 1
        s.load(a)
        start_unsat = len(s.unsat)
        ok, fl = s.run(max_flips, rng, cb)
        total += fl
        if t == 0:
            first_unsat = start_unsat
        if ok:
            break
    dt = time.perf_counter() - t0
    return {"solved": ok, "flips": total, "tries": t + 1, "seconds": dt,
            "init_unsat": first_unsat, "model": s.a if ok else None}

def verify(clauses, a):
    return all(any(a[abs(l)] == (1 if l > 0 else 0) for l in c) for c in clauses)

def find_cnf(path):
    if os.path.isfile(path):
        return [path]
    return sorted(os.path.join(r, f) for r, _, fs in os.walk(path) for f in fs if f.endswith(".cnf"))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    ap.add_argument("--init", default="greedy")
    ap.add_argument("--max-flips", type=int, default=200_000)
    ap.add_argument("--tries", type=int, default=10)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--cb", type=float, default=2.5)
    ap.add_argument("--minisat", action="store_true")
    args = ap.parse_args()

    paths = find_cnf(args.path)
    if args.limit:
        paths = paths[:args.limit]
    inits = list(INITS) if args.init == "all" else [args.init]
    stats = {i: [0, 0, 0.0, 0] for i in inits}

    for p in paths:
        n, clauses = read_cnf(p)
        line = [f"{os.path.basename(p)} (n={n}, m={len(clauses)})"]
        for i in inits:
            r = solve(n, clauses, i, args.max_flips, args.tries, args.seed, cb=args.cb)
            if r["solved"]:
                assert verify(clauses, r["model"])
            st = stats[i]
            st[0] += r["solved"]; st[1] += r["flips"]; st[2] += r["seconds"]; st[3] += r["init_unsat"]
            line.append(f"{i}: {'SAT' if r['solved'] else 'fail'} {r['flips']}fl")
            
            # Print the satisfying model assignment if solved
            if r["solved"] and r["model"]:
                model_out = " ".join(f"{v if val == 1 else -v}" for v, val in enumerate(r["model"][1:], 1))
                print(f"    Solution: {model_out}")

        print("  ".join(line))

        if args.minisat:
            from pysat.solvers import Minisat22
            with Minisat22(bootstrap_with=clauses) as s:
                t0 = time.perf_counter(); res = s.solve(); t1 = time.perf_counter() - t0
            print(f"    MiniSat plain: sat={res} {t1:.4f}s")

    for i, (sv, fl, sec, iu) in stats.items():
        print(f"Init: {i} | Solved: {sv}/{len(paths)} | Total Flips: {fl}")

if __name__ == "__main__":
    main()
