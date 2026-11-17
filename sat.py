import argparse
import os
import sys
import time

def read_cnf(path):
    num_vars, clauses = 0, []
    current = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("c") or line.startswith("%"):
                continue
            if line.startswith("p"):
                _, _, n, _ = line.split()[:4]
                num_vars = int(n)
                continue
            for tok in line.split():
                lit = int(tok)
                if lit == 0:
                    clauses.append(current)
                    current = []
                else:
                    current.append(lit)
    if current:
        clauses.append(current)
    num_vars = max([num_vars] + [abs(l) for c in clauses for l in c])
    return num_vars, clauses

def init_assignment(num_vars, value=1):
    return [None] + [value] * num_vars

def literal_value(lit, assignment):
    v = assignment[abs(lit)]
    return v if lit > 0 else 1 - v

def evaluate(clauses, assignment):
    table = [[literal_value(l, assignment) for l in clause] for clause in clauses]
    row_sums = [sum(row) for row in table]
    num_errors = sum(1 for s in row_sums if s == 0)
    return table, row_sums, num_errors

def count_errors(clauses, assignment):
    return sum(1 for c in clauses if not any(literal_value(l, assignment) for l in c))

def choose_start(num_vars, clauses):
    all_one = init_assignment(num_vars, 1)
    all_zero = init_assignment(num_vars, 0)
    e1 = count_errors(clauses, all_one)
    e0 = count_errors(clauses, all_zero)
    if e0 > e1:
        return all_zero, "all-0"
    return all_one, "all-1"

def state_key(assignment):
    return bytes(assignment[1:])

def rank_groups(clauses, table, row_sums):
    error_count = {}
    for clause, s in zip(clauses, row_sums):
        if s == 0:
            for var in {abs(l) for l in clause}:
                error_count[var] = error_count.get(var, 0) + 1

    if not error_count:
        return [], {}

    critical = {v: 0 for v in error_count}
    for clause, row, s in zip(clauses, table, row_sums):
        if s == 1:
            v = abs(clause[row.index(1)])
            if v in critical:
                critical[v] += 1

    groups = []
    for count in sorted(set(error_count.values()), reverse=True):
        members = sorted((v for v, c in error_count.items() if c == count),
                         key=lambda v: (critical[v], v))
        groups.append((count, members))
    return groups, {"error_count": error_count, "critical": critical}

def step(clauses, assignment, step_no, visited, verbose=True, stats=None):
    say = print if verbose else (lambda *a, **k: None)
    table, row_sums, errors = evaluate(clauses, assignment)
    groups, info = rank_groups(clauses, table, row_sums)
    if not groups:
        return "solved"

    if verbose:
        say(f"--- step {step_no} (errors before: {errors}) ---")

    for gi, (count, members) in enumerate(groups):
        flipped = 0
        for var in members:
            old = assignment[var]
            assignment[var] = 1 - old
            key = state_key(assignment)
            if key in visited:
                assignment[var] = old
                say(f"  skip x{var}: repeat state")
                continue
            visited.add(key)
            flipped += 1
            if stats is not None:
                stats["flips"] += 1
            errors_now = count_errors(clauses, assignment)
            say(f"  flip x{var}: {old} -> {assignment[var]} (errors: {errors_now})")
            if errors_now == 0:
                return "ok"
        if flipped:
            return "ok"

    return "stuck"

def solve(clauses, num_vars, max_steps):
    assignment = choose_start(num_vars, clauses)[0]
    visited = {state_key(assignment)}
    stats = {"flips": 0}
    steps = 0
    t0 = time.perf_counter()
    
    while True:
        if count_errors(clauses, assignment) == 0:
            status = "solved"
            break
        if steps >= max_steps:
            status = "capped"
            break
        if step(clauses, assignment, steps + 1, visited, verbose=False, stats=stats) == "stuck":
            status = "stuck"
            break
        steps += 1
        
    return {"status": status, "steps": steps, "flips": stats["flips"], "seconds": time.perf_counter() - t0}

def interactive(path):
    num_vars, clauses = read_cnf(path)
    assignment, name = choose_start(num_vars, clauses)
    print(f"Variables: {num_vars}, Clauses: {len(clauses)}, Start: {name}")

    visited = {state_key(assignment)}
    step_no = 1
    
    while True:
        try:
            cmd = input("\n[n = next step, n x = next x steps, t = table, q = quit] > ").split()
        except EOFError:
            break
        if not cmd:
            continue
        if cmd[0] == "q":
            break
        elif cmd[0] == "t":
            table, row_sums, errors = evaluate(clauses, assignment)
            for clause, row, s in zip(clauses, table, row_sums):
                print(f"{clause} -> {row} sum={s}")
            print(f"errors: {errors}")
        elif cmd[0] == "n":
            count = int(cmd[1]) if len(cmd) > 1 and cmd[1].isdigit() else 1
            for _ in range(count):
                result = step(clauses, assignment, step_no, visited)
                if result == "solved":
                    print("SATISFIED!")
                    return
                if result == "stuck":
                    print("Stuck :( )")
                    return
                step_no += 1

def batch(folder, max_steps, limit, compare):
    paths = sorted([os.path.join(root, f) for root, _, files in os.walk(folder) for f in files if f.endswith(".cnf")])
    if limit:
        paths = paths[:limit]

    minisat = None
    if compare:
        from pysat.solvers import Minisat22
        minisat = Minisat22

    solved, total = 0, len(paths)
    for i, path in enumerate(paths, 1):
        num_vars, clauses = read_cnf(path)
        res = solve(clauses, num_vars, max_steps)
        print(f"[{i}/{total}] {os.path.basename(path)} -> {res['status']} ({res['steps']} steps, {res['flips']} flips)")
        if res['status'] == "solved":
            solved += 1
        if minisat:
            with minisat(bootstrap_with=clauses) as s:
                print(f"  MiniSat: sat={s.solve()}")

    print(f"\nFinished. Solved {solved}/{total} files.")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    ap.add_argument("--max-steps", type=int, default=5000)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--compare", action="store_true")
    args = ap.parse_args()

    if os.path.isdir(args.path):
        batch(args.path, args.max_steps, args.limit, args.compare)
    elif os.path.isfile(args.path):
        interactive(args.path)

if __name__ == "__main__":
    main()