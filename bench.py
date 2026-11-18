import argparse
import csv
import os
import statistics as st

from sat import INITS, find_cnf, read_cnf, solve, verify

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("folder")
    ap.add_argument("--inits", nargs="+", default=list(INITS), choices=list(INITS))
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--max-flips", type=int, default=200_000)
    ap.add_argument("--tries", type=int, default=10)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--cb", type=float, default=2.5)
    ap.add_argument("--csv", help="write run data to CSV")
    args = ap.parse_args()

    paths = find_cnf(args.folder)
    if args.limit:
        paths = paths[:args.limit]
    if not paths:
        raise SystemExit(f"no .cnf files found in {args.folder}")

    rows = []
    for i, p in enumerate(paths, 1):
        n, clauses = read_cnf(p)
        name = os.path.basename(p)
        for init in args.inits:
            for seed in range(args.runs):
                r = solve(n, clauses, init, args.max_flips, args.tries, seed, cb=args.cb)
                if r["solved"]:
                    assert verify(clauses, r["model"]), f"invalid model on {name}"
                rows.append({"file": name, "vars": n, "clauses": len(clauses), "init": init,
                             "seed": seed, "solved": r["solved"], "flips": r["flips"],
                             "tries": r["tries"], "seconds": r["seconds"],
                             "init_unsat": r["init_unsat"]})
        print(f"[{i}/{len(paths)}] {name}")

    if args.csv:
        with open(args.csv, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows[0]))
            w.writeheader()
            w.writerows(rows)
        print(f"Data written to {args.csv}")

    print("\nBenchmark Summary:")
    for init in args.inits:
        rs = [r for r in rows if r["init"] == init]
        ok = [r["flips"] for r in rs if r["solved"]]
        secs = sum(r["seconds"] for r in rs)
        allflips = sum(r["flips"] for r in rs)
        rate = f"{len(ok)}/{len(rs)} ({100 * len(ok) / len(rs):.0f}%)"
        mean_flips = f"{st.mean(ok):,.0f}" if ok else "-"
        median_flips = f"{st.median(ok):,.0f}" if ok else "-"
        fps = f"{allflips / secs:,.0f}" if secs else "0"
        
        print(f"Init: {init} | Solved: {rate} | Mean Flips: {mean_flips} | Median Flips: {median_flips} | Flips/s: {fps}")

    never = sorted({r["file"] for r in rows} - {r["file"] for r in rows if r["solved"]})
    if never:
        print(f"\nUnsolved files ({len(never)}): " + ", ".join(never[:5]))

    common = set.intersection(*[{r["file"] for r in rows if r["init"] == i and r["solved"]}
                                for i in args.inits])
    if common and len(args.inits) > 1:
        print(f"\nMedian flips on {len(common)} files solved by ALL heuristics:")
        for init in args.inits:
            xs = [r["flips"] for r in rows if r["init"] == init and r["solved"] and r["file"] in common]
            med = f"{st.median(xs):,.0f}" if xs else "-"
            print(f"  {init}: {med}")

if __name__ == "__main__":
    main()