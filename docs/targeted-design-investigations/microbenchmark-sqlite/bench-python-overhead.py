# Auxiliary bench: bound the Python-loop + cursor-iteration cost of
# queryEbClosures.py by running the same iteration shape against a
# recursive CTE that returns 15000 tiny rows with no I/O.
#
# If the per-iteration time is much smaller than the ~55 ms cached
# EbClosure fetch, then Python loop overhead is not what is making
# that measurement slow.
#
# Usage: python bench-python-overhead.py [n_iters]
#   default n_iters = 10000 (matches a full queryEbClosures.py pass)
#
# Uses an in-memory database, so it does not touch TenThousand.sqlite
# or any other on-disk file.

import sqlite3
import sys
import time

def bench(n_iters):
    conn = sqlite3.connect(":memory:")
    cursor = conn.cursor()
    # Same PRAGMAs as queryEbClosures.py, minus journal_mode which is
    # irrelevant for :memory:.
    cursor.executescript('''
        PRAGMA synchronous=NORMAL;
        PRAGMA cache_size = 1000000;
        PRAGMA locking_mode = EXCLUSIVE;
        PRAGMA temp_store = MEMORY;
    ''')

    # A recursive CTE emitting 15000 rows. Matches the row count of
    # the inner query in queryEbClosures.py (txIndex 0..14999).
    cte = '''
        WITH RECURSIVE c(x) AS (
            VALUES(0) UNION ALL SELECT x+1 FROM c WHERE x < 14999
        )
        SELECT x FROM c
    '''

    # Warmup to get statement prep out of the way.
    for _ in cursor.execute(cte):
        pass

    timings = [0.0] * n_iters
    t_start = time.perf_counter()
    for i in range(n_iters):
        t1 = time.perf_counter()
        cur = cursor.execute(cte)
        for _ in cur:
            pass
        t2 = time.perf_counter()
        timings[i] = t2 - t1
    t_end = time.perf_counter()

    # Summary to stderr so it does not pollute the per-iteration dump.
    total = t_end - t_start
    avg_ms = 1000.0 * total / n_iters
    timings_sorted = sorted(timings)
    p50 = timings_sorted[n_iters // 2] * 1000
    p99 = timings_sorted[int(n_iters * 0.99)] * 1000
    pmax = timings_sorted[-1] * 1000
    print(f"n_iters={n_iters}", file=sys.stderr)
    print(f"total   = {total:.3f} s", file=sys.stderr)
    print(f"avg     = {avg_ms:.3f} ms / iter", file=sys.stderr)
    print(f"p50     = {p50:.3f} ms", file=sys.stderr)
    print(f"p99     = {p99:.3f} ms", file=sys.stderr)
    print(f"max     = {pmax:.3f} ms", file=sys.stderr)

    for t in timings:
        print(t)

if __name__ == "__main__":
    n_iters = int(sys.argv[1]) if len(sys.argv) > 1 else 10000
    bench(n_iters)
