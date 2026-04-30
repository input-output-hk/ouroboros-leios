import sqlite3
import subprocess
import sys
import time


def query_ebs(db_name):
    # Connect to the database
    conn = sqlite3.connect(db_name)
    cursor = conn.cursor()

    # Adding the optional ones among these made no difference in the
    # (post-churn) TenThousand.sqlite example.
    cursor.executescript(
        """
        PRAGMA journal_mode=WAL;
        PRAGMA synchronous=NORMAL;
        PRAGMA cache_size = 1000000;
        PRAGMA locking_mode = EXCLUSIVE;
        PRAGMA temp_store = MEMORY;
    """
    )

    ebPoints = cursor.execute(
        """
        SELECT ebSlot, ebHash FROM EB 
        ORDER BY ebSlot
    """
    ).fetchall()

    conn.close()  # close it to flush the page cache

    timings1 = [0.1] * len(ebPoints)
    timings2 = [0.2] * len(ebPoints)
    ntimings = 0

    # Reconnect to the database
    conn = sqlite3.connect(db_name)
    cursor = conn.cursor()
    cursor.execute("PRAGMA synchronous = NORMAL;")

    # We call this _after_ opening the database to undo whatever OS
    # prefetching happened when the connection read the first page of
    # the database file.
    subprocess.run(["vmtouch", "-e", "-q", db_name], check=True)

    # But I still see unexpected cache hits in the first couple
    # iterations. I think maybe those are just in the actual first
    # page, and so it's in the SQLite page cache. It doesn't seem
    # worth the trouble to flush that first, since SQLite doesn't make
    # that easy to do (reasonable!).

    # My drive is a WD_BLACK SN770 2TB, which uses up to 64 MB of the
    # host's RAM as its cache (aka Host Memory Buffer, aka HMB).
    #
    # The vmtouch command above doesn't reset that cache. It should be
    # largely irrelevant since our database file is much bigger than
    # 64 MB and we touch the whole thing on each iteration, though.

    for ebSlot, ebHash in ebPoints:
        t1 = time.perf_counter()
        # for EBs later in the traversal, this might have some cache hits
        tx_refs = cursor.execute(
            "SELECT txHash, txBytesSize FROM EB2TX WHERE (ebSlot, ebHash) = (?, ?) ORDER BY txIndex ASC",
            (ebSlot, ebHash),
        )
        for _ in tx_refs:
            pass
        t2 = time.perf_counter()
        # should be fully cached now
        tx_refs = cursor.execute(
            "SELECT txHash, txBytesSize FROM EB2TX WHERE (ebSlot, ebHash) = (?, ?) ORDER BY txIndex ASC",
            (ebSlot, ebHash),
        )
        for _ in tx_refs:
            pass
        t3 = time.perf_counter()
        timings1[ntimings] = t2 - t1
        timings2[ntimings] = t3 - t2
        ntimings += 1

    for i in range(ntimings):
        print(timings1[i], timings2[i])


if __name__ == "__main__":
    db_name = sys.argv[1]
    query_ebs(db_name)
