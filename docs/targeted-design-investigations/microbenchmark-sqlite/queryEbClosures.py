import locale
import sqlite3
import subprocess
import sys
import time

def query_ebs(db_name, ilb, eub):
    # Connect to the database
    conn = sqlite3.connect(db_name)
    cursor = conn.cursor()

    # Adding these made no difference in the (post-churn)
    # TenThousand.sqlite example.
    cursor.executescript('''
        PRAGMA journal_mode=WAL;
        PRAGMA synchronous=NORMAL;
        PRAGMA cache_size = 1000000;
        PRAGMA locking_mode = EXCLUSIVE;
        PRAGMA temp_store = MEMORY;
    ''')

    ebPoints = cursor.execute('''
        SELECT ebSlot, ebHash FROM EB 
        ORDER BY ebSlot
    ''').fetchall()

    conn.close()   # close it to flush the page cache

    timings1 = [0.1] * len(ebPoints)
    timings2 = [0.2] * len(ebPoints)
    ntimings = 0

    # Reconnect to the database
    conn = sqlite3.connect(db_name)
    cursor = conn.cursor()
    cursor.execute("PRAGMA synchronous = NORMAL;")

    # See queryEbBodies.py for an explanation of this.
    subprocess.run(['vmtouch', '-e', '-q', db_name], check=True)

    for ebSlot, ebHash in ebPoints:
        t1 = time.perf_counter()
        # for EBs later in the traversal, this might have some cache hits
        first_ebHashes = cursor.execute('''
            SELECT 
                (   SELECT t2.ebHash 
                    FROM EB2TX t2 
                    WHERE t2.txHash = t1.txHash 
                    LIMIT 1
                ) AS first_ebHash
            FROM EB2TX t1
            WHERE t1.ebSlot = ? AND t1.ebHash = ?
              AND ? <= txIndex AND txIndex < ?;
        ''',(ebSlot, ebHash, ilb, eub));
        for _ in first_ebHashes:
            pass
        t2 = time.perf_counter()
        # should be fully cached now
        first_ebHashes = cursor.execute('''
            SELECT 
                (   SELECT t2.ebHash 
                    FROM EB2TX t2 
                    WHERE t2.txHash = t1.txHash 
                    LIMIT 1
                ) AS first_ebHash
            FROM EB2TX t1
            WHERE t1.ebSlot = ? AND t1.ebHash = ?
              AND ? <= txIndex AND txIndex < ?;
        ''',(ebSlot, ebHash, ilb, eub));
        for _ in first_ebHashes:
            pass
        t3 = time.perf_counter()
        timings1[ntimings] = t2 - t1
        timings2[ntimings] = t3 - t2
        ntimings += 1

    for i in range(ntimings):
        print(timings1[i], timings2[i])

if __name__ == "__main__":
    db_name = sys.argv[1]
    ilb = sys.argv[2] if 2 < len(sys.argv) else 0
    eub = sys.argv[3] if 3 < len(sys.argv) else 15000
    query_ebs(db_name, ilb, eub)
