import datetime
import locale
import sqlite3
import sys
import time

need_rebuild_index = lambda n: n > 3000    # TODO tune this threshold

def prune_ebs(db_name, cutoff):
    # Connect to the database
    conn = sqlite3.connect(db_name)
    cursor = conn.cursor()

    # Assume WAL and then optimize for massive bulk data insertion.
    #
    # TODO this is too aggressive for the actual implementation, but
    # we're being generous for the benchmark.
    cursor.executescript('''
        PRAGMA journal_mode=WAL;
        PRAGMA synchronous = 0;
        PRAGMA cache_size = 1000000;
        PRAGMA locking_mode = EXCLUSIVE;
        PRAGMA temp_store = MEMORY;
    ''')

    try:
        cursor.execute('''
            CREATE TEMPORARY TABLE choppingBlock (
                ebSlot INTEGER, 
                ebHash BLOB,
                PRIMARY KEY (ebSlot, ebHash)
            );
        ''')

        cursor.execute('''
            INSERT INTO choppingBlock (ebSlot, ebHash)
            SELECT ebSlot, ebHash FROM EB 
            WHERE ebSlot <= ?;
        ''', (cutoff,))
        
        cursor.execute("SELECT COUNT(*) FROM choppingBlock;")
        n = cursor.fetchone()[0]
        if 0 == n:
            print(f"No EB rows found with ebSlot <= {cutoff}.")
            return

        if need_rebuild_index(n):
            print("Dropping index.")
            cursor.execute("DROP INDEX IF EXISTS idx_EB2TX_txHash")

        # EXPLAIN QUERY PLAN gives
        # 
        # |--SEARCH EB2TX USING COVERING INDEX sqlite_autoindex_EB2TX_1 (ebSlot=? AND ebHash=?)
        # `--USING INDEX sqlite_autoindex_choppingBlock_1 FOR IN-OPERATOR
        #
        # which looks healthy.
        cursor.execute('''
            DELETE FROM EB2TX 
            WHERE (ebSlot, ebHash) IN (
                SELECT ebSlot, ebHash FROM choppingBlock
            );
        ''')

        # EXPLAIN QUERY PLAN gives
        # 
        # |--SEARCH EB USING COVERING INDEX sqlite_autoindex_EB_1 (ebSlot=? AND ebHash=?)
        # `--USING INDEX sqlite_autoindex_choppingBlock_1 FOR IN-OPERATOR
        #
        # which looks healthy.
        cursor.execute('''
            DELETE FROM EB 
            WHERE (ebSlot, ebHash) IN (
                SELECT ebSlot, ebHash FROM choppingBlock
            );
        ''')

        conn.commit()
        locale.setlocale(locale.LC_TIME, "")
        print("")
        print(f"Deleted {n} EBs via cutoff {cutoff} at {datetime.datetime.now().strftime("%c")}")

        if need_rebuild_index(n):
            print("Building/rebuilding index on EB2TX.txHash.")
            print("This could take several minutes.")
        index_start = time.time()
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_EB2TX_txHash ON EB2TX(txHash)")
        conn.commit()
        print(f"Indexing took {time.time() - index_start:.1f}s.")

    except sqlite3.Error as e:
        # Roll back if anything goes wrong so we don't end up with orphaned rows
        conn.rollback()
        print(f"SQLite errored: {e}")
    finally:
        conn.close()

if __name__ == "__main__":
    db_name = sys.argv[1]
    cutoffSlot = int(round(float(sys.argv[2])))
    prune_ebs(db_name, cutoffSlot)
