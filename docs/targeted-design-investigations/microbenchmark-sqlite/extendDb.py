# Generate a worst-case Leios database file.
#
# This script started as a Gemini Pro 3 response to the prompt in
# GeminiLog.txt. Then I manually tweaked it.
#
# - I abstracted out NumEBs.  I did not abstract out NumTXs, because
#   it wasn't trivial to alter the 12 MB targetting, for example.
#
# - I switched from manual progress reporting to tqdm.
#
# - I added the CLI argument.
#
# - I made it add to an existing database instead of only building from scratch.
#
# - I set it to WAL.

import datetime
import locale
import numpy as np
import os
import sqlite3
import time
import tqdm
import sys


def need_rebuild_index(n):
    n > 3000  # TODO tune this threshold


def extend_database(db_name, num_ebs):
    conn = sqlite3.connect(db_name)
    cursor = conn.cursor()

    # Assume WAL and then optimize for massive bulk data insertion.
    #
    # TODO this is too aggressive for the actual implementation, but
    # we're being generous for the benchmark.
    cursor.executescript(
        """
        PRAGMA journal_mode=WAL;
        PRAGMA synchronous = 0;
        PRAGMA cache_size = 1000000;
        PRAGMA locking_mode = EXCLUSIVE;
        PRAGMA temp_store = MEMORY;
    """
    )

    cursor.executescript(
        """
        CREATE TABLE IF NOT EXISTS EB (
            ebSlot INTEGER,
            ebHash BLOB,
            PRIMARY KEY (ebSlot, ebHash)
        );

        CREATE TABLE IF NOT EXISTS EB2TX (
            ebSlot INTEGER,
            ebHash BLOB,
            txIndex INTEGER,
            txHash BLOB,
            txBytesSize INTEGER,
            PRIMARY KEY (ebSlot, ebHash, txIndex),
            FOREIGN KEY (ebSlot, ebHash) REFERENCES EB(ebSlot, ebHash)
        );
    """
    )

    # ---------------------------------------------------------
    # 1. Check existing state and calculate remaining rows
    # ---------------------------------------------------------
    cursor.execute("SELECT COUNT(*), MIN(ebSlot), MAX(ebSlot) FROM EB")
    current_count, min_slot, max_slot = cursor.fetchone()

    rows_to_insert = num_ebs - current_count
    if rows_to_insert <= 0:
        print(f"Database already contains {num_ebs} or more EB rows. Exiting.")
        return

    if need_rebuild_index(rows_to_insert):
        print("Dropping index.")
        cursor.execute("DROP INDEX IF EXISTS idx_EB2TX_txHash")

    # Handle empty DB vs existing DB
    if min_slot is None:
        min_slot = 1000000
        max_slot = 1000000

    print(f"Generating {rows_to_insert} EB slots...")

    count1 = int(rows_to_insert * 0.324)
    count2 = rows_to_insert - count1

    # The new gaps can only sum up to whatever is left of the global 129600 limit
    current_diff = max_slot - min_slot
    global_target_diff = 129550  # Aim near 129600
    allowed_growth = max(global_target_diff - current_diff, 0)

    gaps1 = np.random.poisson(20.0, count1)

    # Prevent gaps1 from immediately exceeding the allowed growth
    if gaps1.sum() > allowed_growth:
        gaps1 = (gaps1 * (allowed_growth / max(gaps1.sum(), 1))).astype(int)

    target_remaining = allowed_growth - gaps1.sum()
    mean2 = max(target_remaining / max(count2, 1), 0.1)
    gaps2 = np.random.poisson(mean2, count2)

    # Use a random order, because the adversary could ultimately cause significant reordering
    #
    # TODO a refactor screwed this up: this shuffle used to shuffle
    # the slots, but not it's meaninglessly shuffling the gaps
    all_gaps = np.concatenate([gaps1, gaps2])
    np.random.default_rng().shuffle(all_gaps)

    # Strictly enforce that global max - global min <= 129600
    max_allowed_sum = 129600 - current_diff
    while all_gaps.sum() > max_allowed_sum:
        idx = np.random.randint(0, rows_to_insert)
        if all_gaps[idx] > 0:
            all_gaps[idx] -= 1

    # Pair slots and hashes for database insertion
    eb_slots = max_slot + np.cumsum(all_gaps)
    eb_hashes = [os.urandom(32) for _ in range(rows_to_insert)]
    eb_data = list((int(slot), e_hash) for slot, e_hash in zip(eb_slots, eb_hashes))

    sqltime1 = time.time()
    cursor.executemany("INSERT INTO EB (ebSlot, ebHash) VALUES (?, ?)", eb_data)
    conn.commit()
    sqltime2 = time.time()
    print(f"Completed {len(eb_data)} INSERTs INTO table EB.")
    print("")

    # ---------------------------------------------------------
    # 2. Generate EB2TX data (15000 * rows_to_insert rows)
    # ---------------------------------------------------------
    print(f"Generating and inserting EB2TX data ({15000 * len(eb_data)} rows).")
    print(
        "For 10000 EBs, this generated a ~27.5 GB file and took about ~30 minutes with a nice-ish NVMe drive."
    )
    print("")

    tx_indices = np.arange(15000, dtype=int)

    eb_data2 = [None] * rows_to_insert
    for i, (slot, e_hash) in tqdm.tqdm(
        enumerate(eb_data),
        desc="Generating",
        miniters=1,
        unit="",
        total=rows_to_insert,
        smoothing=0.01,
    ):
        # We use an adaptive feedback loop to find the perfect Pareto shape (alpha `a`)
        # so that the sum of the power-law distribution falls naturally into our target.
        # This preserves the pure mathematical distribution without harsh post-clipping artifacts.
        a = 1.05
        while True:
            # np.random.pareto is Lomax distribution, adding 1 and multiplying by 50
            # creates a standard Pareto with a minimum of exactly 50.
            sizes = ((np.random.pareto(a, 15000) + 1) * 50).astype(int)
            sizes = np.clip(sizes, 50, 16384)
            total = sizes.sum()

            # Very near 12 MB, but no greater
            if (
                True
            ):  # 11995000 <= total <= 12000000:   # FYI, replacing this with True was about 17x faster
                break

            # Dynamically adjust the alpha parameter based on how far off we are
            ratio = total / 11997500.0
            a *= ratio**0.5
            a = max(0.5, min(a, 3.0))

        eb_data2[i] = list(
            (slot, e_hash, int(idx), int(size)) for idx, size in zip(tx_indices, sizes)
        )

    sqltime3 = time.time()
    for i, batch in tqdm.tqdm(
        enumerate(eb_data2),
        desc="Writing",
        miniters=1,
        unit="",
        total=rows_to_insert,
        smoothing=0.01,
    ):
        cursor.executemany(
            """
            INSERT INTO EB2TX (ebSlot, ebHash, txIndex, txHash, txBytesSize)
            VALUES (?, ?, ?, randomblob(32), ?)
        """,
            batch,
        )

        # Commit periodically to flush from memory to disk
        if (i + 1) % 500 == 0:
            conn.commit()
    conn.commit()
    sqltime4 = time.time()
    locale.setlocale(locale.LC_TIME, "")
    print("")
    print(
        f"Completed INSERTs INTO table EB2TX at {datetime.datetime.now().strftime("%c")}"
    )

    # ---------------------------------------------------------
    # 3. Create Index
    # ---------------------------------------------------------
    print("Building/rebuilding index on EB2TX.txHash.")
    if need_rebuild_index(rows_to_insert):
        print("This could take several minutes.")
    sqltime5 = time.time()
    cursor.execute("CREATE INDEX IF NOT EXISTS idx_EB2TX_txHash ON EB2TX(txHash)")
    conn.commit()
    sqltime6 = time.time()

    conn.close()
    print("")
    print(
        f"Done creating/updating {db_name} after ({sqltime2 - sqltime1:.1f}, {sqltime4 - sqltime3:.1f}, {sqltime6 - sqltime5:.1f})"
    )


if __name__ == "__main__":
    filename = sys.argv[1]
    num_ebs = int(sys.argv[2])
    extend_database(db_name=filename, num_ebs=num_ebs)
