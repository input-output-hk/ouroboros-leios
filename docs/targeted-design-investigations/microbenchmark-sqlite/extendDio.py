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

import numpy as np
import os
import tqdm
import sys

import ctypes


# Constants
PAGE_SIZE = 4096
ELEMENTS_TOTAL = 15000
HASH_SIZE = 32
INT_SIZE = 4
ELEM_SIZE = HASH_SIZE + INT_SIZE  # 36 bytes

# Alignment Logic
ELEMS_PER_PAGE = PAGE_SIZE // ELEM_SIZE  # 113 elements
NUM_PAGES = (ELEMENTS_TOTAL + ELEMS_PER_PAGE - 1) // ELEMS_PER_PAGE
BUFFER_SIZE = NUM_PAGES * PAGE_SIZE


def write_with_direct_io(buf, fd, sizes):
    # 2. Fill the buffer with elements and padding
    current_elem = 0
    for p in range(NUM_PAGES):
        page_offset = p * PAGE_SIZE
        for e in range(ELEMS_PER_PAGE):
            if current_elem >= ELEMENTS_TOTAL:
                break

            elem_offset = page_offset + (e * ELEM_SIZE)

            # Simulated 32-byte txHash
            hash_data = os.urandom(HASH_SIZE)
            # 4-byte integer (little endian)
            int_data = int(sizes[current_elem]).to_bytes(INT_SIZE, "little")

            # Place into buffer
            buf[elem_offset : elem_offset + HASH_SIZE] = hash_data
            buf[elem_offset + HASH_SIZE : elem_offset + ELEM_SIZE] = int_data

            current_elem += 1

    os.write(fd, buf)


def extend_database(db_name, num_ebs):
    rows_to_insert = num_ebs
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
    eb_data = [(int(slot), e_hash) for slot, e_hash in zip(eb_slots, eb_hashes)]

    # Open file with DIRECT flag
    # 1. Allocate page-aligned memory buffer
    # libc.posix_memalign requires: (pointer_to_mem, alignment, size)
    libc = ctypes.CDLL("libc.so.6")
    buf_ptr = ctypes.c_void_p()
    if libc.posix_memalign(ctypes.byref(buf_ptr), PAGE_SIZE, BUFFER_SIZE) != 0:
        raise MemoryError("Failed to allocate aligned memory")
    ctypes.memset(buf_ptr, 0, BUFFER_SIZE)

    # Create a buffer interface to the allocated memory
    BufferType = ctypes.c_char * BUFFER_SIZE
    buf = BufferType.from_address(buf_ptr.value)

    fd = os.open(db_name, os.O_WRONLY | os.O_CREAT | os.O_DIRECT)
    os.lseek(fd, 0, os.SEEK_END)

    # get all the per-EB disk allocation out of the way at once
    os.posix_fallocate(fd, 0, os.fstat(fd).st_size + rows_to_insert * BUFFER_SIZE)

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
            if True:  # 11995000 <= total <= 12000000:
                break

            # Dynamically adjust the alpha parameter based on how far off we are
            ratio = total / 11997500.0
            a *= ratio**0.5
            a = max(0.5, min(a, 3.0))

        eb_data2[i] = sizes

    for _, sizes in tqdm.tqdm(
        enumerate(eb_data2),
        desc="Writing",
        miniters=1,
        unit="",
        total=rows_to_insert,
        smoothing=0.01,
    ):
        write_with_direct_io(buf, fd, sizes)

    os.close(fd)


if __name__ == "__main__":
    filename = sys.argv[1]
    num_ebs = int(sys.argv[2])
    extend_database(db_name=filename, num_ebs=num_ebs)
