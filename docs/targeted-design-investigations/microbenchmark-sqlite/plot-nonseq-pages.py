# This script plots the data in the result of
#
# python plot-nonseq-pages.py <(grep -E -e 'Non-sequential pages\.* [0-9]' info-{0..50}-StartSmall.sqlite.sql | awk '{print $4}' | tr -d %)

import matplotlib.pyplot as plt
import sys


def plot_interleaved_sequences(file_path):
    # 1. Read the numbers from the text file
    with open(file_path, "r") as file:
        # Read lines, strip whitespace, and convert to float (ignoring empty lines)
        data = [float(line.strip()) for line in file if line.strip()]

    # 2. De-interleave the sequences using Python slicing
    # list[start::step] grabs every 3rd element starting from 'start'
    n = 5
    seq = [None] * n
    for i in range(n):
        seq[i] = data[i::n]

    # 3. Plot the sequences
    plt.figure(figsize=(10, 6))

    #    plt.plot(seq[0], label='EB', marker='x', linestyle='--')
    #    plt.plot(seq[1], label='EB automatic', marker='o', linestyle='-')
    plt.plot(seq[2], label="EB2TX", marker="x", linestyle="--")
    plt.plot(seq[3], label="IDX_EB2TX_TXHASH", marker="o", linestyle="-")
    plt.plot(seq[4], label="EB2TX automatic", marker="o", linestyle="-")

    # 4. Add formatting to the plot
    plt.title(file_path)
    plt.xlabel("Iteration")
    plt.ylabel("Non-sequential pages (%)")
    plt.legend()
    plt.grid(True)

    # 5. Save or show the plot
    # plt.savefig('sequences_plot.png') # Uncomment to save to a file
    plt.show()


if __name__ == "__main__":
    plot_interleaved_sequences(sys.argv[1])
