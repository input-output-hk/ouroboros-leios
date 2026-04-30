import matplotlib.pyplot as plt
from matplotlib.widgets import Slider
import numpy as np
import sys


def plot_interactive_flipbook(file_pattern, upper_bound):
    if not file_list:
        print("No files given.")
        return

    # 2. Pre-load all data into memory so interactions are lightning fast
    all_col1, all_col2, file_names = [], [], []

    for fpath in file_list:
        c1, c2 = [], []
        with open(fpath, "r") as file:
            for line in file:
                parts = line.strip().split()
                if len(parts) >= 2:
                    try:
                        c1.append(float(parts[0]) * 1000)
                        c2.append(float(parts[1]) * 1000)
                    except ValueError:
                        continue
        if c1:  # Only save if the file actually contained valid data
            all_col1.append(c1)
            all_col2.append(c2)
            file_names.append(fpath)

    if not all_col1:
        print("No valid data found in the files.")
        return

    # 3. Setup the figure and make room for the slider at the bottom
    fig, ax = plt.subplots(figsize=(20, 12))

    # Static colors for the two columns
    color_col1 = "#0072B2"  # Color-blind friendly blue
    color_col2 = "black"

    # 4. Draw the initial plot (File Index 0)
    initial_time = np.arange(len(all_col1[0]))
    (line1,) = ax.plot(
        initial_time, all_col1[0], color=color_col1, lw=2, label="1st SELECT"
    )
    (line2,) = ax.plot(
        initial_time, all_col2[0], color=color_col2, alpha=0.5, lw=2, label="2nd SELECT"
    )

    ax.set_title(file_names[0])
    ax.set_xlabel("EB Index")
    ax.set_ylabel("SELECT duration (ms)")
    ax.legend()
    ax.grid(True, linestyle="--", alpha=0.5)

    # 5. Lock the axes limits based on global minimums and maximums
    max_len = max(len(c) for c in all_col1)
    global_min = min(min(c1 + c2) for c1, c2 in zip(all_col1, all_col2))
    global_max = max(max(c1 + c2) for c1, c2 in zip(all_col1, all_col2))
    global_max = global_max if upper_bound is None else min(upper_bound, global_max)

    padding = (global_max - global_min) * 0.05
    if padding == 0:
        padding = 1.0  # Edge case fallback if all data is perfectly flat

    ax.set_xlim(0, max_len)
    ax.set_ylim(0, global_max + padding)

    # 6. Create the Slider UI
    if 1 < len(file_names):
        plt.subplots_adjust(bottom=0.25)

        ax_slider = plt.axes([0.2, 0.1, 0.65, 0.03])
        slider = Slider(
            ax=ax_slider,
            label="File Index",
            valmin=0,
            valmax=len(file_names) - 1,
            valinit=0,
            valstep=1,  # Snaps to whole numbers only
        )

        # 7. Define the update function triggered by the slider
        def update(val):
            idx = int(slider.val)
            current_time = np.arange(len(all_col1[idx]))

            # Update the line data (colors remain static now)
            line1.set_data(current_time, all_col1[idx])
            line2.set_data(current_time, all_col2[idx])

            # Update the title
            ax.set_title(file_names[idx])

            # Redraw the canvas
            fig.canvas.draw_idle()

        # Register the update function
        slider.on_changed(update)

        # 8. Add keyboard bindings for left/right arrows
        def on_key(event):
            current_val = slider.val
            if event.key == "right":
                # Move forward, capping at the maximum index
                new_val = min(current_val + 1, slider.valmax)
                slider.set_val(new_val)
            elif event.key == "left":
                # Move backward, capping at the minimum index
                new_val = max(current_val - 1, slider.valmin)
                slider.set_val(new_val)

        # Connect the key press event to the figure
        fig.canvas.mpl_connect("key_press_event", on_key)

    mng = plt.get_current_fig_manager()
    mng.window.wm_geometry("+50+50")  # Set top-left position
    plt.show()


if __name__ == "__main__":
    upper_bound = None
    file_list = sys.argv[1:]
    # A first argument of -98.9 bounds the y-axis to ≤ 98.9, for example.
    if file_list[0].startswith("-"):
        upper_bound = float(file_list[0][1:])
        file_list = file_list[1:]
    plot_interactive_flipbook(file_list, upper_bound)
