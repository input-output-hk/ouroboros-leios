import { useGraphContext } from "@/contexts/GraphContext/context";
import { type FC } from "react";

/** Built with AI !! */
export const Slider: FC = () => {
    const min = 0;
    const { state: { currentTime, maxTime } } = useGraphContext();

    // const handleClick: MouseEventHandler<HTMLDivElement> = (e) => {
    //     // Get the slider's bounding rectangle
    //     const rect = e.currentTarget.getBoundingClientRect();
    //     // Calculate the click position relative to the slider
    //     const position = e.clientX - rect.left;
    //     // Convert position to a percentage
    //     const percentage = position / rect.width;
    //     // Convert percentage to value within range
    //     const newValue = Math.round((percentage * (max - min) + min) / step) * step;
    //     // Clamp value between min and max
    //     const finalValue = Math.min(Math.max(newValue, min), max);
    //     setValue(finalValue);
    // };

    // // Prevent default drag behavior
    // const preventDrag: DragEventHandler<HTMLDivElement> = (e) => {
    //     e.preventDefault();
    // };

    return (
        <div className="w-full mx-auto p-4">
          Time in Milliseconds: {currentTime}
            <div
                className="relative w-full h-12 cursor-pointer"
                draggable={false}
                onDragStart={e => e.preventDefault()}
            >
                {/* Track */}
                <div className="absolute top-1/2 left-0 w-full h-2 -mt-1 rounded-full bg-gray-200">
                    {/* Filled portion */}
                    <div
                        className="absolute h-full rounded-full bg-blue-500"
                        style={{ width: `${(currentTime - min) / (maxTime - min) * 100}%` }}
                    />
                </div>
                {/* Thumb */}
                {/* <div
                    className="absolute top-1/2 -mt-2 w-4 h-4 rounded-full bg-blue-500 shadow flex items-center justify-center"
                    style={{ left: `calc(${(value - min) / (max - min) * 100}% - 12px)` }}
                >
                    <div className="absolute bg-white p-4 rounded-md shadow-lg top-full mt-2 w-[140px] text-center text-xs">
                        Frame: {value}
                    </div>
                </div> */}
            </div>
        </div>
    );
};
