import { type Dispatch, type DragEventHandler, type FC, type MouseEventHandler, type SetStateAction } from "react";

interface ISliderProps {
    max?: number;
    value: number;
    setValue: Dispatch<SetStateAction<number>>;
}

/** Built with AI !! */
export const Slider: FC<ISliderProps> = ({
    max = 100,
    value,
    setValue
}) => {
    const min = 0;
    const step = 1;

    const handleClick: MouseEventHandler<HTMLDivElement> = (e) => {
        // Get the slider's bounding rectangle
        const rect = e.currentTarget.getBoundingClientRect();
        // Calculate the click position relative to the slider
        const position = e.clientX - rect.left;
        // Convert position to a percentage
        const percentage = position / rect.width;
        // Convert percentage to value within range
        const newValue = Math.round((percentage * (max - min) + min) / step) * step;
        // Clamp value between min and max
        const finalValue = Math.min(Math.max(newValue, min), max);
        setValue(finalValue);
    };

    // Prevent default drag behavior
    const preventDrag: DragEventHandler<HTMLDivElement> = (e) => {
        e.preventDefault();
    };

    return (
        <div className="w-full mx-auto p-4">
            <div
                className="relative w-full h-12 cursor-pointer"
                onClick={handleClick}
                onDragStart={preventDrag}
            >
                {/* Track */}
                <div className="absolute top-1/2 left-0 w-full h-2 -mt-1 rounded-full bg-gray-200">
                    {/* Filled portion */}
                    <div
                        className="absolute h-full rounded-full bg-blue-500"
                        style={{ width: `${(value - min) / (max - min) * 100}%` }}
                    />
                </div>
                {/* Thumb */}
                <div
                    className="absolute top-1/2 -mt-4 w-8 h-8 rounded-full bg-white border-2 border-blue-500 shadow flex items-center justify-center"
                    style={{ left: `calc(${(value - min) / (max - min) * 100}% - 12px)` }}
                >
                    <div className="text-sm">
                        {value}
                    </div>
                    <div className="absolute bg-white p-4 rounded-md shadow-lg top-full mt-2 w-[140px] text-center text-xs">
                        Incoming Message
                    </div>
                </div>
            </div>
        </div>
    );
};