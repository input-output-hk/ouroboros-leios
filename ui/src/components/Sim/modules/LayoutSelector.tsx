import { useSimContext } from "@/contexts/SimContext/context";
import { LayoutMode } from "@/contexts/SimContext/types";
import { FC } from "react";

export const LayoutSelector: FC = () => {
  const {
    state: { layoutMode },
    dispatch,
  } = useSimContext();

  return (
    <div className="flex items-center justify-start gap-3 border-2 rounded-md p-4 border-gray-200 bg-white/80 backdrop-blur-xs">
      <label htmlFor="layout" className="text-gray-900">
        Layout
      </label>
      <select
        id="layout"
        className="text-lg rounded-md font-medium transition-all duration-150 bg-transparent border border-gray-300 hover:border-gray-400 text-gray-900 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500 px-3 py-2 cursor-pointer"
        value={layoutMode}
        onChange={(e) =>
          dispatch({
            type: "SET_LAYOUT_MODE",
            payload: e.target.value as LayoutMode,
          })
        }
      >
        <option value="original">Original</option>
        <option value="auto">Auto</option>
        <option value="circular">Circular</option>
        <option value="mercator">Mercator</option>
      </select>
    </div>
  );
};
