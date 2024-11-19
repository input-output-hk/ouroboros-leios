import { FC, useRef } from "react";

export const Canvas: FC = () => {
  const canvasRef = useRef(null);
  return (
    <div className="h-[80vh] border-2 border-gray-200 rounded mb-8 w-2/3">
      <div className="flex items-center justify-center gap-4 mt-4">
        {/* <div>
          <h4>Transactions Generated: {generatedTxs.size}</h4>
        </div>
        <div>
          <h4>Transactions Sent: {sentTxs.size}</h4>
        </div> */}
      </div>
      <canvas ref={canvasRef} />
    </div>
  )
}
