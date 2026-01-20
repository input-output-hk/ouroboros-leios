// Theme colors from Leios site
const COLORS = {
  background: '#200830',
  border: '#45364e',
  text: '#f8f6fa',
  textMuted: '#8f6dae',
  honest: '#6effd1',
  adversary: '#ef4444',
};

interface PeerInfoProps {
  selectedNode: {
    id: string;
    honest: boolean;
    upstream: string[];
    downstream: string[];
  };
  onClose: () => void;
  onSelectPeer?: (peerId: string) => void;
}

interface PeerCircleProps {
  id: string;
  onClick?: () => void;
}

function PeerCircle({ id, onClick }: PeerCircleProps) {
  const isAdversary = id.startsWith('A');
  return (
    <button
      onClick={onClick}
      className="flex flex-col items-center gap-0.5 cursor-pointer hover:opacity-80 transition-opacity"
    >
      <div
        className="w-6 h-6 rounded-full flex items-center justify-center"
        style={{
          backgroundColor: isAdversary ? COLORS.adversary : COLORS.honest,
          border: `2px solid ${isAdversary ? '#f87171' : '#a7ffe8'}`,
        }}
      />
      <span
        className="text-[9px] font-mono"
        style={{ color: isAdversary ? COLORS.adversary : COLORS.text }}
      >
        {id}
      </span>
    </button>
  );
}

export function PeerInfo({ selectedNode, onClose, onSelectPeer }: PeerInfoProps) {
  return (
    <div className="p-2 rounded" style={{ backgroundColor: COLORS.background }}>
      <div className="flex justify-between items-center mb-2">
        <span className="text-xs" style={{ color: COLORS.textMuted }}>Node Peers</span>
        <button
          onClick={onClose}
          className="text-sm px-1 hover:opacity-80 cursor-pointer"
          style={{ color: COLORS.textMuted }}
        >
          ✕
        </button>
      </div>

      {/* Upstream */}
      <div className="mb-2">
        <div className="text-xs mb-1.5 text-center" style={{ color: COLORS.textMuted }}>
          Upstream ({selectedNode.upstream.length})
        </div>
        <div className="flex flex-wrap gap-2 justify-center min-h-8">
          {selectedNode.upstream.length > 0 ? (
            selectedNode.upstream.map((peer) => (
              <PeerCircle
                key={peer}
                id={peer}
                onClick={() => onSelectPeer?.(peer)}
              />
            ))
          ) : (
            <span className="text-xs" style={{ color: COLORS.border }}>None</span>
          )}
        </div>
      </div>

      {/* Arrow down */}
      <div className="flex justify-center text-xs" style={{ color: COLORS.border }}>↓</div>

      {/* Selected node */}
      <div className="flex flex-col items-center my-2">
        <div
          className="w-10 h-10 rounded-full flex items-center justify-center"
          style={{
            backgroundColor: selectedNode.honest ? COLORS.honest : COLORS.adversary,
            border: `3px solid ${selectedNode.honest ? '#a7ffe8' : '#f87171'}`,
          }}
        />
        <span
          className="text-xs font-mono font-bold mt-1"
          style={{ color: selectedNode.honest ? COLORS.honest : COLORS.adversary }}
        >
          {selectedNode.id}
        </span>
      </div>

      {/* Arrow down */}
      <div className="flex justify-center text-xs" style={{ color: COLORS.border }}>↓</div>

      {/* Downstream */}
      <div className="mt-2">
        <div className="text-xs mb-1.5 text-center" style={{ color: COLORS.textMuted }}>
          Downstream ({selectedNode.downstream.length})
        </div>
        <div className="flex flex-wrap gap-2 justify-center min-h-8">
          {selectedNode.downstream.length > 0 ? (
            selectedNode.downstream.map((peer) => (
              <PeerCircle
                key={peer}
                id={peer}
                onClick={() => onSelectPeer?.(peer)}
              />
            ))
          ) : (
            <span className="text-xs" style={{ color: COLORS.border }}>None</span>
          )}
        </div>
      </div>
    </div>
  );
}
