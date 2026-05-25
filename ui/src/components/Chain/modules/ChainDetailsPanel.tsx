"use client";

import { useSimContext } from "@/contexts/SimContext/context";
import { printBytes } from "@/utils";
import { FC, useMemo } from "react";

const Row: FC<{ label: string; children: React.ReactNode }> = ({
  label,
  children,
}) => (
  <div className="grid grid-cols-[100px_1fr] gap-2 py-1 text-xs">
    <span className="text-gray-500">{label}</span>
    <span className="font-mono break-all">{children}</span>
  </div>
);

export const ChainDetailsPanel: FC = () => {
  const {
    state: {
      aggregatedData: { chain },
      selectedBlock,
    },
    dispatch,
  } = useSimContext();

  const data = useMemo(() => {
    if (!selectedBlock) return undefined;
    if (selectedBlock.kind === "rb") {
      const rb = chain.rbs.get(selectedBlock.id);
      return rb ? { kind: "rb" as const, rb } : undefined;
    }
    const eb = chain.ebs.get(selectedBlock.id);
    return eb ? { kind: "eb" as const, eb } : undefined;
  }, [selectedBlock, chain]);

  if (!data) return null;

  const selectRb = (id: string) =>
    dispatch({ type: "SET_SELECTED_BLOCK", payload: { kind: "rb", id } });
  const selectEb = (id: string) =>
    dispatch({ type: "SET_SELECTED_BLOCK", payload: { kind: "eb", id } });

  const link = (
    label: string,
    onClick: () => void,
    exists: boolean,
  ) => (
    <button
      type="button"
      onClick={onClick}
      disabled={!exists}
      className="text-blue-600 hover:underline disabled:text-gray-400 disabled:no-underline text-left"
    >
      {label}
    </button>
  );

  return (
    <div className="border-2 border-gray-200 rounded-sm p-4 z-30 bg-white/90 backdrop-blur-xs w-80 max-h-[80vh] overflow-y-auto">
      <div className="flex items-center justify-between mb-2">
        <h2 className="font-bold uppercase">
          {data.kind === "rb" ? "Ranking Block" : "Endorser Block"}
        </h2>
        <button
          type="button"
          onClick={() => dispatch({ type: "SET_SELECTED_BLOCK", payload: undefined })}
          className="text-gray-500 hover:text-black text-xs"
        >
          Close
        </button>
      </div>
      {data.kind === "rb" ? (
        <>
          <Row label="ID">{data.rb.id}</Row>
          <Row label="Slot">{data.rb.slot}</Row>
          {data.rb.blockNumber !== undefined ? (
            <Row label="Block #">{data.rb.blockNumber}</Row>
          ) : null}
          <Row label="Producer">{data.rb.producer}</Row>
          <Row label="Size">{printBytes(data.rb.sizeBytes)}</Row>
          <Row label="Parent">
            {data.rb.parentId
              ? link(
                  data.rb.parentId,
                  () => selectRb(data.rb.parentId!),
                  chain.rbs.has(data.rb.parentId),
                )
              : "—"}
          </Row>
          <Row label="Certifies EB">
            {data.rb.certifiesEbId
              ? link(
                  data.rb.certifiesEbId,
                  () => selectEb(data.rb.certifiesEbId!),
                  chain.ebs.has(data.rb.certifiesEbId),
                )
              : "—"}
          </Row>
          <Row label="Announces EB">
            {data.rb.announcesEbId
              ? link(
                  data.rb.announcesEbId,
                  () => selectEb(data.rb.announcesEbId!),
                  chain.ebs.has(data.rb.announcesEbId),
                )
              : "—"}
          </Row>
        </>
      ) : (
        <>
          <Row label="ID">{data.eb.id}</Row>
          <Row label="Slot">{data.eb.slot}</Row>
          <Row label="Producer">{data.eb.producer}</Row>
          <Row label="Size">{printBytes(data.eb.sizeBytes)}</Row>
        </>
      )}
    </div>
  );
};
