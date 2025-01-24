import { useSimContext } from "@/contexts/SimContext/context";
import { FC } from "react";
import { Bar, BarChart, Legend, Tooltip, XAxis, YAxis } from "recharts";

export const BlocksView: FC = ({ }) => {
    const {
        state: {
            aggregatedData: {
                blocks,
            }
        }
    } = useSimContext();

    return (
        <div className="flex flex-col w-full h-4/5 items-center justify-center">
            <h1>Transactions Per Block</h1>
            <BarChart width={640} height={480} data={blocks}>
                <XAxis dataKey="slot" />
                <YAxis />
                <Tooltip />
                <Legend />
                <Bar dataKey="praosTx" name={"Praos TXs"} fill="#8884d8" />
                <Bar dataKey="leiosTx" name={"Leios TXs"} fill="#82ca9d" />
            </BarChart>
        </div>
    )
}