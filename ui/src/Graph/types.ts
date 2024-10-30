export interface INodeMap {
    nodes: {
        location: number[];
        stake?: number;
    }[];
    links: {
        nodes: number[];
        id?: number;
    }[]
}

export enum EMessageType {
    TransactionGenerated = "TransactionGenerated",
    TransactionReceived = "TransactionReceived",
    InputBlockReceived = "InputBlockReceived",
    PraosBlockReceived = "PraosBlockReceived",
    Slot = "Slot",
    InputBlockGenerated = "InputBlockGenerated"
}

export interface ITransactionGenerated {
    type: EMessageType.TransactionGenerated,
    data: {
        id: number;
        publisher: number;
        bytes: number;
    }
}

export interface ITransactionReceived {
    type: EMessageType.TransactionReceived,
    data: {
        id: number;
        sender: number;
        recipient: number;
    }
}

export interface IInputBlockReceived {
    type: EMessageType.InputBlockReceived,
    data: {
        slot: number;
        producer: number;
        index: number;
        sender: number;
        recipient: number;
    }
}

export interface IPraosBlockReceived {
    type: EMessageType.PraosBlockReceived,
    data: {
        slot: number;
        sender: number;
        recipient: number;
    }
}

export interface ISlot {
    type: EMessageType.Slot,
    data: {
        number: number;
    }
}

export interface IInputBlockGenerated {
    type: EMessageType.InputBlockGenerated,
    data: {
        slot: number;
        producer: number;
        index: number;
        vrf: number;
        timestamp: number;
        transactions: number[];
    }
}

export type TMessageType = IInputBlockGenerated | IInputBlockReceived | IPraosBlockReceived | ISlot | ITransactionGenerated | ITransactionReceived;

export interface IMessage {
    time: number;
    message: TMessageType;
}