export class MemoryPool<T> {
  private items: T[] = [];
  public readonly capacity: number;

  constructor(capacity: number) {
    this.capacity = capacity;
  }

  enqueue(item: T): boolean {
    if (this.items.length >= this.capacity) {
      return false; // Queue is full
    }
    this.items.push(item);
    return true;
  }

  dequeue(): T | undefined {
    return this.items.shift();
  }

  peek(): T | undefined {
    return this.items[0];
  }

  get size(): number {
    return this.items.length;
  }

  isFull(): boolean {
    return this.items.length >= this.capacity;
  }
}
