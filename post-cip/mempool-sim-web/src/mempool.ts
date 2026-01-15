export class MemoryPool<T> {

  private items: T[] = [];

  private size_B: number;
  
  public readonly capacity_B: number;

  constructor(capacity_B: number) {
    this.size_B = 0;
    this.capacity_B = capacity_B;
  }

  enqueue(item: T, item_B: number): boolean {
    if (this.size_B + item_B > this.capacity_B) {
      return false;
    }
    this.items.push(item);
    this.size_B += item_B;
    return true;
  }

  dequeue(): T | undefined {
    return this.items.shift();
  }

  peek(): T | undefined {
    return this.items[0];
  }

  getSize_B(): number {
    return this.size_B;
  }

}
