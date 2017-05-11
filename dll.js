// A doubly-linked list class.
// Each item has prev, next, and value.
class DLL {
  constructor(value, prev, next) {
    this.value = value;
    this.prev = prev || null;
    this.next = next || null;
  }

  // Removes this node from a DLL
  // The prev and next will still be valid after removal.
  remove() {
    let prev = this.prev;
    let next = this.next;
    if (prev) {
      this.prev.next = next;
    }
    if (next) {
      this.next.prev = prev;
    }
  }

  // Returns a new DLL with this value inserted at the beginning
  // Can only be called on the head
  prepend(value) {
    if (this.prev) {
      throw new Error('prepend should only be called on the head');
    }
    let newNode = new DLL(value, null, this);
    this.prev = newNode;
    return newNode;
  }
}

// TODO: test this
module.exports = DLL;
