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

  // Call this on the first node in a list
  toArray() {
    let answer = [];
    let node = this;
    while (node) {
      answer.push(node.value);
      node = node.next;
    }
    return answer;
  }

  join(connector) {
    return this.toArray().join(connector);
  }

  // Returns a new DLL with this value inserted at the beginning
  // Can only be called on the head
  // Returns the new head
  prepend(value) {
    if (this.prev) {
      throw new Error('prepend should only be called on the head');
    }
    let newNode = new DLL(value, null, this);
    this.prev = newNode;
    return newNode;
  }

  // Returns a new DLL with this value appended at the end
  // Can only be called on the tail
  // Returns the new tail
  append(value) {
    if (this.next) {
      throw new Error('append should only be called on the tail');
    }
    let newNode = new DLL(value, this, null);
    this.next = newNode;
    return newNode;
  }
}

// TODO: test this
module.exports = DLL;
