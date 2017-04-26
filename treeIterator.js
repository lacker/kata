class TreeIterator {
  constructor(root) {
    this.stack = [];
    while (root) {
      this.stack.push(root);
      root = root.left;
    }
  }

  endOfPath() {
    return this.stack[this.stack.length - 1];
  }

  // Throws an error when there is no next value,
  // same error as popping from an empty list
  nextValue() {
    let current = this.stack.pop();
    if (!current) {
      throw new Error('end of iteration');
    }
    let returnValue = current.value;
    if (current.right) {
      let node = current.right;
      while (node) {
        this.stack.push(node);
        node = node.left;
      }
    }
    return returnValue;
  }
}

module.exports = TreeIterator;

