// Converts a tree to a doubly-linked list with the provided left and right
// nodes.
// left and right and tree can all be null
function helper(tree, left, right) {
  // Base case
  if (tree === null) {
    if (left !== null) {
      left.right = right;
    }
    if (right !== null) {
      right.left = left;
    }
    return;
  }

  // Handle the left side
  if (tree.left === null) {
    tree.left = left;
    if (left !== null) {
      left.right = tree;
    }
  } else {
    helper(tree.left, left, tree);
  }

  // Handle the right side
  if (tree.right === null) {
    tree.right = right;
    if (right !== null) {
      right.left = tree;
    }
  } else {
    helper(tree.right, tree, right);
  }
}

// Converts a tree to a doubly-linked list
function treeToList(tree) {
  helper(tree, null, null);
}

module.exports = treeToList;

// TODO: test
