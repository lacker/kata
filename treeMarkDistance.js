// Given the root of a binary tree with 2 marked nodes, determine the
// length of the path between the 2 marked nodes.
// marked nodes are just ones with "mark: true".

// This recursive function returns info to help solve the problem.
// If there are two marked nodes it returns { answer: answer }.
// If there is only one marked node it returns { depth: depth }.
// If there are no marked nodes it returns { empty: true }.
// Assumes there are at most two marked nodes.
function helper(tree) {
  if (!tree) {
    return { empty: true };
  }
  let left = helper(tree.left);
  if (left.answer) {
    return left;
  }
  let right = helper(tree.right);
  if (right.answer) {
    return right;
  }

  if (left.empty && right.empty) {
    if (tree.marked) {
      return { depth: 0 };
    } else {
      return { empty: true };
    }
  }

  if (left.depth !== undefined && right.depth !== undefined) {
    return { answer: 2 + left.depth + right.depth };
  }

  // The last case: there is precisely one marked node between left and
  // right subtrees
  let treeWithMark = left.empty ? right : left;
  if (tree.marked) {
    return { answer: treeWithMark.depth };
  } else {
    return { depth: treeWithMark.depth + 1 };
  }
}

function treeMarkDistance(tree) {
  let data = helper(tree);
  if (tree.answer === undefined) {
    return -1;
  }
  return tree.answer;
}

module.exports = treeMarkDistance;
