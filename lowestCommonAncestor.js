// All of these assume the tree has no duplicates

// Returns an object with:
// lca: the lca of the two nodes, if it's known
// num: the number of value1 and value2 that is in the tree
function helper(tree, value1, value2) {
  if (!tree) {
    return {
      num: 0,
    };
  }
  let left = helper(tree.left, value1, value2);
  if (left.lca) {
    return left;
  }
  let right = helper(tree.right, value1, value2);
  if (right.lca) {
    return right;
  }
  let thisNum = (tree.value === value1 || tree.value === value2) ? 1 : 0;
  let num = left.num + right.num + thisNum;
  if (num >= 2) {
    return {
      lca: tree,
      num: num
    };
  }
  return {
    num: num
  };
}

// Returns the lowest common ancestor.
function lca(tree, value1, value2) {
  let data = helper(tree, value1, value2);
  return data.lca;
}

module.exports = lca;
