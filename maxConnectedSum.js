// Code to find the maximum sum of any connected subgraph of a tree.

// Returns an object with:
// root: the max connected sum including the root node
// any: the max connected sum of any subgroup
function helper(tree) {
  if (!tree) {
    return {
      root: 0,
      any: 0,
    };
  }

  let left = helper(tree.left);
  let right = helper(tree.right);

  // Figure out the max connected sum including the root node
  let root = tree.value;
  if (left.root > 0) {
    root += left.root;
  }
  if (right.root > 0) {
    root += right.root;
  }

  return {
    root: root,
    any: Math.max(left.any, right.any, root),
  };
}

function maxConnectedSum(tree) {
  return helper(tree).any;
}

module.exports = maxConnectedSum;
