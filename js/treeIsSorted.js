// Returns an object with
// min: the min value of the tree
// sorted: whether the tree is sorted
// max: the max value of the tree
// If sorted is false the others aren't needed
function helper(tree) {
  if (!tree) {
    return { sorted: true };
  }
  let left = helper(tree.left);
  if (!left.sorted || left.max > tree.value) {
    return { sorted: false };
  }
  let right = helper(tree.right);
  if (!right.sorted || right.min < tree.value) {
    return { sorted: false };
  }
  return {
    min: left.min || tree.value,
    sorted: true,
    max: right.max || tree.value,
  };
}

function isSorted(tree) {
  let data = helper(tree);
  return data.sorted;
}

module.exports = isSorted;
