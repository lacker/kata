function equal(tree1, tree2) {
  if (!tree1 && !tree2) {
    return true;
  }
  if (!tree1 || !tree2) {
    return false;
  }
  if (tree1.value !== tree2.value) {
    return false;
  }
  return equal(tree1.left, tree2.left) && equal(tree1.right, tree2.right);
}

module.exports = equal;
