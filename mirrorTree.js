function mirrorTree(tree) {
  if (!tree) {
    return null;
  }
  return {
    value: tree.value,
    left: mirrorTree(tree.right),
    right: mirrorTree(tree.left),
  };
}

module.exports = mirrorTree;
