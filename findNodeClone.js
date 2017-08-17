// Add "parent" links to a tree.
// For the root, parent should be null.
addParentLinks(tree, parent) {
  if (!tree) {
    return;
  }
  tree.parent = parent;
  addParentLinks(tree.left);
  addParentLinks(tree.right);
}
