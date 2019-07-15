// Makes a tree from an inorder and a preorder traversal.
// Assumes all values are distinct
// Note this could be more efficient with less list-copying
function makeTree(inorder, preorder) {
  if (inorder.length !== preorder.length) {
    throw new Error('inorder length should equal preorder length');
  }
  if (inorder.length === 0) {
    return null;
  }
  let rootValue = preorder[0];
  let index = inorder.indexOf(rootValue);
  let leftInorder = inorder.slice(0, index);
  let rightInorder = inorder.slice(index + 1);
  let leftPreorder = preorder.slice(1, index + 1);
  let rightPreorder = preorder.slice(index + 1);
  return {
    value: rootValue,
    left: makeTree(leftInorder, leftPreorder),
    right: makeTree(rightInorder, rightPreorder),
  };
}

module.exports = makeTree;
