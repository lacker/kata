// Appends the inorder onto output
function inorderHelper(tree, output) {
  if (!tree) {
    return;
  }
  inorderHelper(tree.left, output);
  output.push(tree.value);
  inorderHelper(tree.right, output);
}

function inorder(tree) {
  let answer = [];
  inorderHelper(tree, answer);
  return answer;
}

module.exports = inorder;
