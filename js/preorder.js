// Appends the preorder onto output
function preorderHelper(tree, output) {
  if (!tree) {
    return;
  }
  output.push(tree.value);
  preorderHelper(tree.left, output);
  preorderHelper(tree.right, output);
}

function preorder(tree) {
  let answer = [];
  preorderHelper(tree, answer);
  return answer;
}

module.exports = preorder;
