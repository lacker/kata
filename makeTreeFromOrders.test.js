const inorder = require('./inorder');
const preorder = require('./preorder');
const makeTree = require('./makeTreeFromOrders');
const treeEqual = require('./treeEqual');

let tree = {
  value: 'A',
  left: {
    value: 'B',
    left: { value: 'C' },
    right: { value: 'D' },
  },
  right: {
    value: 'E',
    left: { value: 'F' },
    right: { value: 'G' },
  },
};

function testTree(tree) {
  let inorderList = inorder(tree);
  let preorderList = preorder(tree);
  let tree2 = makeTree(inorderList, preorderList);
  expect(treeEqual(tree, tree2)).toBe(true);
}

test('making trees', () => {
  testTree(tree);
  testTree(null);
  testTree(tree.left);
  testTree(tree.right);
});
