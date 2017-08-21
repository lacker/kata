const {
  findNodeClone,
  addParentLinks,
} = require('./findNodeClone');

function makeTree() {
  let tree = {
    value: 'A',
    left: {
      value: 'B',
    },
    right: {
      value: 'C',
    }
  };
  addParentLinks(tree);
  return tree;
}

test('tree-making', () => {
  let tree = makeTree();
  expect(tree.left.value).toBe('B');
  expect(tree.left.parent.value).toBe('A');
  expect(tree.right.value).toBe('C');
  expect(tree.right.parent).toBe(tree);
});
