const {
  findNodeClone,
  clone,
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

test('cloning', () => {
  let tree1 = makeTree();
  let tree2 = clone(tree1);
  expect(tree2.left.value).toBe('B');
  expect(tree2.right.parent.value).toBe('A');
});

test('finding the clone', () => {
  let tree1 = makeTree();
  let tree2 = clone(tree1);
  expect(findNodeClone(tree1.left, tree2)).toBe(tree2.left);
});
