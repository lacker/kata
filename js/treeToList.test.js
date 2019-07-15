let treeToList = require('./treeToList');

// Checks that list is a doubly-linked-list with the given items.
function checkList(list, items) {
  let node = list;
  while (node.left !== null) {
    node = node.left;
  }

  let prev = null;
  for (let item of items) {
    expect(node.left).toBe(prev);
    expect(node.value).toBe(item);
    prev = node;
    node = node.right;
  }
  expect(node).toBe(null);
}

function makeTree() {
  return {
    value: 'D',
    left: {
      value: 'B',
      left: {
        value: 'A',
      },
      right: {
        value: 'C',
      },
    },
    right: {
      value: 'F',
      left: {
        value: 'E',
      },
      right: {
        value: 'G',
      },
    },
  };
}

test('tree to list', () => {
  let tree = makeTree();
  treeToList(tree);
  checkList(tree, ['A', 'B', 'C', 'D', 'E', 'F', 'G']);
});
