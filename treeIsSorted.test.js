let isSorted = require('./treeIsSorted');

test('normal tree', () => {
  let tree = {
    left: {
      left: { value: 'A' },
      value: 'B',
      right: { value: 'C' },
    },
    value: 'D',
    right: {
      left: { value: 'E' },
      value: 'F',
      right: { value: 'G' },
    },
  };
  expect(isSorted(tree)).toBe(true);

  tree.left.right.value = 'Z';
  expect(isSorted(tree)).toBe(false);
});
