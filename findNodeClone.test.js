const findNodeClone = require('./findNodeClone');

test('normal behavior', () => {
  let tree = {
    value: 'A',
    left: {
      value: 'B',
    },
    right: {
      value: 'C',
    }
  };
  addParentLinks(tree, null);
  expect(tree.left.parent.value).toBe('A');
});
