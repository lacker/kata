const mirrorTree = require('./mirrorTree');
const isMirror = require('./isMirror');

test('trees', () => {
  let tree = {
    value: 1,
    left: {
      value: 2,
      left: {
        value: 3,
      },
      right: {
        value: 'A',
      },
    },
    right: {
      value: 'B',
    },
  };

  let m = mirrorTree(tree);

  expect(isMirror(tree, m)).toBe(true);
  expect(isMirror(m, tree)).toBe(true);

  tree.left.right.value = 'X';
  expect(isMirror(tree, m)).toBe(false);
  expect(isMirror(m, tree)).toBe(false);
});
