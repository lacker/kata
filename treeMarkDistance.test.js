const treeMarkDistance = require('./treeMarkDistance');

test('cousins', () => {
  let tree = {
    left: {
      right: {
        mark: true,
      }
    },
    right: {
      left: {
        mark: true,
      }
    }
  };
  expect(treeMarkDistance(tree)).toBe(4);
});
