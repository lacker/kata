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

test('grandparent', () => {
  let tree = {
    left: {
      mark: true,
      right: {
        right: {
          mark: true,
        }
      }
    },
    right: {
      left: {
        left: {},
        right: {},
      },
      right: {
        left: {},
        right: {},
      }
    }
  };
  expect(treeMarkDistance(tree)).toBe(2);
})
