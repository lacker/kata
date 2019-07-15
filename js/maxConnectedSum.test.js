const maxConnectedSum = require('./maxConnectedSum');

let tree = {
  value: 1,
  left: {
    value: -2,
    left: {
      value: 10,
    },
    right: {
      value: 1,
    },
  },
  right: {
    value: 10,
    left: {
      value: -1,
    },
    right: {
      value: 1,
    },
  },
};

test('max connected sums', () => {
  expect(maxConnectedSum(tree)).toBe(21);
  expect(maxConnectedSum(tree.left)).toBe(10);
  expect(maxConnectedSum(tree.right)).toBe(11);
  expect(maxConnectedSum(tree.right.left)).toBe(0);
});
