let lca = require('./lowestCommonAncestor');

let tree = {
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

test('lca', () => {
  let t = lca(tree, 'A', 'C');
  expect(t.value).toBe('B');
});
