let longestPath = require('./treeLongestPath');

let x = {
  value: 'X',
};
let y = {
  value: 'Y',
};

test('sibling', () => {
  let tree = {
    left: x,
    right: y,
  };
  expect(longestPath(tree, x, y)).toBe(2);
});

test('uncle', () => {
  let tree = {
    left: x,
    right: {
      left: {},
      right: y,
    },
  };

  expect(longestPath(tree, x, y)).toBe(3);
});

test('impossible', () => {
  let tree = {
    left: x,
    right: x,
  };
  expect(longestPath(tree, x, y)).toBe(-1);
});
