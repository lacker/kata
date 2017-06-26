const countIslands = require('./countIslands');

test('two islands', () => {
  let matrix = [
    [0, 0, 1],
    [1, 0, 1],
    [1, 0, 0],
  ];
  expect(countIslands(matrix)).toBe(2);

  // Make sure it works twice
  expect(countIslands(matrix)).toBe(2);
});
