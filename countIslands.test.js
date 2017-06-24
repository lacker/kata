const countIslands = require('./countIslands');

test('two islands', () => {
  let matrix = [
    [0, 0, 1],
    [1, 0, 1],
    [1, 0, 0],
  ];
  expect(countIslands(matrix)).toBe(2);

  // TODO: Make sure it works twice
});
