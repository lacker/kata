const flatten = require('./flatten');

test('flattening a random thing', () => {
  let input = [[1, 2], [[[[[[3]]]]]], 4, 5, [6, [7, [8, [9]]]]];
  expect(flatten(input)).toEqual([1, 2, 3, 4, 5, 6, 7, 8, 9]);
});
