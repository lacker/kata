const findDominos = require('./findDominos');

test('there is a match', () => {
  let data = [[1, 9], [2, 2], [3, 3], [7, 2], [9, 1], [-5, 15]];
  expect(findDominos(data, 10)).toEqual([[1, 9], [9, 1]]);
});
