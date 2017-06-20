const sequenceSum = require('./sequenceSum');

test('a sum that exists', () => {
  expect(sequenceSum([1, 2, 3, 4, 5, 6], 9)).toBe(true);
});
