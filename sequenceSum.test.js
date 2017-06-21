const sequenceSum = require('./sequenceSum');

test('a sum that exists', () => {
  expect(sequenceSum([1, 2, 3, 4, 5, 6], 9)).toBe(true);
});

test('a sum that does not exist', () => {
  expect(sequenceSum([2, 4, 6, 8, 10, 12, 14, 16, 18, 20], 21)).toBe(false);
});
