let threeSum = require('./threeSum');

test('sums', () => {
  expect(threeSum([1, 2, 3, 4, 5, 6, 7])).toBe(false);
  expect(threeSum([1, 2, 3, -12, 4, 5, 6, 7])).toBe(true);
  expect(threeSum([-9, -7, -5, -3, -1, 1, 3, 5, 7, 9])).toBe(false);
  expect(threeSum([-3, -2, -1, 1, 2, 3])).toBe(true);
});
