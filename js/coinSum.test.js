const coinSum = require('./coinSum');

test('regular american coins', () => {
  expect(coinSum([1, 5, 10, 25], 13)).toBe(4);
});
