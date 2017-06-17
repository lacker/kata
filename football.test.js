const football = require('./football');

test('basic operation', () => {
  expect(football(6)).toBe(2);

  // 6 ways to get it from 7 3 2
  // All 3's
  // All 2's
  // 3 3 2 2 2 leads to 5 choose 2 = 10
  expect(football(12)).toBe(18);
});
