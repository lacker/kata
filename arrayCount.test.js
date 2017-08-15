const arrayCount = require('./arrayCount');

test('normal behavior', () => {
  expect(arrayCount([1, 4, 7, 7, 7, 8, 9], 7)).toBe(3);
});

test('nonexistent', () => {
  expect(arrayCount([3, 4, 5, 6, 8, 9, 10], 7)).toBe(0);
});
