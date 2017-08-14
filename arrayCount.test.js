const arrayCount = require('./arrayCount');

test('normal behavior', () => {
  expect(arrayCount([1, 4, 7, 7, 7, 8, 9], 7)).toBe(3);
});
