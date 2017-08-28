const isValidNumber = require('./isValidNumber');

test('basic', () => {
  expect(isValidNumber('13')).toBe(true);
});
