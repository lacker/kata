const isValidNumber = require('./isValidNumber');

test('basic', () => {
  expect(isValidNumber('13')).toBe(true);
});

test('bad stuff', () => {
  expect(isValidNumber('a')).toBe(false);
  expect(isValidNumber('.')).toBe(false);
  expect(isValidNumber('-')).toBe(false);
  expect(isValidNumber('1e3')).toBe(false);
});
