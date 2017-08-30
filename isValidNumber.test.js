const isValidNumber = require('./isValidNumber');

test('basic', () => {
  expect(isValidNumber('13')).toBe(true);
});

test('bad stuff', () => {
  expect(isValidNumber('a')).toBe(false);
  expect(isValidNumber('.')).toBe(false);
  expect(isValidNumber('-')).toBe(false);
  expect(isValidNumber('1e3')).toBe(false);
  expect(isValidNumber('-.')).toBe(false);
});

test('decimals', () => {
  expect(isValidNumber('0.123')).toBe(true);
  expect(isValidNumber('-0.89898')).toBe(true);
  expect(isValidNumber('.456')).toBe(true);
  expect(isValidNumber('-.777')).toBe(true);
});
