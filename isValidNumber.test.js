const isValidNumber = require('./isValidNumber');

function numberize(x) {
  if (isValidNumber(x)) {
    return x;
  } else {
    return 'nan';
  }
}

function expectInvalid(x) {
  expect(numberize(x)).toBe('nan');
}

test('basic', () => {
  expect(isValidNumber('13')).toBe(true);
});

test('bad stuff', () => {
  expectInvalid('a');
  expectInvalid('.');
  expectInvalid('-');
  expectInvalid('1e3');
  expectInvalid('-.');
});

test('decimals', () => {
  expect(isValidNumber('0.123')).toBe(true);
  expect(isValidNumber('-0.89898')).toBe(true);
  expect(isValidNumber('.456')).toBe(true);
  expect(isValidNumber('-.777')).toBe(true);
});
