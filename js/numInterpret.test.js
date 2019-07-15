const numInterpret = require('./numInterpret');

test('basic functionality', () => {
  expect(numInterpret('1')).toBe(1);
  expect(numInterpret('11')).toBe(2);
  expect(numInterpret('111')).toBe(3);
  expect(numInterpret('1111')).toBe(5);
});

test('stuff that should not work', () => {
  expect(numInterpret('a')).toBe(0);
  expect(numInterpret('0123123123')).toBe(0);
  expect(numInterpret('11113031111')).toBe(0);
});

test('single pathers', () => {
  expect(numInterpret('99999999')).toBe(1);
  expect(numInterpret('39465738946578349657843')).toBe(1);
});
