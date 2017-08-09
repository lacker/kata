const numInterpret = require('./numInterpret');

test('basic functionality', () => {
  expect(numInterpret('1')).toBe(1);
  expect(numInterpret('11')).toBe(2);
  expect(numInterpret('111')).toBe(3);
  expect(numInterpret('1111')).toBe(5);
});
