let combineDigits = require('./combineDigits');

test('combining digits runs', () => {
  expect(combineDigits()).toBeGreaterThan(0);
});
