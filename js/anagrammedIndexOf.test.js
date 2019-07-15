let aio = require('./anagrammedIndexOf');

test('basic example', () => {
  expect(aio('actor', 'cat')).toBe(0);
  expect(aio('actor', 'rot')).toBe(2);
  expect(aio('actor', 'cot')).toBe(1);
  expect(aio('actor', 'foo')).toBe(-1);
});
