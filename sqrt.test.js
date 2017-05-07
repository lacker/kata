const sqrt = require('./sqrt');

function testSqrtOf(x) {
  let s = sqrt(x);
  expect(Math.abs(s * s - x)).toBeLessThan(0.001);
}

test('sqrting things', () => {
  testSqrtOf(1);
  testSqrtOf(0);
  testSqrtOf(30000);
});
