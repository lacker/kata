const depthSum = require('./depthSum');

test('standard problem', () => {
  let input = [8, 4, [5, 3, [9]], 6];
  expect(depthSum(input)).toBe(61);
});
