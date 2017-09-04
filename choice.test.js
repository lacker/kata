const choice = require('./choice');

test('right length', () => {
  expect(choice([1, 2, 3, 4], 0).length).toBe(0);
  expect(choice([1, 2, 3, 4], 1).length).toBe(1);
  expect(choice([1, 2, 3, 4], 2).length).toBe(2);
  expect(choice([1, 2, 3, 4], 3).length).toBe(3);
  expect(choice([1, 2, 3, 4], 4).length).toBe(4);
});
