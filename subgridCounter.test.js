const SubgridCounter = require('./subgridCounter');

test('basic subgrid', () => {
  let data = [
    [1, 0, 1],
    [0, 1, 0],
    [1, 0, 1],
  ];
  let counter = new SubgridCounter(data);
  expect(counter.count(0, 0, 0, 0)).toBe(1);
  expect(counter.count(1, 1, 1, 1)).toBe(1);
  expect(counter.count(0, 1, 2, 2)).toBe(3);
})
