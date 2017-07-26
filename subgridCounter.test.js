const SubgridCounter = require('./subgridCounter');

test('basic subgrid', () => {
  let data = [
    [1, 0, 1],
    [0, 1, 0],
    [1, 0, 1],
  ];
  let counter = new SubgridCounter(data);
  expect(counter.count(1, 1, 1, 1)).toBe(1);
})
