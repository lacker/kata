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
});

test('modifying the grid', () => {
  let data = [[1]];
  let counter1 = new SubgridCounter(data);
  expect(counter1.count(0, 0, 0, 0)).toBe(1);
  data[0][0] = 2;
  let counter2 = new SubgridCounter(data);
  expect(counter2.count(0, 0, 0, 0)).toBe(2);
  expect(counter1.count(0, 0, 0, 0)).toBe(1);  
});
