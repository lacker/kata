const inPlaceShift = require('./inPlaceShift');

test('relatively prime', () => {
  let arr = [1, 2, 3, 4, 5, 6, 7];
  inPlaceShift(arr, 3);
  expect(arr).toEqual([5, 6, 7, 1, 2, 3, 4]);
});

test('both even', () => {
  let arr = [1, 2, 3, 4, 5, 6];
  inPlaceShift(arr, 2);
  expect(arr).toEqual([5, 6, 1, 2, 3, 4]);
});

test('zero', () => {
  let arr = [1, 2, 3];
  inPlaceShift(arr, 0);
  expect(arr).toEqual([1, 2, 3]);
});
