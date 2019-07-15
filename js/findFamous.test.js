const findFamous = require('./findFamous');

function fiveIsFamous(i, j) {
  if (i === 5) {
    return false;
  }
  if (j === 5) {
    return true;
  }
  return (i % 3) === (j % 3) ? true : false;
}

test('finding five', () => {
  expect(findFamous(fiveIsFamous, 1000)).toBe(5);
});

test('when there is no five', () => {
  expect(findFamous(fiveIsFamous, 3)).toBe(-1);
});
