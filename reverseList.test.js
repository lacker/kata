let reverse = require('./reverseList');

test('reversing null is null', () => {
  expect(reverse(null)).toBeNull();
});
