let reverse = require('./reverseList');

test('reversing null is null', () => {
  expect(reverse(null)).toBeNull();
});

test('reversing a linked list', () => {
  let list = {
    value: 1,
    next: {
      value: 2,
      next: {
        value: 3,
        next: null,
      },
    },
  };
  let goal = {
    value: 3,
    next: {
      value: 2,
      next: {
        value: 1,
        next: null,
      },
    },
  };
  expect(reverse(list)).toEqual(goal);
});
