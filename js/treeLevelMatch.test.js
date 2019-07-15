const levelMatch = require('./treeLevelMatch');

test('equal trees', () => {
  let one = {
    value: 'A',
    left: {
      value: 'B',
      left: {
        value: 'C',
      },
      right: {
        value: 'D',
      }
    }
  };

  let two = {
    value: 'A',
    right: {
      value: 'B',
      left: {
        value: 'C',
      },
      right: {
        value: 'D',
      }
    }
  };

  expect(levelMatch(one, two)).toBe(true);
});
