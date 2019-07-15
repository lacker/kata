let TreeIterator = require('./treeIterator');

test('normal tree', () => {
  let tree = {
    left: {
      left: { value: 'A' },
      value: 'B',
      right: { value: 'C' },
    },
    value: 'D',
    right: {
      left: { value: 'E' },
      value: 'F',
      right: { value: 'G' },
    },
  };
  let iter = new TreeIterator(tree);
  expect(iter.nextValue()).toBe('A');
  expect(iter.nextValue()).toBe('B');
  expect(iter.nextValue()).toBe('C');
  expect(iter.nextValue()).toBe('D');
  expect(iter.nextValue()).toBe('E');
  expect(iter.nextValue()).toBe('F');
  expect(iter.nextValue()).toBe('G');
  expect(() => iter.nextValue()).toThrow();
});
