let DLL = require('./dll');

test('basic DLL ops', () => {
  let node = new DLL(1);
  expect(node.prev).toBe(null);
  expect(node.next).toBe(null);
});

test('remove', () => {
  let head = new DLL('A');
  head.append('B').append('C').append('D');
  expect(head.join(',')).toBe('A,B,C,D');
  head.next.remove();
  expect(head.join(',')).toBe('A,C,D');
});
