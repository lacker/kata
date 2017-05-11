let DLL = require('./dll');

test('basic DLL ops', () => {
  let node = new DLL(1);
  expect(node.prev).toBe(null);
  expect(node.next).toBe(null);
});
