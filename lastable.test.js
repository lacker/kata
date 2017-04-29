let Lastable = require('./lastable');

test('pop it all', () => {
  let data = new Lastable();
  data.put('a', 1);
  data.put('b', 2);
  data.put('c', 3);
  data.put('d', 4);
  data.get('a');
  data.get('c');
  data.get('a');
  expect(data.last()).toBe('a');
  data.del('a');
  expect(data.last()).toBe('c');
  data.del('c');
  expect(data.last()).toBe('d');
});

test('puts on deleted keys', () => {
  let data = new Lastable();
  data.put('a', 1);
  data.put('b', 2);
  data.del('a');
  data.put('a', 3);
  data.put('c', 4);
  expect(data.last()).toBe('c');
  data.del('c');
  expect(data.last()).toBe('a');
  data.del('a');
  expect(data.last()).toBe('b');
});
