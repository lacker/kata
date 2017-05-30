const Sampler = require('./sampler');

// Returns a function that just returns each of these values in sequence.
// If it gets called more, raise an error.
function fakeRandom(values) {
  let i = 0;
  let answer = () => {
    if (i >= values.length) {
      throw new Error('reached the end of the list');
    }
    let x = values[i];
    i++;
    return s;
  }
}

test('five things', () => {
  let s = new Sampler();
  s.add('A', 10);
  s.add('B', 10);
  s.add('C', 10);
  s.add('D', 10);
  s.add('E', 10);
  let samples = [
    s.sample(0.1),
    s.sample(0.3),
    s.sample(0.5),
    s.sample(0.7),
    s.sample(0.9),
  ];
  s.sort();
  expect(s.join('')).toBe('ABCDE');
});
