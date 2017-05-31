const Sampler = require('./sampler');

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
  samples.sort();
  expect(samples.join('')).toBe('ABCDE');
});
