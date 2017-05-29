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
