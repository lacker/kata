const topWords = require('./topWords');

test('basic usage', () => {
  let doc = 'a b c d e f g a b c a b a';
  let top = topWords(doc, 3);
  expect(top).toEqual([
    ['a', 4],
    ['b', 3],
    ['c', 2],
  ]);
});

test('with punctuation', () => {
  let doc = 'Bonk, and bonk.';
  let top = topWords(doc, 3);
  expect(top).toEqual([
    ['bonk', 2],
    ['and', 1],
  ]);
});
