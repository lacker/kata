let evaluate = require('./arithmetic');

test('basic formula', () => {
  let answer = evaluate('12*12+7*8');
  expect(answer).toBe(200);
});
