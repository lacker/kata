const balanceParens = require('./balanceParens');

test('already balanced', () => {
  let x = 'arf(bar(zz()(a(v(f)g)h))h)(hh())'
  expect(balanceParens(x)).toBe(x);
});

test('complex example', () => {
  expect(balanceParens(')((())')).toBe('(())');
});
