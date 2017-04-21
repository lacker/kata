let almostPalindrome = require('./almostPalindrome');

test('exact', () => {
  expect(almostPalindrome('arfbarfrabfra')).toBe(true);
  expect(almostPalindrome('10011001')).toBe(true);
});

test('off by one', () => {
  expect(almostPalindrome('arfbarfrabbfra')).toBe(true);
  expect(almostPalindrome('100211001')).toBe(true);
});

test('way off', () => {
  expect(almostPalindrome('arfbarfarfbarf')).toBe(false);
  expect(almostPalindrome('10010110')).toBe(false);
});
