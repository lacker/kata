// Checks if this string is a palindrome from index i to j, inclusive.
function isPalindrome(s, i, j) {
  if (j <= i) {
    return true;
  }
  if (s[i] !== s[j]) {
    return false;
  }
  return isPalindrome(s, i + 1, j - 1);
}

// Checks if you can make the string s from i to j, inclusive, into a
// palindrome by removing at most one character.
function almostPalindromeHelper(s, i, j) {
  if (j <= i) {
    return true;
  }
  if (s[i] === s[j]) {
    return almostPalindromeHelper(s, i + 1, j - 1);
  }

  // If s[i] and s[j] are different, either s[i] has to be removed, or
  // s[j] has to be removed.
  return isPalindrome(s, i + 1, j) || isPalindrome(s, i, j - 1);
}

function almostPalindrome(s) {
  return almostPalindromeHelper(s, 0, s.length - 1);
}

module.exports = almostPalindrome;

