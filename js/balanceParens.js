// Returns a string with balanced parentheses while removing
// as few characters as possible from str.
function balanceParens(str) {
  // Counts opens - closed.
  let opens = 0;

  // First pass: Remove extra close-parens
  let firstPass = [];
  for (let char of str) {
    if (char === '(') {
      opens += 1;
      firstPass.push('(');
    } else if (char === ')') {
      if (opens === 0) {
        // We have to remove this character
      } else {
        opens -= 1;
        firstPass.push(')');
      }
    } else {
      firstPass.push(char);
    }
  }

  // Second pass: remove extra open-parens
  let output = [];
  for (let char of firstPass) {
    if (opens > 0 && char === '(') {
      // Remove this one
      opens -= 1;
    } else {
      output.push(char);
    }
  }

  return output.join('');
}

module.exports = balanceParens;
