// We have a coding system from letters to numbers where a=1, b=2, ...z=26.
// numInterpret takes a string of digits as an input and computes
// the number of valid interpretations of the input.
function numInterpret(s) {
  let cache = new Map();
  // Helper uses the cache and returns the number of interpretations
  // for the string containing indices 0..i
  // So when i = -1 it's the empty string
  let helper = (i) => {
    if (i === -1) {
      return 1;
    }
    if (i < -1) {
      throw new Error('i should not be ' + i);
    }
    if (cache.has(i)) {
      return cache.get(i);
    }

    let answer = 0;
    // Check if s[i] is itself a legit interpretation
    if ('123456789'.indexOf(s[i]) >= 0) {
      answer += helper(i - 1);
    }

    // Check if s[i-1] s[i] makes a two-digit interpretation
    // The '.0' avoids things that already have a decimal point
    let num = Number(s[i - 1] + s[i] + '.0');
    if (num >= 10 && num <= 26) {
      answer += helper(i - 2);
    }

    cache.set(i, answer);
    return answer;
  };

  return helper(s.length - 1);
}

module.exports = numInterpret;
