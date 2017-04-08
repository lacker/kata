// Returns a list of all the ways of combining + and - with the given string
function allWays(str) {
  if (str.length <= 0) {
    return [''];
  }
  let subanswer = allWays(str.slice(1));
  let answer = [];
  for (let way of subanswer) {
    answer.push(str[0] + way);
    answer.push('-' + str[0] + way);
    answer.push('+' + str[0] + way);
  }
  return answer;
}

// Returns the number of ways of combining + and - with 123456789 that
// evals to 100
// Can't put a plus before the first one
function combineDigits() {
  let answer = 0;
  let ways = allWays('123456789');
  for (let way of ways) {
    if (way[0] === '+') {
      continue;
    }
    if (eval(way) === 100) {
      answer += 1;
    }
  }
  return answer;
}

module.exports = combineDigits;
