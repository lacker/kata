// Evaluates an arithmetic expression.
// Only handles + and *
function evaluate(expression) {
  let parts = expression.split(/[+]/);
  let answer = 0;
  for (let part of parts) {
    let subparts = part.split(/[*]/);
    let subanswer = 1;
    for (let subpart of subparts) {
      subanswer *= subpart;
    }
    answer += subanswer;
  }
  return answer;
}


module.exports = evaluate;
