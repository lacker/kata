// Given an array of that contains both integers and nested arrays,
// calculate and return the depth sum.
// For example:
// Input: [8, 4, [5, 3, [9]], 6]
// Output: 8+4+2*(5+3+3*(9)))+6 ==> 88

// Returns the depth sum, where 'depth' is the deepness we already are at.
function helper(array, depth) {
  let answer = 0;
  for (let item of array) {
    if (Array.isArray(item)) {
      answer += helper(item, depth + 1);
    } else {
      answer += depth * item;
    }
  }
  return answer;
}

function depthSum(array) {
  return helper(array, 1);
}

module.exports = depthSum;
