// Returns whether any three items in this array sum to zero.
function threeSum(array) {
  let twoSums = new Set();
  for (let i = 0; i < array.length; i++) {
    for (let j = i + 1; j < array.length; j++) {
      twoSums.add(array[i] + array[j]);
    }
  }
  for (let x of array) {
    if (twoSums.has(-x)) {
      return true;
    }
  }
  return false;
}

module.exports = threeSum;

// TODO: test
