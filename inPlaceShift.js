// Right circular k-shift, in place, starting at i.
// So this shifts i, i + k, ... ending at i.
// Returns how many items got shifted.
function helper(array, k, i) {
  let count = 0;
  let index = i;
  let carry = array[index];
  while (true) {
    index = (index + k) % array.length;
    let temp = array[to];
    array[to] = carry;
    carry = temp;
    count++;
    if (index === i) {
      break;
    }
  }
  return count;
}

// Right circular k-shift everything in the array
function inPlaceShift(array, k) {
  let todo = array.length;
  for (let i = 0; todo > 0; i++) {
    todo -= helper(array, k, i);
  }
}

module.exports = inPlaceShift;
