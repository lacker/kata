
// Find the index of k in the array. array is sorted array of ints.
// Only return it if it is in [i, j]
// Return -1 if it isn't there
function indexOf(array, i, j, k) {
  if (i > j) {
    return -1;
  }
  if (i === j) {
    if (array[i] === k) {
      return i;
    } else {
      return -1;
    }
  }
  let mid = Math.floor((i + j) / 2);
  let val = array[mid];
  if (val === k) {
    return mid;
  }
  if (val > k) {
    return indexOf(array, i, mid - 1, k );
  } else {
    return indexOf(array, mid + 1, j, k);
  }
}

// In a sorted array of integers, count how many times a particular one appears.
function arrayCount(array, k) {
  let i = indexOf(array, 0, array.length - 1, k);
  if (i === -1) {
    return 0;
  }
  let min = i;
  while (min > 0 && array[min - 1] === k) {
    min -= 1;
  }
  let max = i;
  while (max < array.length - 1 && array[max + 1] === k) {
    max += 1;
  }
  return max - min + 1;
}

module.exports = arrayCount;
