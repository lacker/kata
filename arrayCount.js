
// Find the index of k in the array. array is sorted array of ints.
// Only return it if it is in [i, j]
// Return -1 if it isn't there
function indexOf(array, i, j, k) {
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
    return indexOf(array, i, mid, k);
  } else {
    return indexOf(array, mid, j, k);
  }
}

// In a sorted array of integers, count how many times a particular one appears.
function arrayCount(array, k) {
  // TODO
}
