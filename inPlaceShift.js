// Right circular k-shift, in place, starting at i.
// So this shifts i, i + k, ... ending at i.
// Returns how many items got shifted.
function inPlaceShift(array, k, i) {
  let count = 0;
  let from = i;
  let temp = null;
  while (true) {
    let to = (from + k) % array.length;
    // TODO: more
  }
}
