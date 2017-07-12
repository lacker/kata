
// Given a list of pairs (dominos) of integers, and an integer K,
// find 2 dominos that their left values sum to K and their right values
// sum to K.

function getKey(left, right) {
  return left + ',' + right;
}

function getPairKey(k, left, right) {
  let pairLeft = k - left;
  let pairRight = k - right;
  return getKey(pairLeft, pairRight);
}
