
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

function findDominos(list, k) {
  let dominos = new Map();
  for (let domino of list) {
    let [left, right] = domino;
    let key = getKey(left, right);
    let pairKey = getPairKey(k, left, right);
    if (dominos.has(pairKey)) {
      return [dominos.get(pairKey), domino];
    }
    dominos.set(key, domino);
  }
  return -1;
}

module.exports = findDominos;
