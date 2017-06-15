// Returns the number of ways to get n out of 2, 3, and 7.
// Let's say order matters.
let MEMO = new Map();

function football(n) {
  if (MEMO.has(n)) {
    return MEMO.get(n);
  }
  if (n < 2) {
    return 0;
  }
  let answer = football(n - 2) + football(n - 3) + football(n - 7);
  MEMO.set(n, answer);
  return answer;
}

// TODO: test
