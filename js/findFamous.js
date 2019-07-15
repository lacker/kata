// Given a list of persons, find out the "famous person" in the list.
// A person is a "famous person" iff all others knows him/her AND he/she
// doesn't know anybody else.
// Take a function bool know(i, j) which return true if
// i knows j, or false if i does not know j.
// The people are numbered 0 to n-1.
// Return -1 if there is no famous person.
function findFamous(know, n) {
  if (n <= 0) {
    return -1;
  }
  // Run a tournament to figure out who wins.
  // Loop invariant: winner is the only person who could be famous.
  let winner = 0;
  for (let challenger = 1; challenger < n; challenger++) {
    if (know(winner, challenger)) {
      // winner cannot be famous. challenger could be.
      winner = challenger;
    } else {
      // winner could be famous. challenger could not be.
    }
  }

  // Now check if winner actually is famous.
  for (let other = 0; other < n; other++) {
    if (other === winner) {
      continue;
    }
    if (know(winner, other) || !know(other, winner)) {
      // winner is not famous, so nobody can be
      return -1;
    }
  }
  return winner;
}

module.exports = findFamous;
