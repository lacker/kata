var CACHE = {};

// Sizes is an array of ints representing the size of minions.
// Returns an array of probabilities that each one will be the last standing.
function volcano(sizes) {
  if (sizes.length == 1) {
    return [1.0];
  }

  if (sizes.length == 0) {
    throw new Error("cannot run volcano on the empty list");
  }

  let key = "" + sizes;
  if (CACHE[key]) {
    return CACHE[key];
  }

  // Recurse if anything is a zero
  for (let i = 0; i < sizes.length; i++) {
    if (sizes[i] == 0) {
      let smaller = sizes.slice(0, i).concat(sizes.slice(i + 1));
      let answer = volcano(smaller);
      return answer
        .slice(0, i)
        .concat([0])
        .concat(answer.slice(i));
    }
  }

  // Sum up each possibility
  let answer = [];
  for (let size of sizes) {
    answer.push(0);
  }
  for (let i = 0; i < sizes.length; i++) {
    let copy = sizes.concat([]);
    copy[i] -= 1;
    let subanswer = volcano(copy);
    for (let j = 0; j < subanswer.length; j++) {
      answer[j] += (1.0 / sizes.length) * subanswer[j];
    }
  }
  CACHE[key] = answer;
  return answer;
}

console.log(volcano([4, 4, 8]));
