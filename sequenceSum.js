// Given a sequence of positive integers seq and an integer total,
// return whether a contiguous sequence of seq sums up to total
function sequenceSum(seq, sum) {
  if (sum === 0) {
    return true;
  }

  // Sums that start at the beginning
  let partials = new Set();
  partials.add(0);
  let accum = 0;
  for (let integer of seq) {
    accum += integer;
    if (partials.has(accum - sum)) {
      return true;
    }
    partials.add(accum);
  }
  return false;
}

// TODO: test
