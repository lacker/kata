// Pick k items from the list randomly
function choice(list, numToChoose) {
  let total = list.length;
  if (total < numToChoose) {
    throw new Error(
      'cannot choose ' + numToChoose +
      ' from a list of length ' + total);
  }

  let output = [];
  while (output.length < numToChoose) {
    // Consider taking index total - 1
    // There is a numToChoose / total chance of wanting it
    let chance = numToChoose / total;
    if (Math.random() < chance) {
      // Do select it
      output.push(list[total - 1]);
      numToChoose -= 1;
    }
    total -= 1;
  }
  return output;
}

module.exports = choice;
