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
    // TODO
  }
}
