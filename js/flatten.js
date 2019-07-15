function flatten(array) {
  let answer = [];
  for (let item of array) {
    if (Array.isArray(item)) {
      for (let subitem of flatten(item)) {
        answer.push(subitem);
      }
    } else {
      answer.push(item);
    }
  }
  return answer;
}

module.exports = flatten;
