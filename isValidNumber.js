function isValidPositiveNumber(str, i) {
  // TODO
}

function isValidNumber(str) {
  if (!str || str.length < 1) {
    return false;
  }
  if (str[0] === '-') {
    return isValidPositiveNumber(str, 1);
  } else {
    return isValidPositiveNumber(str, 0);
  }
}

module.exports = isValidNumber;
