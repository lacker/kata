// Does allow trailing zeros
function isValidPostDecimalPoint(str, i) {
  while (i < str.length) {
    if ('0123456789'.indexOf(str[i]) < 0) {
      return false;
    }
    i++;
  }
  return true;
}

// Allows leading zeros
function isValidPositiveNumber(str, i) {
  if (str === '.') {
    return false;
  }
  if (str === '') {
    return false;
  }
  while (i < str.length) {
    if (str[i] === '.') {
      return isValidPostDecimalPoint(str, i + 1);
    }
    if ('0123456789'.indexOf(str[i]) < 0) {
      return false;
    }
  }
  return true;
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

// TODO: test
module.exports = isValidNumber;
