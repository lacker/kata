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

// Does not allow leading zeros
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
