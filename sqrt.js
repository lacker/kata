function sqrt(x) {
  let epsilon = 0.0000001;
  if (x < 0) {
    throw new Error('cant do sqrt of ' + x);
  }
  let a = 0;
  let b = 1;
  while (Math.abs(a - b) > epsilon) {
    a = b;
    b = (b + x/b) / 2;
  }
  return b;
}

module.exports = sqrt;
