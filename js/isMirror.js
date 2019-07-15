function isMirror(a, b) {
  if (!a && !b) {
    return true;
  }
  if (!a || !b) {
    return false;
  }
  if (a.value !== b.value) {
    return false;
  }
  return isMirror(a.left, b.right) && isMirror(a.right, b.left);
}

module.exports = isMirror;
