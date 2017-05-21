// Returns the next level in a binary tree given the current level
function nextLevel(level) {
  let answer = [];
  for (let node of level) {
    if (node.left) {
      answer.push(node.left);
    }
    if (node.right) {
      answer.push(node.right);
    }
  }
  return answer;
}

// Checks if the two trees have the same contents at each level.
function levelMatch(tree1, tree2) {
  let level1 = [tree1];
  let level2 = [tree2];
  while (level1.length !== 0 && level2.length !== 0) {
    if (level1.length !== level2.length) {
      return false;
    }
    for (let i = 0; i < level1.length; i++) {
      if (level1[i].value !== level2[i].value) {
        return false;
      }
    }
  }
  return true;
}

// TODO: test
module.exports = levelMatch;
