// Returns an object with:
// longestPath = the length of the longest path between node1 and node2
// Otherwise:
// depth1 = the depth of node1, if it's there
// depth2 = the depth of node2, if it's there
function helper(tree, node1, node2) {
  if (node1 === node2) {
    return {
      longestPath: 0,
    };
  }
  if (!tree) {
    return {};
  }
  if (tree === node1) {
    return {
      depth1: 0,
    };
  }
  if (tree === node2) {
    return {
      depth2: 0,
    };
  }

  let leftData = helper(tree.left, node1, node2);
  if (leftData.longestPath != null) {
    return leftData;
  }
  let rightData = helper(tree.right, node1, node2);
  if (rightData.longestPath != null) {
    return rightData;
  }

  let depth1 = (leftData.depth1 == null) ? rightData.depth1 : leftData.depth1;
  let depth2 = (leftData.depth2 == null) ? rightData.depth2 : leftData.depth2;
  let answer = {};
  if (depth1 != null) {
    answer.depth1 = depth1 + 1;
  }
  if (depth2 != null) {
    answer.depth2 = depth2 + 1;
  }
  if (answer.depth1 != null && answer.depth2 != null) {
    return {
      longestPath: answer.depth1 + answer.depth2,
    };
  }
  return answer;
}


function longestPath(tree, node1, node2) {
  let data = helper(tree, node1, node2);
  if (data.longestPath != null) {
    return data.longestPath;
  }
  return -1;
}

module.exports = longestPath;
