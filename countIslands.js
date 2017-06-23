// Replaces [i][j] from 1 -> 0 and recurses locally
// Returns whether there was a replace
function flood(matrix, i, j) {
  if (i < 0 || i >= matrix.length || j < 0 || j >= matrix[i].length) {
    return false;
  }
  if (matrix[i][j] === 0) {
    return false;
  }
  matrix[i][j] = 0;
  flood(matrix, i - 1, j);
  flood(matrix, i + 1, j);
  flood(matrix, i, j - 1);
  flood(matrix, i, j + 1);
  return true;
}

function countIslands(matrix) {
  let copy = JSON.parse(JSON.stringify(matrix));
  let answer = 0;
  for (let i = 0; i < copy.length; i++) {
    for (let j = 0; j < copy[i].length; j++) {
      if (flood(matrix, i, j)) {
        answer++;
      }
    }
  }
  return answer;
}

// TODO: more
