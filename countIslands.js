// Replaces [i][j] from 1 -> 0 and recurses locally
function flood(matrix, i, j) {
  if (i < 0 || i >= matrix.length || j < 0 || j >= matrix[i].length) {
    return;
  }
  if (matrix[i][j] === 0) {
    return;
  }
  matrix[i][j] = 0;
  flood(matrix, i - 1, j);
  flood(matrix, i + 1, j);
  flood(matrix, i, j - 1);
  flood(matrix, i, j + 1);
}

// TODO: more
