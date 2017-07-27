// Given a large rectangular 2D grid of arbitrarily-placed 1's and 0's,
// create a service that answers the query "how many 1's in a given subgrid?".
// Coordinates are "math-style" where x is the first one, y is the second.
class SubgridCounter {
  constructor(grid) {
    this.partial = new Map();
    let maxX = grid.length - 1;
    let maxY = grid[0].length - 1;
    for (let x = 0; x <= maxX; x++) {
      for (let y = 0; y <= maxY; y++) {
        let answer = (
          grid[x][y] +
          this._get(x - 1, y) + this._get(x, y - 1) - this._get(x - 1, y - 1));
        this._set(x, y, answer);
      }
    }
  }

  // Gets the count of the subgrid 0, 0, x, y
  _get(x, y) {
    if (x < 0 || y < 0) {
      return 0;
    }
    let key = x + ',' + y;
    return this.partial.get(key);
  }

  // Sets the count of the subgrid 0, 0, x, y
  _set(x, y, count) {
    let key = x + ',' + y;
    this.partial.set(key, count);
  }

  count(minX, minY, maxX, maxY) {
    return (
      this._get(maxX, maxY) - this._get(minX - 1, maxY)
      - this._get(maxX, minY - 1) + this._get(minX - 1, minY - 1));
  }
}

module.exports = SubgridCounter;
