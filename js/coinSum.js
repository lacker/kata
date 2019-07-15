// This class can be used for a single op, because it memoizes.
class CoinSummer {
  constructor(coins) {
    // The keys are comma-separated answers to count:
    // numCoins,target
    this.memo = new Map();

    this.coins = coins;
  }

  // How many combinations of the first numCoins coin types sum to the
  // target value.
  count(numCoins, target) {
    if (numCoins === 0) {
      return target === 0 ? 1 : 0;
    }

    let key = numCoins + ',' + target;
    if (this.memo.has(key)) {
      return this.memo.get(key);
    }

    let lastCoin = this.coins[numCoins - 1];

    // One possibility is to not use lastCoin at all
    let answer = this.count(numCoins - 1, target);

    // Another possibility is to use lastCoin at least once
    if (lastCoin <= target) {
      answer += this.count(numCoins, target - lastCoin);
    }

    this.memo.set(key, answer);
    return answer;
  }
}

// Given a sorted list of denominations of coins and a target value,
// determine how many combinations of the coin types sum to the target
// value.
function coinSum(coins, target) {
  let summer = new CoinSummer(coins);
  return summer.count(coins.length, target);
}

module.exports = coinSum;
