// A Sampler lets you add objects with weights.
// You can then call "sample" which returns one of the objects
// at random.
class Sampler {
  constructor() {
    this.numItems = 0;
    this.totalWeight = 0;

    // Used iff we have only one item
    this.item = null;

    // Used recursively if we have more than one item
    this.left = null;
    this.right = null;
  }

  add(item, weight) {
    if (weight <= 0) {
      throw new Error('weight cannot be ' + weight);
    }

    if (this.numItems === 0) {
      this.numItems = 1;
      this.totalWeight = weight;
      this.item = item;
      return;
    }

    if (this.numItems === 1) {
      // Time to split this node into two nodes
      this.left = new Sampler();
      this.right = new Sampler();
      this.left.add(this.item, this.totalWeight);
      this.right.add(item, weight);

      this.numItems = 2;
      this.totalWeight += weight;
      this.item = null;
      return;
    }

    // Recurse
    this.numItems += 1;
    this.totalWeight += weight;
    if (this.left.numItems <= this.right.numItems) {
      this.left.add(item, weight);
    } else {
      this.right.add(item, weight);
    }
  }

  sample() {
    // TODO: implement
  }
}

// TODO: test
module.exports = Sampler;
