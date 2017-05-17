const SortedMap = require('collections/sorted-map');
const DLL = require('./dll');

class Lastable {
  constructor() {
    // A lastable stores objects with three things:
    // key: the key
    // value: the value
    // id: each data access gets an id. ids go *down* over time.
    //     this contains the lowest id for any of the accesses of this key
    //     (ie the most recent one)

    // Maps key -> { value, node }
    // where node is a list node
    this.data = new Map();

    // A list of all keys, from most recently used to least
    // null if there are none
    this.list = null;
  }

  prependHelper(key) {
    if (this.list) {
      this.list = this.list.prepend(key);
    } else {
      this.list = new DLL(key);
    }
  }

  put(key, value) {
    let blob = this.data.get(key);
    if (blob) {
      blob.node.remove();
    }
    this.prependHelper(key);
    this.data.set(key, { value: value, node: this.list });
  }

  get(key) {
    let blob = this.data.get(key);
    if (!blob) {
      throw new Error('nothing there for key: ' + key);
    }
    blob.node.remove();
    this.prependHelper(key);
    blob.node = this.list;
    return blob.value;
  }

  del(key) {
    let blob = this.data.get(key);
    if (blob) {
      blob.node.remove();
      this.data.remove(key);
    }
  }

  // Returns a key
  last() {
    return this.list.value;
  }
}

module.exports = Lastable;
