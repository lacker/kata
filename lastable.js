const SortedMap = require('collections/sorted-map');

class Lastable {
  constructor() {
    // A lastable stores objects with three things:
    // key: the key
    // value: the value
    // id: each data access gets an id. ids go *down* over time.
    //     this contains the lowest id for any of the accesses of this key
    //     (ie the most recent one)

    // Indexes by key
    this.dataByKey = new Map();

    // Indexes by id
    this.dataById = new SortedMap();

    this.nextId = -1;
  }

  // Returns {key: key, value: value} and removes it
  // Returns null if it's not there
  pop(key) {
    if (!this.dataByKey.has(key)) {
      return null;
    }

    let data = this.dataByKey.get(key);

    // Remove the current thing
    this.dataByKey.delete(data.key);
    this.dataById.delete(data.id);

    return { key: data.key, value: data.value };
  }

  // Should only be used when key isn't there
  addNew(key, value) {
    if (this.dataByKey.has(key)) {
      throw new Error('used addNew wrong');
    }

    this.nextId--;
    let data = { key: key, value: value, id: this.nextId };
    this.dataByKey.set(key, data);
    this.dataById.set(id, data);
  }
  
  put(key, value) {
    this.pop(key);
    this.addNew(key, value);
  }

  get(key) {
    let old = this.pop(key);
    if (!old) {
      throw new Error('nothing there for key: ' + key);
    }
    this.addNew(key, old.value);
    return old.value;
  }

  del(key) {
    this.pop(key);
  }
  
  // Returns a key
  last() {
    return this.dataById.iterator().next().value.key;
  }
}

module.exports = Lastable;
// TODO: test
