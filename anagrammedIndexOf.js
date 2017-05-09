/*
anagrammed indexOf
("actor, "cat") = 0 // 'act' is an anagram of 'cat'

Note: this is only intended to work on [a-z]
*/

let charmap = new Map();

for (let char of 'abcdefghijklmnopqrstuvwxyz') {
  // 32 bits
  let n = Math.floor(Math.random() * 4294967296);
  charmap.set(char, n);
}

// Could fail but should work. TODO: test
function anagrammedIndexOf(bigWord, littleWord) {
  let len = littleWord.length;
  let hash = 0;
  for (let i = 0; i < bigWord.length; i++) {
    // See if bigWord[i - len + 1] .. bigWord[i] makes the word
    let newChar = bigWord[i];
    if (!charmap.has(newChar)) {
      throw new Error('weird char: ' + newChar);
    }
    hash = hash ^ charmap.get(newChar);
    let drop = i - len;
    if (drop >= 0) {
      hash = hash ^ charmap.get(bigword[drop]);
    }
    if (drop >= -1 && hash === 0) {
      return drop + 1;
    }
  }
  return -1;
}
