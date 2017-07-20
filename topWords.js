// Take input from a document and present the top N most frequent words and
// their counts within the document.
// doc is just a string of text.
// Returns a length-n list of [word, count] pairs.
function topWords(doc, n) {
  // Could use more punctuation
  let words = doc.toLowerCase().split(/[ \.,]+/);
  let counts = {};
  for (let word of words) {
    counts[word] = (counts[word] || 0) + 1;
  }
  let pairs = [];
  for (let word in counts) {
    pairs.push([word, counts[word]]);
  }
  pairs.sort(comparePair);
  return pairs.slice(0, n);
}

function comparePair(pair1, pair2) {
  let [word1, count1] = pair1;
  let [word2, count2] = pair2;
  return count1 - count2;
}

module.exports = topWords;
