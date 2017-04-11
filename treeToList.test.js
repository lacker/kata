
// Checks that list is a doubly-linked-list with the given items.
function checkList(list, items) {
  let node = list;
  while (node.left !== null) {
    node = node.left;
  }

  let prev = null;
  for (let item of items) {
    expect(node.left).toBe(prev);
    expect(node.value).toBe(item);
    prev = node;
    node = node.right;
  }
  expect(node).toBe(null);
}
