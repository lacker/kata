// Reverse a linked list.
// A linked list is an object with two fields:
//   value
//   next
// Next is null at the end of the list.
// This does not mutate the argument
function reverse(linkedList) {
  let answer = null;
  while (linkedList !== null) {
    answer = {
      value: linkedList.value,
      next: answer,
    };
    linkedList = linkedList.next;
  }
  return answer;
}

// TODO: test
