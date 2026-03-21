// Test multiple closures sharing state
function counter() {
  let count = 0;
  function inc() {
    count = count + 1;
    return count;
  }
  return inc;
}
let c = counter();
console.log(c());
console.log(c());
console.log(c());
// expected: 1
// expected: 2
// expected: 3
