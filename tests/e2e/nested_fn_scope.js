// Nested functions with scope isolation
function outer() {
  var x = 10;
  function inner() {
    var x = 20;
    return x;
  }
  return x + inner();
}
console.log(outer());
