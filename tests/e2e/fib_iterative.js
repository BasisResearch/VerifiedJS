// Test: iterative fibonacci (ECMA-262 §13.7.3)
function fib(n) {
  var a = 0;
  var b = 1;
  var i = 0;
  while (i < n) {
    var temp = a + b;
    a = b;
    b = temp;
    i = i + 1;
  }
  return a;
}
console.log(fib(10));
// Expected: 55
