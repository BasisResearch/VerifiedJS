// Iterative Fibonacci (ECMA-262 §13.7.4)
function fib(n) {
  var a = 0;
  var b = 1;
  var i = 0;
  while (i < n) {
    var temp = b;
    b = a + b;
    a = temp;
    i = i + 1;
  }
  return a;
}
console.log(fib(0));
console.log(fib(1));
console.log(fib(10));
