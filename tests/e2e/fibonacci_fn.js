// Fibonacci via iterative function
function fib(n) {
  var a = 0;
  var b = 1;
  for (var i = 0; i < n; i = i + 1) {
    var tmp = b;
    b = a + b;
    a = tmp;
  }
  return a;
}
console.log(fib(10));
