// E2E: fibonacci — tests recursion, function calls, conditionals
// expected: 0
// expected: 1
// expected: 1
// expected: 2
// expected: 3
// expected: 5
// expected: 8

function fib(n) {
  if (n <= 1) return n;
  return fib(n - 1) + fib(n - 2);
}

var i = 0;
while (i < 7) {
  console.log(fib(i));
  i = i + 1;
}
