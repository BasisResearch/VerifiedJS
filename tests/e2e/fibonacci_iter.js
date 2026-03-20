// E2E: iterative fibonacci (ECMA-262 §13.7)
// expected: 55

function fib(n) {
  let a = 0;
  let b = 1;
  let i = 0;
  while (i < n) {
    let temp = b;
    b = a + b;
    a = temp;
    i = i + 1;
  }
  return a;
}
console.log(fib(10));
