// Recursive summation (ECMA-262 §14.1)
function sumTo(n) {
  if (n <= 0) { return 0; }
  return n + sumTo(n - 1);
}
console.log(sumTo(5));
console.log(sumTo(10));
