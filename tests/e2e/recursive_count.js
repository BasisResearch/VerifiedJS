// Recursive countdown (ECMA-262 §14.1)
function count(n) {
  if (n <= 0) { return 0; }
  return 1 + count(n - 1);
}
console.log(count(5));
