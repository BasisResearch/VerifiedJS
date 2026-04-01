// Test: recursive countdown function (ECMA-262 §14.1)
function countdown(n) {
  if (n <= 0) {
    return 0;
  }
  return n + countdown(n - 1);
}
console.log(countdown(10));
// Expected: 55
