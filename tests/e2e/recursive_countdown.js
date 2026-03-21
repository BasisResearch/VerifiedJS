// Test recursive countdown
function countdown(n) {
  if (n <= 0) {
    return 0;
  }
  return n + countdown(n - 1);
}
console.log(countdown(5));
// expected: 15
