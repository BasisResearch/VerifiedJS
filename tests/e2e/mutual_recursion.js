// Recursive function (ECMA-262 §14.1)
function countdown(n) {
  if (n <= 0) return 0;
  return countdown(n - 1) + 1;
}
console.log(countdown(5));
console.log(countdown(3));
console.log(countdown(0));
