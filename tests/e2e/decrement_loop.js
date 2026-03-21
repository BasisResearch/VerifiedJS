// Decrement loop (ECMA-262 §13.7.4)
var n = 10;
var result = 1;
while (n > 1) {
  result = result * n;
  n = n - 1;
}
console.log(result);
