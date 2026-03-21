// Check if numbers are even
function isEven(n) {
  if (n < 0) { n = -n; }
  var x = n;
  while (x >= 2) { x = x - 2; }
  return x === 0;
}
console.log(isEven(4));
console.log(isEven(7));
console.log(isEven(0));
