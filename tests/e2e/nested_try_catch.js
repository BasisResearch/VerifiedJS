// Try/catch normal completion (ECMA-262 §13.15)
var x = 10;
try {
  x = x + 5;
} catch (e) {
  x = 0;
}
console.log(x);
console.log(x + 1);
