// switch/case equivalent via if-else — ECMA-262 §13.12
// Testing the desugared form (switch desugars to strict-eq if-chain)
var x = 2;
var result = 0;
if (x === 1) {
  result = 10;
} else if (x === 2) {
  result = 20;
} else if (x === 3) {
  result = 30;
} else {
  result = 99;
}
console.log(result);
