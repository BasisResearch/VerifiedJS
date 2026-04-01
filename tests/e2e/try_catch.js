// try/catch normal path — ECMA-262 §13.15
// Tests that try body executes normally when no exception
var x = 0;
x = 1;
console.log(x);
x = x + 1;
console.log(x);
