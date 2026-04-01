// E2E: variable assignment (ECMA-262 §13.15)
// expected: 5
// expected: 15
// expected: 30

var x = 5;
console.log(x);
x = x + 10;
console.log(x);
x = x * 2;
console.log(x);
