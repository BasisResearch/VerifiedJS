// E2E: variable scoping with reassignment (ECMA-262 §13.3.1)
// expected: 10
// expected: 20

var x = 10;
console.log(x);
x = 20;
console.log(x);
