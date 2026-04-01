// E2E: logical OR as default value (ECMA-262 §12.13.3)
// expected: 10
// expected: 42

var x = 0 || 10;
console.log(x);
var y = 42 || 99;
console.log(y);
