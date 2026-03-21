// E2E: nested ternary expressions (ECMA-262 §12.13)
// expected: medium

var x = 5;
var label = x < 3 ? "small" : x < 7 ? "medium" : "large";
console.log(label);
