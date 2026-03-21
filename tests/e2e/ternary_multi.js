// Test: nested ternary operator (ECMA-262 §13.14)
var x = 5;
var result = x > 10 ? "big" : x > 3 ? "medium" : "small";
console.log(result);
// Expected: medium
