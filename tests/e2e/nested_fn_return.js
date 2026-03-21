// Test: nested function calls with returns (ECMA-262 §14.1)
function add(a, b) { return a + b; }
function mul(a, b) { return a * b; }
var result = add(mul(3, 4), mul(5, 6));
console.log(result);
// Expected: 42
