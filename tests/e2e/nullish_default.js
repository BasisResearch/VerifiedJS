// Test: nullish coalescing simulation (ECMA-262 §13.15.3)
var x = null;
var y = x !== null && x !== undefined ? x : "default";
console.log(y);
// Expected: default
