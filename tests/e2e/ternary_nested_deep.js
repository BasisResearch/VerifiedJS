// Test deeply nested ternary
let x = 5;
let r = x > 10 ? "big" : x > 3 ? "medium" : x > 0 ? "small" : "zero";
console.log(r);
// expected: medium
