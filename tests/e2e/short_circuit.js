// E2E: short-circuit evaluation (ECMA-262 §13.12)
// expected: 0
// expected: 5
// expected: 3
// expected: 0

console.log(false && 5);
console.log(true && 5);
console.log(3 || 0);
console.log(0 || false || 0);
