// E2E: logical operators and short-circuit evaluation (ECMA-262 §12.13)
// expected: 5
// expected: 0
// expected: 3
// expected: 10

console.log(0 || 5);
console.log(0 && 5);
console.log(3 || 5);
console.log(10 && 20 && 10);
