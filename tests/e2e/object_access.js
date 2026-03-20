// E2E: multi-arg function calls and arithmetic
// expected: 50
// expected: 8
// expected: 0

function compute(a, b) {
  return a * b;
}
console.log(compute(5, 10));
console.log(compute(2, 4));
console.log(compute(0, 100));
