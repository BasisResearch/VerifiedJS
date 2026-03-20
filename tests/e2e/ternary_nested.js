// E2E: nested ternary/conditional expressions (ECMA-262 §13.13)
// expected: zero
// expected: positive
// expected: negative

function classify(n) {
  return n === 0 ? "zero" : n > 0 ? "positive" : "negative";
}
console.log(classify(0));
console.log(classify(5));
console.log(classify(-3));
