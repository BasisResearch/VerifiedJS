// Test nested ternary (conditional) expressions
function classify(x) {
  return x > 0 ? "positive" : x < 0 ? "negative" : "zero";
}
console.log(classify(5));
console.log(classify(-3));
console.log(classify(0));
// Expected:
// positive
// negative
// zero
