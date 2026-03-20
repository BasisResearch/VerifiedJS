// E2E: nested if/else (ECMA-262 §13.6)
// expected: positive
// expected: zero
// expected: negative

function classify(n) {
  if (n > 0) {
    return "positive";
  } else if (n === 0) {
    return "zero";
  } else {
    return "negative";
  }
}
console.log(classify(5));
console.log(classify(0));
console.log(classify(-3));
