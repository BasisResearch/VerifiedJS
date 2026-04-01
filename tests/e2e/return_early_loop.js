// E2E: return from inside conditional (ECMA-262 §13.10)
// expected: 3

function classify(n) {
  if (n > 5) {
    return 1;
  }
  if (n > 2) {
    return 3;
  }
  return 5;
}
console.log(classify(4));
