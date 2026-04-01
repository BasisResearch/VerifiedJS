// If-else chain (ECMA-262 §13.6)
function classify(n) {
  if (n < 0) { return -1; }
  else if (n === 0) { return 0; }
  else { return 1; }
}
console.log(classify(-5));
console.log(classify(0));
console.log(classify(7));
