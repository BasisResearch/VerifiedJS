// Chained conditional logic (ECMA-262 §13.6)
function classify(n) {
  if (n < 0) { return "negative"; }
  if (n === 0) { return "zero"; }
  if (n < 10) { return "small"; }
  return "large";
}
console.log(classify(-5));
console.log(classify(0));
console.log(classify(7));
console.log(classify(100));
