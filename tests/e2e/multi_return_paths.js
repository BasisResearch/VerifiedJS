// Function with multiple return paths
function classify(n) {
  if (n < 0) return -1;
  if (n === 0) return 0;
  return 1;
}
console.log(classify(-5));
console.log(classify(0));
console.log(classify(42));
