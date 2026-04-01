// Test: while loop accumulation — Gauss sum (ECMA-262 §13.7.3)
var sum = 0;
var i = 1;
while (i <= 100) {
  sum = sum + i;
  i = i + 1;
}
console.log(sum);
// Expected: 5050
