// Test: for loop with early break (ECMA-262 §13.7, §13.8)
var result = 0;
for (var i = 0; i < 10; i = i + 1) {
  if (i === 5) {
    break;
  }
  result = result + i;
}
console.log(result);
// Expected: 10
