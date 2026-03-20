// E2E: for-of iterates over iterable values (ECMA-262 §13.7.5.13)
var arr = [10, 20, 30];
for (var item of arr) {
  console.log(item);
}
// Expected output: 10, 20, 30
