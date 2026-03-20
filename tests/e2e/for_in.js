// E2E: for-in iterates over object property keys (ECMA-262 §13.7.5)
var obj = { a: 1, b: 2, c: 3 };
for (var key in obj) {
  console.log(key);
}
// Expected output: a, b, c (property keys)
