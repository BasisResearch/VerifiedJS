// Test: try/catch variable scoping (ECMA-262 §13.15)
// catch param is block-scoped
var result = 0;
try {
  throw 42;
} catch (e) {
  result = 1;
}
console.log(result);
// Expected: 1
