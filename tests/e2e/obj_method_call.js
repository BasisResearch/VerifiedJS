// Test: object with method call (ECMA-262 §12.3.2, §14.1)
var obj = {
  x: 10,
  double: function() { return 20; }
};
console.log(obj.double());
// Expected: 20
