// Test: nested object property access (ECMA-262 §12.3.2)
var obj = {
  a: { b: { c: 42 } }
};
console.log(obj.a.b.c);
// Expected: 42
