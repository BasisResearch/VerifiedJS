// Test nested object literal creation and access
let obj = { a: { b: 42 } };
let inner = obj.a;
console.log(inner.b);
// expected: 42
