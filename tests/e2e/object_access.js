// E2E: object property access (ECMA-262 §12.2.6, §12.3.2)
// expected: 42
// expected: hello

var obj = { x: 42, y: "hello" };
console.log(obj.x);
console.log(obj.y);
