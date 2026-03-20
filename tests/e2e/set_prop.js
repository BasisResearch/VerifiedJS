// E2E: property assignment on objects (ECMA-262 §9.1.9 [[Set]])
var obj = {};
obj.x = 42;
obj.y = "hello";
console.log(obj.x);
console.log(obj.y);
// Expected output: 42, hello
