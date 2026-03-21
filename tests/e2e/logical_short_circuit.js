// Test: logical operator short-circuit evaluation (ECMA-262 §13.12)
var x = 0;
var a = false || 42;
var b = true && 99;
var c = null || "default";
var d = "truthy" && "second";
console.log(a);
console.log(b);
console.log(c);
console.log(d);
// Expected:
// 42
// 99
// default
// second
