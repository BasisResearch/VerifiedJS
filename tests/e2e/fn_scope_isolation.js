// Test function scope isolation (ECMA-262 §10.2)
var x = 1;
function inc() { var x = 2; return x; }
var y = inc();
console.log(x);
console.log(y);
