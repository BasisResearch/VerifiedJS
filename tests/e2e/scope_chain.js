// Scope chain: inner function sees outer var
var x = 100;
function addX(n) { return n + x; }
console.log(addX(5));
console.log(addX(20));
