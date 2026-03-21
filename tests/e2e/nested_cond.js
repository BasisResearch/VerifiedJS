// Nested conditional expressions
var a = 10;
var b = 20;
var c = a > b ? a : b;
console.log(c);
var d = a < b ? (a > 5 ? a : 5) : b;
console.log(d);
