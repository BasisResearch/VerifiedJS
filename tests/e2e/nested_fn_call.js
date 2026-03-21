// Nested function calls (ECMA-262 §13.3.1)
function add(a, b) { return a + b; }
function mul(a, b) { return a * b; }
console.log(add(mul(2, 3), mul(4, 5)));
