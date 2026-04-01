// Nested function calls test
function add(a, b) { return a + b; }
function mul(a, b) { return a * b; }
console.log(add(mul(2, 3), mul(4, 5)));
// expected: 26
