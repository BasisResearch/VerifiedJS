// Test multiple function definitions and calls
function add(a, b) { return a + b; }
function double(x) { return x * 2; }
var result = double(add(3, 4));
console.log(result);
