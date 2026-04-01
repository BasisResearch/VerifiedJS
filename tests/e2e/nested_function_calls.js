// Test nested function calls as arguments
function double(x) {
  return x * 2;
}
function add(a, b) {
  return a + b;
}
console.log(add(double(3), double(4)));
// expected: 14
