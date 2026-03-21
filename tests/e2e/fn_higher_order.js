// Test: higher-order function (ECMA-262 §14.1)
function apply(f, x) {
  return f(x);
}
function double(n) {
  return n * 2;
}
console.log(apply(double, 21));
// Expected: 42
