// E2E: higher-order functions — passing functions as arguments (ECMA-262 §10.2)
// expected: 8

function apply(f, x) {
  return f(x);
}
function double(n) {
  return n * 2;
}
console.log(apply(double, 4));
