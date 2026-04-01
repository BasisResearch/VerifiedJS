// E2E: functions as first-class values (ECMA-262 §14.1)
// expected: 7

function add(a, b) {
  return a + b;
}
var f = add;
console.log(f(3, 4));
