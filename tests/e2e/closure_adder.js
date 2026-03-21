// Closure that captures a value (ECMA-262 §10.2)
function makeAdder(n) {
  function adder(x) { return x + n; }
  return adder;
}
var add5 = makeAdder(5);
console.log(add5(3));
console.log(add5(10));
