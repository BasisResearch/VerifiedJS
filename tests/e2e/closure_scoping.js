// Test: closure captures lexical scope (ECMA-262 §10.2)
function makeAdder(x) {
  return function(y) {
    return x + y;
  };
}
var add5 = makeAdder(5);
var result = add5(3);
console.log(result);
// Expected: 8
