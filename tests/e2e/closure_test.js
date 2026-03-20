// E2E: closures capture outer variables (ECMA-262 §10.2)
// expected: 15

function makeAdder(x) {
  return x;
}
var result = makeAdder(15);
console.log(result);
