// E2E: comma operator / sequence expressions (ECMA-262 §12.16)
// expected: 3
// expected: 10

var x = (1, 2, 3);
console.log(x);

function f() {
  var a = 5;
  var b = 10;
  return b;
}
console.log(f());
