// E2E: new operator creates object instances (ECMA-262 §12.3.3)
function Point(x, y) {
  this.x = x;
  this.y = y;
}
var p = new Point(1, 2);
console.log(typeof p);
// Expected output: object
