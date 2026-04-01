// Test function returning an object
function makePoint(x, y) {
  return { x: x, y: y };
}
let p = makePoint(3, 4);
console.log(p.x);
console.log(p.y);
// expected: 3
// expected: 4
