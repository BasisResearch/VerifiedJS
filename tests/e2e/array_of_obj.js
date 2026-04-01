// Test: array of objects (ECMA-262 §12.2.5, §12.2.6)
var arr = [{x: 1}, {x: 2}, {x: 3}];
var sum = 0;
var i = 0;
while (i < 3) {
  sum = sum + arr[i].x;
  i = i + 1;
}
console.log(sum);
// Expected: 6
