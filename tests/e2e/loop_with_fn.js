// Loop calling a function each iteration
function addTwo(n) { return n + 2; }
var x = 0;
for (var i = 0; i < 5; i = i + 1) {
  x = addTwo(x);
}
console.log(x);
