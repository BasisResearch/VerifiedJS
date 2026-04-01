// Simulate Array.reduce with a loop
function reduce(n, fn, init) {
  var acc = init;
  for (var i = 0; i < n; i = i + 1) {
    acc = fn(acc, i);
  }
  return acc;
}
function addFn(a, b) { return a + b; }
console.log(reduce(5, addFn, 0));
