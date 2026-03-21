// For loop with break
var x = 0;
for (var i = 0; i < 100; i = i + 1) {
  if (i === 7) break;
  x = x + 1;
}
console.log(x);
