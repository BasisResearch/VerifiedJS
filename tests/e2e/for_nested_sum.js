// Nested for loops: multiplication table sum
var sum = 0;
for (var i = 1; i <= 3; i = i + 1) {
  for (var j = 1; j <= 3; j = j + 1) {
    sum = sum + i * j;
  }
}
console.log(sum);
