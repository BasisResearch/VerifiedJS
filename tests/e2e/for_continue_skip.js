// For loop with continue to skip even numbers
var sum = 0;
for (var i = 1; i <= 10; i = i + 1) {
  if (i === 3 || i === 6 || i === 9) continue;
  sum = sum + i;
}
console.log(sum);
