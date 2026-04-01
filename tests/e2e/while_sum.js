// Test while loop accumulating a sum (ECMA-262 §13.7.4)
var i = 1;
var sum = 0;
while (i <= 5) {
  sum = sum + i;
  i = i + 1;
}
console.log(sum);
