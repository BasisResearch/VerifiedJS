// Simulate array mapping with a loop (ECMA-262 §13.7.4)
var arr = [1, 2, 3, 4, 5];
var i = 0;
var sum = 0;
while (i < arr.length) {
  sum = sum + arr[i] * 2;
  i = i + 1;
}
console.log(sum);
