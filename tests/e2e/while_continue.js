// While loop with conditional accumulation (ECMA-262 §13.7)
let i = 0;
let sum = 0;
while (i < 10) {
  i = i + 1;
  if (i > 5) {
    sum = sum + i;
  }
}
console.log(sum);
