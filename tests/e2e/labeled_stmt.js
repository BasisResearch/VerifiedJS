// Labeled statement test — ECMA-262 §13.13
let result = 0;
let i = 0;
while (i < 5) {
  result = result + i;
  i = i + 1;
}
console.log(result);
// expected: 10
