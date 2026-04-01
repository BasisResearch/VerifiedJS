// Nested loops (ECMA-262 §13.7)
let result = 0;
let i = 0;
while (i < 3) {
  let j = 0;
  while (j < 3) {
    result = result + 1;
    j = j + 1;
  }
  i = i + 1;
}
console.log(result);
