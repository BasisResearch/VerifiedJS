// Nested while loops
let total = 0;
let i = 0;
while (i < 3) {
  let j = 0;
  while (j < 3) {
    total = total + 1;
    j = j + 1;
  }
  i = i + 1;
}
console.log(total); // 9
