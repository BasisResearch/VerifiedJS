// Test for loop with early break
let found = -1;
for (let i = 0; i < 10; i = i + 1) {
  if (i === 7) {
    found = i;
    break;
  }
}
console.log(found);
// expected: 7
