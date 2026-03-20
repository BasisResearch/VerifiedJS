// E2E: while loop with break (ECMA-262 §13.8)
// expected: 5

let i = 0;
while (true) {
  if (i === 5) break;
  i = i + 1;
}
console.log(i);
