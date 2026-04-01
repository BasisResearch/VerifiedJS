// E2E: for loop (ECMA-262 §13.7.4)
// expected: 0
// expected: 1
// expected: 2
// expected: 3
// expected: 4

for (var i = 0; i < 5; i = i + 1) {
  console.log(i);
}
