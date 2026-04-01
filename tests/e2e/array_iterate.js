// E2E: counting loop (ECMA-262 §13.7.4)
// expected: 0
// expected: 1
// expected: 2

var i = 0;
while (i < 3) {
  console.log(i);
  i = i + 1;
}
