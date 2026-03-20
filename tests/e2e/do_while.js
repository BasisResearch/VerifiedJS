// E2E: do-while loop (ECMA-262 §13.7.2)
// expected: 0
// expected: 1
// expected: 2

var i = 0;
do {
  console.log(i);
  i = i + 1;
} while (i < 3);
