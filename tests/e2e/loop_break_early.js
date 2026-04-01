// While loop with early break (ECMA-262 §13.8)
var i = 0;
while (i < 100) {
  if (i === 5) { break; }
  i = i + 1;
}
console.log(i);
