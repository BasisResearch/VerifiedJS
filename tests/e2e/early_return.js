// Early return from function (ECMA-262 §13.10)
function findFirst(a, b, c) {
  if (a > 0) { return a; }
  if (b > 0) { return b; }
  return c;
}
console.log(findFirst(5, 10, 15));
console.log(findFirst(-1, 7, 15));
console.log(findFirst(-1, -2, 99));
