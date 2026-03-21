// Find minimum of three numbers
function minOf3(a, b, c) {
  if (a <= b && a <= c) return a;
  if (b <= c) return b;
  return c;
}
console.log(minOf3(3, 1, 2));
console.log(minOf3(5, 5, 3));
console.log(minOf3(1, 2, 3));
