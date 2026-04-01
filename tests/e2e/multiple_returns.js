// Multiple function return paths (ECMA-262 §14.1)
function abs(x) {
  if (x < 0) { return -x; }
  return x;
}
console.log(abs(5));
console.log(abs(-3));
console.log(abs(0));
