// Sign function
function sign(x) {
  if (x > 0) return 1;
  if (x < 0) return -1;
  return 0;
}
console.log(sign(42));
console.log(sign(-7));
console.log(sign(0));
