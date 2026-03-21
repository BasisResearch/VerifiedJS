// GCD via subtraction
function gcd(a, b) {
  while (a !== b) {
    if (a > b) {
      a = a - b;
    } else {
      b = b - a;
    }
  }
  return a;
}
console.log(gcd(12, 8)); // 4
