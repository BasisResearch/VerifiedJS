// Sum of digits using modulo and division
function sumDigits(n) {
  var sum = 0;
  while (n > 0) {
    var digit = n - Math.floor(n / 10) * 10;
    sum = sum + digit;
    n = Math.floor(n / 10);
  }
  return sum;
}
console.log(sumDigits(123));
