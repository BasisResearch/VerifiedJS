// Primality test function (ECMA-262 §13.7.4, §13.6)
function isPrime(n) {
  if (n < 2) { return false; }
  var i = 2;
  while (i * i <= n) {
    if (n % i === 0) { return false; }
    i = i + 1;
  }
  return true;
}
console.log(isPrime(2));
console.log(isPrime(7));
console.log(isPrime(10));
console.log(isPrime(13));
