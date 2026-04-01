// Odd/even classification function
function classify(n) {
  if (n / 2 === Math.floor(n / 2)) {
    return "even";
  } else {
    return "odd";
  }
}
console.log(classify(4));
console.log(classify(7));
console.log(classify(0));
