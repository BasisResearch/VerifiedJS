// FizzBuzz (ECMA-262 §13.7.4, §13.6)
var i = 1;
while (i <= 15) {
  if (i % 3 === 0 && i % 5 === 0) {
    console.log("FizzBuzz");
  } else if (i % 3 === 0) {
    console.log("Fizz");
  } else if (i % 5 === 0) {
    console.log("Buzz");
  } else {
    console.log(i);
  }
  i = i + 1;
}
