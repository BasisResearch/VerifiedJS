// Nested if-else (ECMA-262 §13.6)
var x = 15;
if (x > 20) {
  console.log("big");
} else {
  if (x > 10) {
    console.log("medium");
  } else {
    console.log("small");
  }
}
