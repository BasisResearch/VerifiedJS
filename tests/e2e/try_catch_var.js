// Try-catch with error variable (ECMA-262 §13.15)
try {
  throw "oops";
} catch (e) {
  console.log(e);
}
console.log("done");
