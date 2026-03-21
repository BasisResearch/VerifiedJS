// Function with no explicit return gives undefined
function noReturn() {
  let x = 42;
}
let result = noReturn();
console.log(result); // undefined
