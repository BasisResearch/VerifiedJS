// E2E: variable scoping with let (ECMA-262 §13.3.1)
// expected: 10
// expected: 20
// expected: 10

let x = 10;
console.log(x);
if (true) {
  let x = 20;
  console.log(x);
}
console.log(x);
