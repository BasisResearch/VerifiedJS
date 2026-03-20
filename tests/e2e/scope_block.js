// E2E: block scoping with let (ECMA-262 §13.3.1)
// expected: 1
// expected: 2
// expected: 1

let x = 1;
console.log(x);
{
  let x = 2;
  console.log(x);
}
console.log(x);
