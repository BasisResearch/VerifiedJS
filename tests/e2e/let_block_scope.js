// Test: block scoping with let (ECMA-262 §13.3.1)
var x = 10;
{
  let x = 20;
  console.log(x);
}
console.log(x);
// Expected:
// 20
// 10
