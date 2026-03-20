// E2E: compound assignment operators (ECMA-262 §13.15.2)
// expected: 15
// expected: 5
// expected: 50
// expected: 10

let x = 10;
x += 5;
console.log(x);
x -= 10;
console.log(x);
x *= 10;
console.log(x);
x /= 5;
console.log(x);
