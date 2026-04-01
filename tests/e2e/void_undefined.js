// Test: void operator returns undefined (ECMA-262 §13.5)
var x = void 0;
console.log(typeof x);
console.log(x === undefined);
// Expected:
// undefined
// true
