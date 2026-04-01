// Nullish coalescing (ECMA-262 §12.13)
let a = null;
let b = a !== null && a !== undefined ? a : 10;
console.log(b);
let c = 5;
let d = c !== null && c !== undefined ? c : 20;
console.log(d);
