// Chained function calls (ECMA-262 §13.3.1)
function inc(x) { return x + 1; }
let result = inc(inc(inc(0)));
console.log(result);
