// Higher-order function (ECMA-262 §14.1)
function apply(f, x) { return f(x); }
function square(n) { return n * n; }
console.log(apply(square, 7));
