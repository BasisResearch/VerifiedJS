// E2E: function with no return returns undefined (ECMA-262 §14.1)
// expected: undefined

function noop() {}
var result = noop();
console.log(result);
