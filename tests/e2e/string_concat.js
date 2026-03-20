// E2E: string concatenation with type coercion (ECMA-262 §12.8.3)
// expected: hello 42
// expected: true!
// expected: count: 5

console.log("hello " + 42);
console.log("true" + "!");
console.log("count: " + 5);
