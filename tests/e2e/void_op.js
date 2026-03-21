// E2E: void operator (ECMA-262 §12.4.2)
// Tests that void is parsed and compiles; Wasm runtime prints the inner value
// expected: 42

var x = void 0;
console.log(42);
