// Test: abstract equality with type coercion (ECMA-262 §7.2.14)
console.log(null == undefined);
console.log(1 == true);
console.log(0 == false);
console.log("" == false);
console.log(null == false);
// Expected:
// true
// true
// true
// true
// false
