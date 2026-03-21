// E2E: boolean coercion in conditions (ECMA-262 §7.2.14)
// expected: truthy
// expected: falsy

if (1) {
  console.log("truthy");
} else {
  console.log("falsy");
}
if (0) {
  console.log("truthy");
} else {
  console.log("falsy");
}
