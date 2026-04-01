// Test: nested try/finally (ECMA-262 §13.15)
var log = 0;
try {
  try {
    log = 1;
  } finally {
    log = log + 10;
  }
} finally {
  log = log + 100;
}
console.log(log);
// Expected: 111
