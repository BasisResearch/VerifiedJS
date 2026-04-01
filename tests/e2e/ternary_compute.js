// Ternary with computed conditions
function clamp(x, lo, hi) {
  return x < lo ? lo : (x > hi ? hi : x);
}
console.log(clamp(5, 1, 10));
console.log(clamp(-3, 0, 100));
console.log(clamp(999, 0, 100));
