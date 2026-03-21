// Deeply nested if with returns
function grade(score) {
  if (score >= 90) return "A";
  if (score >= 80) return "B";
  if (score >= 70) return "C";
  if (score >= 60) return "D";
  return "F";
}
console.log(grade(95));
console.log(grade(85));
console.log(grade(55));
