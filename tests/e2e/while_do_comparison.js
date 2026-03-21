// Compare while vs do-while: do-while runs body at least once
var a = 0;
while (false) { a = a + 1; }
console.log(a);
var b = 0;
do { b = b + 1; } while (false);
console.log(b);
