// Test: switch/case basic matching (ECMA-262 §13.12)
var x = 2;
var result = 0;
switch (x) {
  case 1:
    result = 10;
    break;
  case 2:
    result = 20;
    break;
  case 3:
    result = 30;
    break;
  default:
    result = -1;
}
console.log(result);
// Expected: 20
