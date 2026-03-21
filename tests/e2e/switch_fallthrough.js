// Test switch with explicit break
let x = 2;
let result = 0;
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
// expected: 20
