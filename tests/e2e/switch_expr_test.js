// Test switch with expression tests and default fallthrough
var x = 2;
var result = 0;
switch (x + 1) {
  case 1: result = 10; break;
  case 3: result = 30; break;
  case 5: result = 50; break;
  default: result = -1;
}
console.log(result);
