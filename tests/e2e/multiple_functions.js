function double(x) {
  return x * 2;
}
function square(x) {
  return x * x;
}
var a = double(3);
console.log(a);
var b = square(a);
console.log(b);
var c = double(square(2));
console.log(c);
