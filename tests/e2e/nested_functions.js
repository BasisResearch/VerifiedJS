function outer(x) {
  function inner(y) {
    return x + y;
  }
  return inner(10);
}
var result = outer(5);
