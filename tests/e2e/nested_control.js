var i = 0;
var count = 0;
while (i < 10) {
  if (i > 2) {
    if (i < 7) {
      count = count + 1;
      console.log(count);
    }
  }
  i = i + 1;
}
console.log(count);
