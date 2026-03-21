// Deeply nested conditionals
let x = 42;
if (x > 0) {
  if (x > 10) {
    if (x > 40) {
      console.log(1); // 1
    } else {
      console.log(2);
    }
  } else {
    console.log(3);
  }
} else {
  console.log(4);
}
