// Power function via loop
function power(base, exp) {
  let result = 1;
  let i = 0;
  while (i < exp) {
    result = result * base;
    i = i + 1;
  }
  return result;
}
console.log(power(2, 10)); // 1024
