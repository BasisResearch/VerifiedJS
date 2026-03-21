// E2E: while loop with false condition never executes body
// expected: done

while (false) {
  console.log("bad");
}
console.log("done");
