// Object property mutation (ECMA-262 §9.1.9)
var obj = {};
obj.count = 0;
obj.count = obj.count + 1;
obj.count = obj.count + 1;
obj.count = obj.count + 1;
console.log(obj.count);
