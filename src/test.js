// const { l, a, c, v } = Named;

// const t = l("x", a(l("y", v("y")), v("x"))); // \x. (\y. y) x
// console.log(Named.show(t));
// // under strong normalization, this should produce \x. x
// console.log(Named.show(Named.simp(t)));

// const k = l("x", l("y", v("x")));
// const i = l("x", v("x"));
// console.log(Named.show(a(k, i)));
// console.log(Named.show(Named.simp(a(k, i)))); // should be \x. \y. y
// const ki = Named.simp(a(k, i));
// const not = l("f", a(a(v("f"), ki), k));
// console.log(Named.show(a(not, ki)));
// console.log(Named.show(Named.simp(a(not, ki)))); // should be \x. \y. x

// function toChurch(n) {
//   const f = v("f");
//   const x = v("x");
//   if(n === 0) return l("f", l("x", x));
//   return l("f", l("x", a(a(toChurch(n - 1), f), a(f, x))));
// }
// function addChurch(m, n) {
//   const f = v("f");
//   const x = v("x");
//   return l("f", l("x", a(a(m, f), a(a(n, f), x))));
// }
// const two = toChurch(2);
// const three = toChurch(3);
// const fiveAdd = addChurch(two, three);
// const five = toChurch(5);
// console.log(Named.show(fiveAdd));
// console.log(Named.show(Named.simp(fiveAdd)));
// console.log(Named.show(five));
// console.log(Named.show(Named.simp(five)));

const { l, a, c } = Higher;
const k = l((x) => l((y) => x));
const i = l((x) => x);
const ki = a(k, i);
const kiN = HigherToNamed(ki);
console.log(Higher.show(NamedToHigher(kiN)));
console.log(Higher.show(Higher.simp(ki)));
// function toChurch(n) {
//   return n === 0
//     ? l((f) => l((x) => x))
//     : l((f) => l((x) => a(a(toChurch(n - 1), f), a(f, x))));
// }
// const twice = toChurch(2);
// const thrice = toChurch(3);
// logshow(twice);
// logshow(normalize(twice));

// const tests = [
// ];

// const displayEl = document.getElementById("display");

// // tests.forEach((test, i) => {
// //   const [ev, show] = test();
// //   const evEl = document.createElement("div");
// //   evEl.innerHTML = `Test ${i + 1}: ${ev}`;
// //   displayEl.appendChild(evEl);
// // });

// function h(tag, attrs, children) {
//   const el = document.createElement(tag);
//   Object.entries(attrs).forEach(([k, v]) => el.setAttribute(k, v));
//   const childEls = children.map((c) =>
//     typeof c === "string" ? document.createTextNode(c) : c
//   );
//   childEls.forEach((c) => el.appendChild(c));
//   return el;
// }