const { l, a, c, v } = Full;

const k = l(l(v(1)));
const i = l(v(0));
const ki = a(k, i);
console.log(Full.show(ki));
console.log(Full.show(Full.norm(ki)));

function toChurch(n) {
  if(n === 0) return l(l(v(0)));
  const f = v(1);
  const x = v(0);
  return l(l(a(a(toChurch(n - 1), f), a(f, x))));
}
function addChurch(m, n) {
  const f = v(1);
  const x = v(0);
  return l(l(a(a(m, f), a(a(n, f), x))));
}
const two = toChurch(2);
const three = toChurch(3);
const fiveAdd = addChurch(two, three);
const five = toChurch(5);
console.log(Full.show(fiveAdd));
console.log(Full.show(Full.norm(fiveAdd)));
console.log(Full.show(five));

// const { l, a, c } = Maker;
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
//   () => {
//     const { l, a, c } = Makers1;
//     const k = l((x) => l((y) => x));
//     const i = l((x) => x);
//     const ki = a(k, i);
//     const a2 = (x, y, z) => a(a(x, y), z);
//     return [a2(k, c(1), c(2)), a2(ki, c(1), c(2))].flatMap((t) => [
//       ev1(t),
//       show1(t),
//     ]);
//   },
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