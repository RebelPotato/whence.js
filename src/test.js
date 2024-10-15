function dbg(...args) {
  console.log(...args);
  return args[args.length - 1];
}

const { fn, a, c } = Core.Self;
const cshow = term => show(Core, term);
const csimp = term => simp(Core, term);

const k = fn((x) => fn((_) => x));
const i = fn((x) => x);
const ki = a(k, i);
dbg(show(Core, ki));
dbg(show(Core, simp(Core, ki)));

const zero = fn((_) => fn((x) => x));
function inc(n) {
  return fn((f) => fn((x) => a(a(n, f), a(f, x))));
}
function toChurch(n) {
  return n === 0
    ? zero
    : inc(toChurch(n - 1));
}
function add(m, n) {
  return fn((f) => fn((x) => a(a(m, f), a(a(n, f), x))));
}
const twice = toChurch(2);
const thrice = toChurch(3);
dbg(show(Core, twice));
dbg(show(Core, thrice));
dbg(show(Core, add(twice, thrice)));
dbg(cshow(csimp(add(twice, thrice))));

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