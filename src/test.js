function dbg(...args) {
  console.log(...args);
  return args[args.length - 1];
}

const { Arr, Bool, Tvar, vari, app, fn, EMP, REFL, ASSUME } = Kernel;
const { IMP_THM } = BoolThms;

console.log(IMP_THM(vari(Bool, "p"), vari(Bool, "q")).show());

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
