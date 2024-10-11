const tests = [
  () => {
    const { l, a, c } = Makers1;
    const k = l((x) => l((y) => x));
    const i = l((x) => x);
    const ki = a(k, i);
    const a2 = (x, y, z) => a(a(x, y), z);
    return [a2(k, c(1), c(2)), a2(ki, c(1), c(2))].flatMap((t) => [
      ev1(t),
      show1(t),
    ]);
  },
];

const displayEl = document.getElementById("display");

// tests.forEach((test, i) => {
//   const [ev, show] = test();
//   const evEl = document.createElement("div");
//   evEl.innerHTML = `Test ${i + 1}: ${ev}`;
//   displayEl.appendChild(evEl);
// });

function h(tag, attrs, children) {
  const el = document.createElement(tag);
  Object.entries(attrs).forEach(([k, v]) => el.setAttribute(k, v));
  const childEls = children.map((c) =>
    typeof c === "string" ? document.createTextNode(c) : c
  );
  childEls.forEach((c) => el.appendChild(c));
  return el;
}
