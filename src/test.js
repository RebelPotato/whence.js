function dbg(...args) {
  console.log(...args);
  return args[args.length - 1];
}

const { Arr, Bool, Tvar, vari, app, fn, EMP, REFL, ASSUME, eq } = Kernel;
const { prove } = Tactics;

console.log("begin");
const p = vari(Bool, "p");
const q = vari(Bool, "q");
const landr = BoolThms.AND(ASSUME(p), ASSUME(q));
console.log(landr.show());
console.log(toHex(landr.hash()));
const ltolandr = BoolThms.DISCH(p, landr);
console.log(ltolandr.show());
console.log(BoolThms.MP(ltolandr, ASSUME(p)).show());

console.log(ltolandr.free.map((x) => x.show()));