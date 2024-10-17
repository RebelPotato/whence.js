function dbg(...args) {
  console.log(...args);
  return args[args.length - 1];
}

const { Arr, Bool, Tvar, vari, app, fn, EMP, REFL, ASSUME, eq } = Kernel;
const { prove } = Tactics;

const landr = BoolThms.AND(ASSUME(vari(Bool, "p")), ASSUME(vari(Bool, "q")));
console.log(BoolThms.AND_R(landr).show());