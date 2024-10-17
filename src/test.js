function dbg(...args) {
  console.log(...args);
  return args[args.length - 1];
}

const { Arr, Bool, Tvar, vari, app, fn, EMP, REFL, ASSUME, eq } = Kernel;
const { prove } = Tactics;

const test = eq(fn(Bool, (x) => x), fn(Tvar("A"), (x) => x));
console.log(test.show(), "::", test.type.show());
const proof = prove(test, Tactics.reflTac).orThrow();
console.log(proof.show());