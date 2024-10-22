function dbg(...args) {
  console.log(...args);
  return args[args.length - 1];
}

// const { Arr, Bool, Tvar, vari, app, fn, EMP, REFL, ASSUME, eq } = Kernel;
// const { prove } = Tactics;

// console.log("begin");
// const p = vari(Bool, "p");
// const q = vari(Bool, "q");
// const landr = BoolThms.AND(ASSUME(p), ASSUME(q));
// console.log(landr.show());
// console.log(toHex(landr.hash()));
// const ltolandr = BoolThms.DISCH(p, landr);
// console.log(ltolandr.show());
// console.log(BoolThms.MP(ltolandr, ASSUME(p)).show());

// console.log(ltolandr.free.map((x) => x.show()));

const parser = mkParser({
  T: {
    arity: 0,
    alias: {},
  },
  F: {
    arity: 0,
    alias: {},
  },
  "→": {
    binop: true,
    arity: 2,
    alias: {
      readable: "arrow",
      ascii: "->",
    },
  },
  "∧": {
    binop: true,
    arity: 2,
    alias: {
      readable: "and",
      ascii: "&",
    },
  },
  "∨": {
    binop: true,
    arity: 2,
    alias: {
      readable: "or",
      ascii: "|",
    },
  },
  "∀": {
    arity: 2,
    alias: {
      readable: "forall",
      ascii: "\-/",
    },
  },
  "∃": {
    arity: 2,
    alias: {
      readable: "exists",
      ascii: "EE",
    },
  },
});

function parse(str) {
  const result = parser(str);
  if(result.failed || result.rest.length > 0) {
    console.error("parse trace: ", result.trace);
    throw new Error("parse failed");
  }
  console.log("parse trace: ", result.trace);
  return result.matched;
}