function dbg(...args) {
  console.log(...args);
  return args[args.length - 1];
}

const MiniDefs = {
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
  "⇒": {
    binop: true,
    arity: 2,
    alias: {
      readable: "implies",
      ascii: "=>",
    },
  },
  "∨": {
    binop: true,
    arity: 2,
    alias: {
      readable: "or",
      ascii: "||",
    },
  },
  "∀": {
    arity: 2,
    alias: {
      readable: "forall",
      ascii: "-/",
    },
  },
  "∃": {
    arity: 2,
    alias: {
      readable: "exists",
      ascii: "EE",
    },
  },
};

const parser = mkParser(MiniDefs, 3);

function parse(str) {
  const result = parser(str);
  if (result.failed || result.rest.length > 0) {
    console.error("parse trace: ", result.trace);
    throw new Error("parse failed");
  }
  return JSON.stringify(result.matched, null, 2);
  // const term = fromJSON(result.matched, MiniDefs, {});
  // return term.show();
}
