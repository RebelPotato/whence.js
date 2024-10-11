const Maker = {
  // lambda, application, constant
  l: (fn) => (S) => (mustHave(S, "l"), S.l((x) => fn((_) => x)(S))), // tricky
  a: (e1, e2) => (S) => (mustHave(S, "a"), S.a(e1(S), e2(S))),
  c: (v) => (S) => (mustHave(S, "c"), S.c(v)),

  // type arrow, type constant
  to: (t1, t2) => (S) => (mustHave(S, "to"), S.to(t1(S), t2(S))),
  t: (n) => (S) => (mustHave(S, "t"), S.t(n)),

  // kind *
  star: (S) => (mustHave(S, "star"), S.star),

  // type annotation
  of: (e, t) => (S) => (mustHave(S, "of"), S.of(e(S), t(S))),
};

const EvalS = {
  l: (fn) => fn,
  a: (e1, e2) => e1(e2),
  c: (v) => v,
  of: (e, _) => e,

  to: (t1, t2) => undefined,
  t: (_) => undefined,
  star: undefined,
};

function eva(term) {
  return term(EvalS);
}

// term == Int -> String
const ShowS = {
  l: (fn) => (level) => {
    // fn :: term a -> term b == (Int -> String) -> (Int -> String)
    const x = `x${level}`;
    return `(λ${x}. ${fn((_) => x)(level + 1)})`;
  },
  a: (e1, e2) => (level) => `(${e1(level)} ${e2(level)})`,
  c: (v) => (_) => `${v}`,

  to: (t1, t2) => level => `(${t1(level)} -> ${t2(level)})`,
  t: n => _ => `${n}`,
  star: _ => "*",

  of: (e, t) => (level) => `${e(level)} :: ${t(level)}`,
};

function show(term) {
  return term(ShowS)(0);
}

const MatchS = {
  to: (a0, b0) => (S) => (mustHave(S, "to"), S.to(a0, b0)),
  t: (n0) => (S) => (mustHave(S, "t"), S.t(n0)),
};

// term == term -> bool
const EqS = {
  to: (a0, b0) => (t) =>
    t(MatchS)({
      to: (a1, b1) => a0(a1) && b0(b1),
      t: (_) => false,
    }),
  t: (n0) => (t) =>
    t(MatchS)({
      t: (n1) => n0 === n1,
      to: (_0, _1) => false,
    }),
};

function eq(a, b) {
  return a(EqS)(b);
}

// term == [Result type, type -> Result ()]
const KindCheckS = {
  to: ([a, _ca], [b, _cb]) => {
    const term = Maker.to(a, b);
    return [term, assertTypeEq(term)];
  },
  t: (n) => {
    const term = Maker.t(n);
    return [term, assertTypeEq(term)];
  },
};

// term == [Result type, type -> Result ()]
// an inferer with a checker
const TypeInferS = {
  of: ([_t, c], [tAnno, _cAnno]) => {
    c(tAnno);
    return [tAnno, assertTypeEq(tAnno)];
  },
  a: ([t1, _c1], [_t2, c2]) =>
    t1(MatchS)({
      to: (a, b) => {
        c2(a);
        return [b, assertTypeEq(b)];
      },
    }),
  c: (n) => {
    let type = undefined;
    if(Number.isInteger(n)) type = "Int";
    if(typeof n === "string") type = "String";
    if(typeof n === "boolean") type = "Bool";
    const term = Maker.t(n);
    return [term, assertTypeEq(term)];
  },
};

const TypeCheckS = {
  // fn :: ([Result type, type -> Result ()]) -> [Result type, type -> Result ()], t :: type
  l: (fn) => [undefined, (t) => {
    const [lhs, rhs] = t(MatchS)({
      to: (a, b) => [a, b],
    });
    fn([rhs, assertTypeEq(rhs)])[1](lhs);
  }],
};

const TypingS = {
  ...KindCheckS,
  ...TypeInferS,
  ...TypeCheckS,
}

function typeCheck(term) {
  return term(TypingS);
}

// Appendix

function mustHave(obj, key) {
  if (!Object.hasOwn(obj, key))
    throw Error(`Tried to get key ${key} from Object ${obj}`);
}

function merge(...objs) {
  return objs.reduce((acc, obj) => Object.assign(acc, obj), {});
}

function assertTypeEq(expected) {
  return (got) => {
    if (!eq(expected, got))
      throw Error(`Expected type ${show(expected)} but inferred ${show(got)}`);
  };
}

function dbg(...args) {
  console.log(...args);
  return args[args.length - 1];
}
