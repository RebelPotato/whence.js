class ADT {
  static sym = Symbol("type");
  constructor(props, options = { show: false }) {
    this.show = options.show;
    // todo: move visitor to prototype
    for (const k of Object.keys(props)) {
      const len = props[k];
      this[k] = function (...args) {
        if (args.length != len)
          throw Error(
            `Constructor ${k} should receive ${len} arguments but got ${args.length}`
          );
        const visitor = {
          match(branches) {
            if (!Object.hasOwn(branches, k))
              throw Error(`Invalid match: did not match ${k}`);
            return branches[k](...args);
          },
        };
        if (this.show) {
          visitor.type = k;
          visitor.params = args;
        }
        visitor[ADT.sym] = this;
        Object.freeze(visitor);
        return visitor;
      }.bind(this);
    }
  }
  hasInstance(obj) {
    return Object.hasOwn(obj, ADT.sym) && Object.hasOwn(obj[ADT.sym], this);
  }
}

function once(fn) {
  let result = undefined;
  let called = false;
  return function (...args) {
    if (!called) {
      result = fn(...args);
      called = true;
    }
    return result;
  };
}
function put(env, x, v) {
  const newEnv = { ...env };
  newEnv[x] = v;
  return newEnv;
}
function freshen(env, n) {
  while (Object.hasOwn(env, n)) n = n + "'";
  return n;
}

// a language has: eval, norm, show
// this may not be the best way to represent a language:
// it forfeits tagless final's composability?

// higher order embedding
const Higher = (() => {
  const Lang = {
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

  // Evaluation by translating to js functions
  // term a == a
  Lang.EvalS = {
    l: (fn) => fn,
    a: (e1, e2) => e1(e2),
    c: (v) => v,
  };
  Lang.eval = function (term) {
    return term(this.EvalS);
  };

  // Translate term to string

  // term a == Int -> String
  Lang.ShowS = {
    l: (fn) => (level) => {
      // fn :: term a -> term b == (Int -> String) -> (Int -> String)
      const x = `x${level}`;
      return `(λ${x}. ${fn((_) => x)(level + 1)})`;
    },
    a: (e1, e2) => (level) => `(${e1(level)} ${e2(level)})`,
    c: (v) => (_) => `${v}`,

    to: (t1, t2) => (level) => `(${t1(level)} -> ${t2(level)})`,
    t: (n) => (_) => `${n}`,
    star: (_) => "*",

    of: (e, t) => (level) => `${e(level)} :: ${t(level)}`,
  };

  Lang.show = function (term) {
    return term(this.ShowS)(0);
  };

  Lang.simp = function (term) {
    return NamedToHigher(Named.simp(HigherToNamed(term)));
  }

  return Lang;
})();

// Translate term to string
// Normalization
// we extend evaluation's return value to include terms.
// V = I Int | T Term | A (V -> V)

const Full = (() => {
  const Lang = {
    l: (t) => (S) => (mustHave(S, "l"), S.l(t(S))),
    a: (t1, t2) => (S) => (mustHave(S, "a"), S.a(t1(S), t2(S))),
    v: (n) => (S) => (mustHave(S, "v"), S.v(n)),
    c: (v) => (S) => (mustHave(S, "c"), S.c(v)),
  };

  Lang.EvalS = {
    l: (t) => (env) => (x) => t([x, ...env]),
    a: (t1, t2) => (env) => t1(env)(t2(env)),
    v: (n) => (env) => env[n],
    c: (v) => (_) => v,
  };
  Lang.eval = function (term) {
    return term(this.EvalS)([]);
  };

  const Value = new ADT({ C: 1, A: 1, T: 1 });
  function readBack(value) {
    return value.match({
      C: (v) => Lang.c(v),
      T: (e) => e,
      A: (f) => Lang.l(readBack(f(Value.T(Lang.v(0))))),
    });
  }

  // normalize a term. does not reach under lambdas!
  // term a == env -> V a
  // env = [V a]
  Lang.NormS = {
    l: (t) => (env) => {
      const otherwise = () => Value.A((x) => t([x, ...env])); // regular evaluation
      if (env.length == 0) return otherwise();
      return env[0].match({
        T: () => Value.T(Lang.l(readBack(t([Value.T(Lang.v(0)), ...env])))), // readback
        A: otherwise,
        C: otherwise,
      });
    },
    a: (t1, t2) => (env) => {
      const otherwise = () =>
        t1(env).match({
          A: (f) => f(t2(env)),
        });
      if (env.length == 0) return otherwise();
      return env[0].match({
        T: () => Value.T(Lang.a(readBack(t1(env)), readBack(t2(env)))), // readback
        A: otherwise,
        C: otherwise,
      });
    },
    v: (n) => (env) =>
      env[n].match({
        T: () => Value.T(Lang.v(n)), // readback
        A: () => env[n],
        C: () => env[n],
      }),
    c: (v) => (env) => {
      const otherwise = () => Value.C(v);
      if (env.length == 0) return otherwise();
      return env[0].match({
        T: () => Value.T(Lang.c(v)), // readback
        A: otherwise,
        C: otherwise,
      });
    },
  };
  Lang.norm = function (term) {
    const value = term(this.NormS)([]);
    return readBack(value);
  };

  // term a == level -> a
  Lang.ShowS = {
    l: (t) => (level) => {
      const x = `x${level}`;
      return `(λ${x}. ${t(level + 1)})`;
    },
    a: (t1, t2) => (level) => `(${t1(level)} ${t2(level)})`,
    v: (n) => (level) => `x${level - n - 1}`,
    c: (v) => (_) => `${v}`,
  };
  Lang.show = function (term) {
    return term(this.ShowS)(0);
  };

  return Lang;
})();

const Named = (() => {
  const Lang = {
    l: (n, t) => (S) => (mustHave(S, "l"), S.l(n, t(S))),
    a: (t1, t2) => (S) => (mustHave(S, "a"), S.a(t1(S), t2(S))),
    v: (n) => (S) => (mustHave(S, "v"), S.v(n)),
    c: (v) => (S) => (mustHave(S, "c"), S.c(v)),
  };

  function put(env, x, v) {
    const newEnv = { ...env };
    newEnv[x] = v;
    return newEnv;
  }
  function freshen(env, n) {
    while (Object.hasOwn(env, n)) n = n + "'";
    return n;
  }

  Lang.EvalS = {
    l: (n, t) => (env) => (x) => t(put(env, n, x)),
    a: (t1, t2) => (env) => t1(env)(t2(env)),
    v: (n) => (env) => env[n],
    c: (v) => (_) => v,
  };
  Lang.eval = function (term) {
    return term(this.EvalS)({});
  };

  // normalize a term strongly. reaches under lambdas!
  const Value = new ADT({ Const: 1, Clo: 3, NVar: 1, NApp: 2 });
  function apply(vf, x) {
    return vf.match({
      Clo: (env, n, body) => body(put(env, n, x)),
      NVar: () => Value.NApp(vf, x),
      NApp: () => Value.NApp(vf, x),
      Const: (t) => {
        throw Error(`Cannot apply constant ${t} to a term`);
      },
    });
  }
  function readBack(used, value) {
    return value.match({
      Const: (v) => Lang.c(v),
      NVar: (n) => Lang.v(n),
      NApp: (f, x) => Lang.a(readBack(used, f), readBack(used, x)),
      Clo: (_env, n, _body) => {
        const n0 = freshen(used, n);
        return Lang.l(n0, readBack(used, apply(value, Value.NVar(n0))));
      }, // should apply a value at the bottom of the stack
    });
  }
  Lang.SimpS = {
    l: (n, t) => (env) => Value.Clo(env, n, t),
    a: (t1, t2) => (env) => apply(t1(env), t2(env)),
    v: (n) => (env) => env[n],
    c: (v) => (_) => Value.Const(v),
  };
  Lang.simp = function (term) {
    const value = term(this.SimpS)([]);
    return readBack({}, value);
  };

  // term a == a
  Lang.ShowS = {
    l: (n, t) => `(λ${n}. ${t})`,
    a: (t1, t2) => `(${t1} ${t2})`,
    v: (n) => `${n}`,
    c: (v) => `${v}`,
  };
  Lang.show = function (term) {
    return term(this.ShowS);
  };

  return Lang;
})();

const HigherToNamedS = {
  // (Int -> Named a) -> Int -> Named a
  l: (fn) => (level) =>
    Named.l(`x${level}`, fn((_) => Named.v(`x${level}`))(level + 1)),
  a: (e1, e2) => (level) => Named.a(e1(level), e2(level)),
  c: (v) => (_) => Named.c(v),
};

function HigherToNamed(term) {
  return term(HigherToNamedS)(0);
}

const NamedToHigherS = {
  l: (n, t) => (env) => Higher.l((x) => t(put(env, n, x))),
  a: (t1, t2) => (env) => Higher.a(t1(env), t2(env)),
  v: (n) => (env) => env[n],
  c: (v) => (_) => Higher.c(v),
};

function NamedToHigher(term) {
  return term(NamedToHigherS)({});
}

// Into ADT

const MatchS = {
  to: (a0, b0) => (S) => (mustHave(S, "to"), S.to(a0, b0)),
  t: (n0) => (S) => (mustHave(S, "t"), S.t(n0)),
};

// Appendix

function mustHave(obj, key) {
  if (!Object.hasOwn(obj, key))
    throw Error(`Tried to get key ${key} from Object ${obj}`);
}

function merge(...objs) {
  return objs.reduce((acc, obj) => Object.assign(acc, obj), {});
}

function dbg(...args) {
  console.log(...args);
  return args[args.length - 1];
}
