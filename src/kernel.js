class ShowEnv {
  constructor() {
    this.env = new Map();
    this.counter = -1;
  }
  get(x) {
    if (!this.env.has(x)) {
      this.counter++;
      this.env.set(x, this.counter);
      return this.counter;
    }
    return this.env.get(x);
  }
}

class UnifyEnv {
  constructor() {
    this.env = new Map();
  }
  walk(x) {
    if (!this.env.has(x)) return x;
    const y = this.env.get(x);
    const z = this.walk(y);
    this.env.set(x, z);
    return z;
  }
  set(x, y) {
    this.env.set(this.walk(x), this.walk(y));
    return this;
  }
}


function fail(msg) {
  throw Error(msg);
}

const Kernel = (() => {
  // ------------------------------------------------------------
  // Types
  // ------------------------------------------------------------

  const Bool = {
    match: (cases) => {
      if (Object.hasOwn(cases, "Bool")) return cases.Bool();
      return cases._(Bool);
    },
    eq(other) {
      return other === Bool;
    },
    show: (env = new ShowEnv()) => "Bool",
    unify: (t, env) => {
      const t0 = env.walk(t);
      return t0.match({
        Tvar: () => env.set(t0, Bool),
        Bool: () => env,
        _: () => fail(`Type mismatch: ${t0.show()} is not Bool`),
      });
    },
    replace: (_) => Bool,
  };

  function Arr(l, r) {
    const obj = {
      match: (cases) => {
        if (Object.hasOwn(cases, "Arr")) return cases.Arr(l, r);
        return cases._(obj);
      },
      eq: (other) =>
        other.match({
          Arr: (l2, r2) => l.eq(l2) && r.eq(r2),
          _: () => false,
        }),
      show: (env = new ShowEnv()) => `(${l.show(env)} -> ${r.show(env)})`,
      unify: (t, env) => {
        const t0 = env.walk(t);
        return t0.match({
          Tvar: () => env.set(t0, obj),
          Arr: (l2, r2) => {
            env = l.unify(l2, env);
            env = r.unify(r2, env);
            return env;
          },
          _: () => fail(`Type mismatch: ${t0.show()} is not ${obj.show()}`),
        });
      },
      replace: (env) => Arr(l.replace(env), r.replace(env)),
    };
    return Object.freeze(obj);
  }

  function Tvar(name = "T") {
    const obj = {
      match: (cases) => {
        if (Object.hasOwn(cases, "Tvar")) return cases.Tvar(name);
        return cases._(obj);
      },
      eq: (other) => other === obj,
      show: (env = new ShowEnv()) => `${name}${env.get(obj)}`,
      unify: (t, env) => {
        const t0 = env.walk(t);
        if (t0.eq(t)) return env;
        return env.set(obj, t0);
      },
      replace: (env) => env.walk(obj),
    };
    return Object.freeze(obj);
  }

  // ------------------------------------------------------------
  // Terms
  // match, type, eq, show, has, replace
  // ------------------------------------------------------------

  function eqOrThrow(t1, t2, errorFn) {
    if (!t1.eq(t2)) {
      throw Error(errorFn());
    }
  }

  function vari(type, name = "x") {
    const obj = {
      match: (cases) => {
        if (Object.hasOwn(cases, "vari")) return cases.vari(type, name);
        return cases._(obj);
      },
      type,
      eq: (other) => other === obj,
      show: (env = new ShowEnv()) => `${name}${env.get(obj)}`,
      has: (x) => obj.eq(x),
      replace: (x, y) => {
        if (obj.eq(x)) {
          eqOrThrow(
            obj.type,
            y.type,
            () =>
              `Type mismatch: cannot replace ${obj.show()} :: ${obj.type.show()} with ${y.show()} :: ${y.type.show()}`
          );
          return y;
        }
        return obj;
      },
    };
    return Object.freeze(obj);
  }

  // use a function as the body to avoid alpha conversions
  function fn(ptype, body) {
    const ret = body(vari(ptype)).type;
    const type = Arr(ptype, ret);
    const obj = {
      match: (cases) => {
        if (Object.hasOwn(cases, "fn")) return cases.fn(ptype, body);
        return cases._(obj);
      },
      type,
      eq: (other) =>
        other.match({
          fn: (otherType, otherBody) => {
            const x = vari(ptype);
            return ptype.eq(otherType) && body(x).eq(otherBody(x));
          },
          _: () => false,
        }),
      show: (env = new ShowEnv()) => {
        const x = vari(ptype);
        env.get(x);
        const ret = `(λ${x.show(env)}. ${body(x).show(env)})`;
        return ret;
      },
      has: (x) => body(vari(ptype)).has(x),
      replace: (x, y) =>
        fn(ptype, (z) => {
          const tmp = vari(ptype);
          return body(tmp).replace(x, y).replace(tmp, z); // tmp is introduced in case z = x
        }),
    };
    return Object.freeze(obj);
  }

  function app(op, arg) {
    const opType = op.type;
    const argType = arg.type;
    const type = opType.match({
      Arr: (l, r) => r.replace(l.unify(argType, new UnifyEnv())),
      _: () => {
        throw Error(
          `Type mismatch: tried to apply non-function ${op.show()} :: ${opType.show()} to an argument`
        );
      },
    });

    const obj = {
      match: (cases) => {
        if (Object.hasOwn(cases, "app")) return cases.app(op, arg);
        return cases._(obj);
      },
      type,
      eq: (other) =>
        other.match({
          app: (otherOp, otherArg) => op.eq(otherOp) && arg.eq(otherArg),
          _: () => false,
        }),
      show: (env = new ShowEnv()) => `(${op.show(env)} ${arg.show(env)})`,
      has: (x) => op.has(x) || arg.has(x),
      replace: (x, y) => app(op.replace(x, y), arg.replace(x, y)),
    };
    return Object.freeze(obj);
  }

  function eq(lhs, rhs) {
    const type1 = lhs.type;
    const type2 = rhs.type;
    eqOrThrow(
      type1,
      type2,
      () =>
        `Type mismatch: cannot construct ${lhs.show()} :: ${type1.show()} = ${rhs.show()} :: ${type2.show()}`
    );
    const type = Bool;
    const obj = {
      match: (cases) => {
        if (Object.hasOwn(cases, "eq")) return cases.eq(lhs, rhs);
        return cases._(obj);
      },
      type,
      eq: (other) =>
        other.match({
          eq: (otherT1, otherT2) => lhs.eq(otherT1) && rhs.eq(otherT2),
          _: () => false,
        }),
      show: (env = new ShowEnv()) => `(${lhs.show(env)} = ${rhs.show(env)})`,
      has: (x) => lhs.has(x) || rhs.has(x),
      replace: (x, y) => eq(lhs.replace(x, y), rhs.replace(x, y)),
    };
    return Object.freeze(obj);
  }

  // ------------------------------------------------------------
  // Theorems and Rules
  // ------------------------------------------------------------

  // a theorem is a sequent, a list of conditions and a conclusion
  // this is never exported!
  function Sequent(ifs, then) {
    for (const t of ifs) {
      eqOrThrow(
        t.type,
        Bool,
        () => `Type mismatch: ${t.show()} :: ${t.type.show()} is not a boolean`
      );
    }
    eqOrThrow(
      then.type,
      Bool,
      () =>
        `Type mismatch: ${then.show()} :: ${then.type.show()} is not a boolean`
    );

    const obj = {
      ifs,
      then,
      match: (cases) => {
        if (Object.hasOwn(cases, "Sequent")) return cases.Sequent(ifs, then);
        return cases._(obj);
      },
      eq: (other) =>
        other.match({
          Sequent: (otherThen, otherIfs) =>
            then.eq(otherThen) &&
            ifs.length == otherIfs.length &&
            ifs.every((t, i) => t.eq(otherIfs[i])),
          _: () => false,
        }),
      show: (env = new ShowEnv()) =>
        `${ifs.map((x) => x.show(env)).join(", ")} ⊢ ${then.show(env)}`,
      replace: (x, y) =>
        Sequent(
          ifs.map((t) => t.replace(x, y)),
          then.replace(x, y)
        ),
    };
    return Object.freeze(obj);
  }

  function REFL(term) {
    return Sequent([], eq(term, term));
  }

  function TRANS(aIsb, bIsc) {
    const ifs1 = aIsb.ifs;
    const ifs2 = bIsc.ifs;
    const [a, b0] = deEq(aIsb.then);
    const [b1, c] = deEq(bIsc.then);

    eqOrThrow(
      b0,
      b1,
      () =>
        `Term mismatch: ${b0.show()} :: ${b0.type.show()} and ${b1.show()} :: ${b1.type.show()} are not equal`
    );

    const then = eq(a, c);
    const ifs = merge(ifs1, ifs2);
    return Sequent(ifs, then);
  }

  function EAPP(opThm, argThm) {
    const [a, b] = deEq(opThm.then);
    const [c, d] = deEq(argThm.then);
    return Sequent(merge(opThm.ifs, argThm.ifs), eq(app(a, c), app(b, d)));
  }

  function ABS(v, thm) {
    const [a, b] = deEq(thm.then);

    for (const t of thm.ifs) {
      if (t.has(v))
        throw Error(
          `Free variable: variiable ${v.show()} is free in condition ${t.show()}`
        );
    }

    // replace all occurences of v in t with x

    const then = eq(
      fn(v.type, (x) => a.replace(v, x)),
      fn(v.type, (x) => b.replace(v, x))
    );
    return Sequent(remove(thm.ifs, v), then);
  }

  function APP(op, arg) {
    const lhs = app(op, arg);
    const [_, body] = de("fn", op);
    return Sequent([], eq(lhs, body(arg)));
  }

  function ASSUME(term) {
    return Sequent([term], term);
  }

  function EMP(pqThm, pThm) {
    const p = pThm.then;
    const [p0, q] = deEq(pqThm.then);
    eqOrThrow(
      p,
      p0,
      () =>
        `Term mismatch: ${p.show()} :: ${p.type.show()} and ${p0.show()} :: ${p0.type.show()} are not equal`
    );
    return Sequent(merge(pThm.ifs, pqThm.ifs), q);
  }

  function DEDUCT(aThm, bThm) {
    const a = aThm.then;
    const b = bThm.then;
    return Sequent(merge(remove(bThm.ifs, a), remove(aThm.ifs, b)), eq(a, b));
  }

  function EQ_DEF(lhs, rhs) {
    const eqFn = fn(lhs.type, (x) => fn(rhs.type, (y) => eq(x, y)));
    return Sequent([], eq(eq(lhs, rhs), app(app(eqFn, lhs), rhs)));
  }

  // ------------------------------------------------------------
  // Creating new constants, terms and operators
  // ------------------------------------------------------------

  function mkConst(name, term, attrs = {}) {
    const obj = {
      match: (cases) => {
        if (Object.hasOwn(cases, name)) return cases[name]();
        return cases._(obj);
      },
      type: term.type,
      eq: (other) => other === obj,
      has: (other) => obj.eq(other),
      replace: (x, y) => (obj.eq(x) ? y : obj),
      show: () => name,
    };
    for (const k of Object.keys(attrs)) {
      obj[k] = attrs[k];
    }
    const DEF = Sequent([], eq(obj, term));
    return [Object.freeze(obj), DEF];
  }

  function mkOp(name, arity, term, attrGen = () => ({})) {
    function gen(...args) {
      if (args.length != arity) {
        throw Error(`Arity mismatch: ${name} expects ${arity} arguments`);
      }
      let rhs = term;
      for (const arg of args) {
        rhs = app(rhs, arg);
      }
      const attrs = attrGen(...args);
      const obj = {
        match: (cases) => {
          if (Object.hasOwn(cases, name)) return cases[name](...args);
          return cases._(obj);
        },
        type: rhs.type,
        eq: (other) =>
          other.match({
            [name]: (...otherArgs) => args.every((x, i) => x.eq(otherArgs[i])),
            _: () => false,
          }),
        has: (other) => obj.eq(other) || args.some((x) => x.has(other)),
        replace: (x, y) => (obj.eq(x) ? y : obj),
        show: (env = new ShowEnv()) =>
          `(${name} ${args.map((x) => x.show(env)).join(" ")})`,
      };
      for (const k of Object.keys(attrs)) {
        obj[k] = attrs[k];
      }
      return Object.freeze(obj);
    }
    function APP(...args) {
      if (args.length != arity) {
        throw Error(`Arity mismatch: ${name} expects ${arity} arguments`);
      }
      const lhs = gen(...args);
      let rhs = term;
      for (const arg of args) {
        rhs = app(rhs, arg);
      }
      return Sequent([], eq(lhs, rhs));
    }
    return [gen, APP];
  }

  function mkBinOp(name, term, attrGen = () => ({})) {
    return mkOp(name, 2, term, (t1, t2) => ({
      ...attrGen(t1, t2),
      show: (env = new ShowEnv()) =>
        `(${t1.show(env)} ${name} ${t2.show(env)})`,
    }));
  }

  // ------------------------------------------------------------
  // Utils
  // ------------------------------------------------------------

  // check if a list of terms contains a term
  function contains(ifs, t) {
    return ifs.some((u) => u.eq(t));
  }

  // merge two lists of terms
  function merge(ifs1, ifs2) {
    const newIfs = [...ifs1];
    for (const t of ifs2) {
      if (!contains(newIfs, t)) newIfs.push(t);
    }
    return newIfs;
  }

  // remove a term from a list of terms
  function remove(ifs, t) {
    return ifs.filter((u) => !u.eq(t));
  }

  // destructure an equality term
  function de(name, t) {
    return t.match({
      [name]: (...args) => [...args],
      _: () => {
        throw Error(`Not ${name}: ${t.show()} :: ${t.type.show()}`);
      },
    });
  }

  function deEq(t) {
    return de("eq", t);
  }

  return {
    // types
    Bool,
    Arr,
    Tvar,
    // terms
    vari,
    fn,
    app,
    eq,
    // rules
    REFL,
    TRANS,
    EAPP,
    ABS,
    APP,
    ASSUME,
    EMP,
    DEDUCT,
    EQ_DEF,
    // new constants, terms and operators
    mkConst,
    mkOp,
    mkBinOp,
    // utils
    de,
  };
})();
