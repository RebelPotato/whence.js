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

const bit256 = (1n << 256n) - 1n;
// hex string representation of a BigInt with 256 bits
const toHex = (x) => x.toString(16).padStart(64, "0");

// sdbm hash function with 256 bits
const sdbm = (str, initial = BigInt(0)) => {
  const arr = str.split("");
  let hashCode = initial;
  for (let i = 0; i < arr.length; i++) {
    hashCode =
      BigInt(arr[i].charCodeAt(0)) +
      (hashCode << 6n) +
      (hashCode << 16n) -
      hashCode;
    // get last 256 bits
    hashCode = hashCode & bit256;
  }
  return hashCode;
};

const combine = (...hashes) => {
  let result = BigInt(0);
  for (const hash of hashes) {
    result = sdbm(toHex(hash), result);
  }
  return result;
};

function fail(msg) {
  throw Error(msg);
}

function matchOr(name, args, self) {
  return (cases) => {
    if (Object.hasOwn(cases, name)) return cases[name](...args);
    return cases._(self());
  };
}

function once(fn) {
  let done = false;
  let result = null;
  return function (...args) {
    if (!done) {
      result = fn(...args);
      done = true;
    }
    return result;
  };
}

const Maybe = {
  Just: (value) => ({
    match: (cases) => cases.Just(value),
    map: (fn) => Maybe.Just(fn(value)),
    app: (x) => x.map(value),
    pipe: (fn) => fn(value),
    orElse: (_) => value,
    orThrow: (_) => value,
    isNothing: false,
  }),
  Nothing: {
    match: (cases) => cases.Nothing(),
    map: (_) => Maybe.Nothing,
    app: (_) => Maybe.Nothing,
    pipe: (_) => Maybe.Nothing,
    orElse: (fn) => fn(),
    orThrow: (msg = "Nothing") => {
      throw new Error(msg);
    },
    isNothing: true,
  },
};

const Either = {
  Left: (value) => ({
    match: (cases) => cases.Left(value),
    map: (_) => Either.Left(value),
    orMap: (fn) => Either.Left(fn(value)),
    app: (_) => Either.Left(value),
    pipe: (_) => Either.Left(value),
    unwrap: (_) => value,
    orThrow: () => {
      throw new Error(value);
    },
  }),
  Right: (value) => ({
    match: (cases) => cases.Right(value),
    map: (fn) => Either.Right(fn(value)),
    orMap: (_) => Either.Right(value),
    app: (x) => x.map(value),
    pipe: (fn) => fn(value),
    unwrap: (_) => value,
    orThrow: () => value,
  }),
  collect(eithers) {
    const acc = [];
    for (const e of eithers) {
      e.match({
        Right: (x) => acc.push(x),
        Left: () => {
          return e;
        },
      });
    }
    return Either.Right(acc);
  },
};

// options for the kernel
const Kernel = KernelGen({
  termToType: false, // dependent types
  typeToType: false, // type operators
  typeToTerm: true, // universal types
});

function KernelGen({ termToType, typeToType, typeToTerm }) {
  // ------------------------------------------------------------
  // Kinds
  // ------------------------------------------------------------

  const Wat = {
    match: matchOr("Wat", [], () => Wat),
    // type: Type is set later
    eq: (other) => other === Wat,
    hollow: (_) => Maybe.Just((_) => Wat),
    show: () => "Wat",
    hash: () => sdbm("Wat"),
  };

  const Type = {
    match: matchOr("Type", [], () => Type),
    type: Wat,
    eq: (other) => other === Type,
    hollow: (_) => Maybe.Just((_) => Type),
    show: () => "Type",
    hash: () => sdbm("Type"),
  };
  Wat.type = Type;

  const isType = (x) => x.type.type.eq(Wat);
  const isTerm = (x) => x.type.type.eq(Type);

  // ------------------------------------------------------------
  // Types
  // ------------------------------------------------------------

  const Bool = {
    match: matchOr("Bool", [], () => Bool),
    type: Type,
    eq: (other) => other === Bool,
    hollow: (_v) => Maybe.Just((_) => Bool),
    show: () => "Bool",
    hash: () => sdbm("Bool"),
  };

  // hollow turns a type into Maybe (Var -> Term), allowing swaping one variable for another
  function hollow2(l, r, comb) {
    return (v) => {
      const newl = l.hollow(v);
      const newr = r.hollow(v);
      if (newl.isNothing && newr.isNothing) return Maybe.Nothing;
      const lFn = newl.orElse(() => (_) => l);
      const rFn = newr.orElse(() => (_) => r);
      return Maybe.Just((v0) => comb(lFn(v0), rFn(v0)));
    };
  }

  function Pi(ptype, body) {
    if (!ptype.eq(Type) && isTerm(ptype))
      // ptype is the type of the input variable, which must be a type
      fail(
        `Pi: type mismatch, ${ptype.show()} :: ${ptype.type.show()} should be a type`
      );
    const Tmp = vari(ptype);
    const ret = body(Tmp);
    const inputKind = ptype.type;
    const outputKind = ret.type;

    if (inputKind.eq(Type) && outputKind.eq(Wat) && !termToType)
      fail(
        `Pi: this kernel cannot build a function from term :: ${ptype.show()} to type :: ${ret.show()}`
      );
    if (inputKind.eq(Wat) && outputKind.eq(Wat) && !typeToType)
      fail(
        `Pi: this kernel cannot build a function from type :: ${ptype.show()} to type :: ${ret.show()}`
      );
    if (inputKind.eq(Wat) && outputKind.eq(Type) && !typeToTerm)
      fail(
        `Pi: this kernel cannot build a function from type :: ${ptype.show()} to term :: ${ret.show()}`
      );
    
    const hasTmp = ret.hollow(Tmp).isNothing;

    // when inputKind = Type and outputKind = Type, this is just the arrow type
    const obj = {
      match: matchOr("Pi", [ptype, body], () => obj),
      type: Type,
      eq: (other) =>
        other.match({
          Pi: (otherPtype, otherBody) => {
            if (!ptype.eq(otherPtype)) return false;
            const T = vari(ptype);
            return body(T).eq(otherBody(T));
          },
          _: () => false,
        }),
      hollow: (v) => {
        const T = vari(ptype);
        return hollow2(ptype, body(T), (p, b) => Pi(p, (x) => b.hollow(T)(x)))(
          v
        );
      },
      show: (env = new ShowEnv()) => {
        if(hasTmp) {
          const T = vari(ptype);
          env.get(T);
          return `(Π${T.show(env)} :: ${ptype.show(env)}. ${body(T).show(env)})`;
        }
        return `(${ptype.show(env)} -> ${ret.show(env)})`;
      },
      hash: (env = new ShowEnv()) => {
        const T = vari(ptype);
        env.get(T);
        return combine(sdbm("Pi"), T.hash(env), body(T).hash(env));
      },
      app: (arg) => {
        if (!ptype.eq(arg.type))
          fail(
            `Pi: type mismatch, tried to apply ${arg.show()} :: ${arg.type.show()} to ${obj.show()}`
          );
        return body(arg);
      },
    };
    return Object.freeze(obj);
  }

  // an arrow is an alias for a pi type with no free variables inside.
  function Arr(l, r) {
    return Pi(l, () => r);
  }

  // ------------------------------------------------------------
  // Terms
  // match, type, eq, show, has, reType, replace, hash
  // ------------------------------------------------------------

  function eqOrThrow(t1, t2, errorFn) {
    if (!t1.eq(t2)) fail(errorFn());
  }

  function vari(type, name = "x") {
    const obj = {
      match: matchOr("vari", [type, name], () => obj),
      type,
      eq: (other) => other === obj,
      show: (env = new ShowEnv()) => `${name}${env.get(obj)}`,
      hollow: (v) => (v === obj ? Maybe.Just((v0) => v0) : Maybe.Nothing),
      hash: (env = new ShowEnv()) =>
        combine(sdbm("vari"), type.hash(env), sdbm(`${name}${env.get(obj)}`)),
    };
    return Object.freeze(obj);
  }

  // use a function as the body to avoid alpha conversions
  function fn(ptype, body) {
    const type = Pi(ptype, (x) => body(x).type); // naive type inference?
    const obj = {
      match: matchOr("fn", [ptype, body], () => obj),
      type,
      eq: (other) =>
        other.match({
          fn: (otherType, otherBody) => {
            if (!ptype.eq(otherType)) return false;
            const x = vari(ptype);
            return body(x).eq(otherBody(x));
          },
          _: () => false,
        }),
      show: (env = new ShowEnv()) => {
        const x = vari(ptype);
        env.get(x);
        return `(λ${x.show(env)} :: ${ptype.show(env)}. ${body(x).show(env)})`;
      },
      hollow: (v) => {
        const x = vari(ptype);
        return hollow2(ptype, body(x), (p, b) =>
          fn(p, (x0) => b.hollow(x)(x0))
        )(v);
      },
      hash: (env = new ShowEnv()) => {
        const x = vari(ptype);
        env.get(x);
        return combine(sdbm("fn"), x.hash(env), body(x).hash(env));
      },
      app: (arg) => {
        if (!ptype.eq(arg.type))
          fail(
            `fn: type mismatch, tried to apply ${arg.show()} :: ${arg.type.show()} but expected ${ptype.show()}`
          );
        return body(arg);
      },
    };
    return Object.freeze(obj);
  }

  function app(op, arg) {
    const opType = op.type;
    const type = opType.match({
      Pi: () => opType.app(arg),
      _: () =>
        fail(
          `app: type mismatch, tried to apply non-function ${op.show()} :: ${opType.show()}`
        ),
    });

    const obj = {
      match: matchOr("app", [op, arg], () => obj),
      type,
      eq: (other) =>
        other.match({
          app: (otherOp, otherArg) => op.eq(otherOp) && arg.eq(otherArg),
          _: () => false,
        }),
      show: (env = new ShowEnv()) => `(${op.show(env)} ${arg.show(env)})`,
      hollow: hollow2(op, arg, app),
      hash: (env = new ShowEnv()) =>
        combine(sdbm("app"), op.hash(env), arg.hash(env)),
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
        `eq: type mismatch, ${lhs.show()} :: ${type1.show()} and ${rhs.show()} :: ${type2.show()} are not of equal types`
    );

    const type = Bool;
    const obj = {
      match: matchOr("eq", [lhs, rhs], () => obj),
      type,
      eq: (other) =>
        other.match({
          eq: (otherT1, otherT2) => lhs.eq(otherT1) && rhs.eq(otherT2),
          _: () => false,
        }),
      show: (env = new ShowEnv()) => `(${lhs.show(env)} = ${rhs.show(env)})`,
      hollow: hollow2(lhs, rhs, eq),
      hash: (env = new ShowEnv()) =>
        combine(sdbm("="), lhs.hash(env), rhs.hash(env)),
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
        () =>
          `⊢: type mismatch, ${t.show()} :: ${t.type.show()} is not a boolean`
      );
    }
    eqOrThrow(
      then.type,
      Bool,
      () =>
        `⊢: type mismatch: ${then.show()} :: ${then.type.show()} is not a boolean`
    );

    const obj = {
      ifs,
      then,
      match: matchOr("Sequent", [ifs, then], () => obj),
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
          ifs.map((t) => t.hollow(x).orElse(() => (_) => t)(y)),
          then.hollow(x).orElse(() => (_) => then)(y)
        ),
      hash: (env = new ShowEnv()) =>
        combine(sdbm("⊢"), then.hash(env), ...ifs.map((t) => t.hash(env))),
    };
    return Object.freeze(obj);
  }

  // t  /  |- t = t
  function REFL(term) {
    return Sequent([], eq(term, term));
  }

  // M |- a = b,   N |- b = c   /   M union N |- a = c
  function TRANS(aIsb, bIsc) {
    const ifs1 = aIsb.ifs;
    const ifs2 = bIsc.ifs;
    const [a, b0] = deEq(aIsb.then);
    const [b1, c] = deEq(bIsc.then);

    eqOrThrow(
      b0,
      b1,
      () =>
        `TRANS: term mismatch, ${b0.show()} :: ${b0.type.show()} and ${b1.show()} :: ${b1.type.show()} are not equal`
    );

    const then = eq(a, c);
    const ifs = merge(ifs1, ifs2);
    return Sequent(ifs, then);
  }

  // M |- a = b,   N |- c = d   /   M union N |- a c = b d
  function EAPP(opThm, argThm) {
    const [a, b] = deEq(opThm.then);
    const [c, d] = deEq(argThm.then);
    return Sequent(merge(opThm.ifs, argThm.ifs), eq(app(a, c), app(b, d)));
  }

  // M |- a = b   /   M\x |- (λx. a) = (λx. b)
  function ABS(v, thm) {
    const [a, b] = deEq(thm.then);

    for (const t of thm.ifs)
      if (!t.hollow(v).isNothing)
        fail(
          `ABS: free variable, variable ${v.show()} is free in condition ${t.show()}`
        );

    // replace all occurences of v in a, b with x
    const aFn = a.hollow(v).orElse(() => (_) => a);
    const bFn = b.hollow(v).orElse(() => (_) => b);
    const then = eq(fn(v.type, aFn), fn(v.type, bFn));
    return Sequent(remove(thm.ifs, v), then);
  }

  // (op arg) reduces one step to v   /   |- op arg = v
  function APP(op, arg) {
    return Sequent([], eq(app(op, arg), op.app(arg)));
  }

  // a  /  a |- a
  function ASSUME(term) {
    return Sequent([term], term);
  }

  // M |- p,   N |- p = q   /   M union N |- q
  function EMP(pqThm, pThm) {
    const p = pThm.then;
    const [p0, q] = deEq(pqThm.then);
    eqOrThrow(
      p,
      p0,
      () =>
        `EMP: term mismatch, ${p.show()} :: ${p.type.show()} and ${p0.show()} :: ${p0.type.show()} are not equal`
    );
    return Sequent(merge(pThm.ifs, pqThm.ifs), q);
  }

  // b, M |- a,   a, N |- b   /   M\b union N\a |- a = b
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

  function mkOp(name, arity, term, attrGen = () => ({})) {
    function gen(...args) {
      if (args.length != arity)
        fail(`${name}: arity mismatch, ${name} expects ${arity} arguments`);
      let rhs = term;
      for (const arg of args) {
        rhs = app(rhs, arg);
      }
      const attrs = attrGen(...args);
      const obj = {
        match: matchOr(name, args, () => obj),
        type: rhs.type,
        eq: (other) =>
          other.match({
            [name]: (...otherArgs) => args.every((x, i) => x.eq(otherArgs[i])),
            _: () => false,
          }),
        hollow: (v) => {
          const newArgs = args.map((x) => x.hollow(v).orElse(() => (_) => x));
          if (newArgs.some((x) => x.isNothing)) return Maybe.Nothing;
          return Maybe.Just((v0) => gen(...newArgs.map((x) => x(v0)))); // assume term has no variables
        },
        show: (env = new ShowEnv()) =>
          `(${name} ${args.map((x) => x.show(env)).join(" ")})`,
        hash: (env = new ShowEnv()) =>
          combine(sdbm(name), ...args.map((x) => x.hash(env))),
      };
      for (const k of Object.keys(attrs)) {
        obj[k] = attrs[k];
      }
      return Object.freeze(obj);
    }
    function DEF(...args) {
      if (args.length != arity)
        fail(`${name}: arity mismatch: ${name} expects ${arity} arguments`);

      const lhs = gen(...args);
      let rhs = term;
      for (const arg of args) {
        rhs = app(rhs, arg);
      }
      return Sequent([], eq(lhs, rhs));
    }
    return [gen, DEF];
  }

  function mkConst(name, term, attrs = {}) {
    const [g, d] = mkOp(name, 0, term, () => ({
      show: () => name,
      ...attrs,
    }));
    return [g(), d()];
  }

  function mkBinOp(name, term, attrGen = () => ({})) {
    return mkOp(name, 2, term, (t1, t2) => ({
      show: (env = new ShowEnv()) =>
        `(${t1.show(env)} ${name} ${t2.show(env)})`,
      ...attrGen(t1, t2),
    }));
  }

  // ------------------------------------------------------------
  // Utils
  // ------------------------------------------------------------

  // merge two lists of terms, sorted according to hash
  function merge(ifs1, ifs2) {
    const newIfs = [];
    let i = 0;
    let j = 0;
    while (i < ifs1.length && j < ifs2.length) {
      const h1 = ifs1[i].hash();
      const h2 = ifs2[j].hash();
      if (h1 < h2) {
        newIfs.push(ifs1[i]);
        i++;
      } else if (h1 > h2) {
        newIfs.push(ifs2[j]);
        j++;
      } else {
        newIfs.push(ifs1[i]);
        i++;
        j++;
      }
    }
    while (i < ifs1.length) {
      newIfs.push(ifs1[i]);
      i++;
    }
    while (j < ifs2.length) {
      newIfs.push(ifs2[j]);
      j++;
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
      _: () => fail(`Not ${name}: ${t.show()} :: ${t.type.show()}`),
    });
  }

  function deEq(t) {
    return de("eq", t);
  }

  return {
    // kinds
    Type,
    // types
    Bool,
    Pi,
    Arr,
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
}
