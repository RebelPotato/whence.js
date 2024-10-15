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

function mustHave(obj, key) {
  if (!Object.hasOwn(obj, key))
    throw Error(`Tried to get key ${key} from Object ${obj}`);
}

// operations on languages

function strip(Lang, term) {
  return term(Lang.Strip);
}

function show(Lang, term) {
  return term(Lang.Show)(0);
}


function simp(Lang, term) {
  const value = term(Lang.Simp)(new NamedEnv(), 0);
  return value.readBack({}, new NamedEnv());
}

class NamedEnv {
  constructor(env = {}) {
    this.env = env;
  }
  put(x, v) {
    const newEnv = { ...this.env };
    newEnv[x] = v;
    return new NamedEnv(newEnv);
  }
  get(x) {
    return this.env[x];
  }
}

// fn :: (repr a -> repr b) -> repr (a -> b)
// a :: repr (a -> b) -> repr a -> repr b
// c :: a -> repr a
const Core = (() => {
  const Lang = {};

  // repr a ==> S -> repr a
  // fn :: (S -> repr a) -> S -> repr b
  // a :: (S -> repr (a -> b)) -> (S -> repr a) -> S -> repr b
  // c :: a -> S -> repr a
  Lang.Self = {
    fn: (fn) => (S) => S.fn((x) => fn((_) => x)(S)), // tricky
    a: (t1, t2) => (S) => S.a(t1(S), t2(S)),
    c: (v) => (S) => S.c(v),
  };

  // repr a ==> a
  Lang.Strip = {
    fn: (fn) => fn,
    a: (t1, t2) => t1(t2),
    c: (v) => v,
  }

  // repr a ==> env -> repr a
  // fn :: (env -> repr a) -> env -> repr b
  // a :: (env -> repr (a -> b)) -> (env -> repr a) -> env -> repr b
  // c :: a -> env -> repr a
  Lang.Compile = (lang) => ({
    fn: (fn) => (env) => lang.fn((x) => fn((_) => x)(env)),
    a: (t1, t2) => (env) => lang.a(t1(env), t2(env)),
    c: (v) => (_) => lang.c(v),
  });
  // for a core term, term(Compile(lang)) == term(lang)

  // repr a ==> level -> string
  // fn :: (level -> string) -> level -> string
  // a :: (level -> string) -> (level -> string) -> level -> string
  // c :: a -> level -> string
  Lang.Show = {
    fn: (fn) => (level) => {
      const x = `x${level}`;
      return `(λ${x}. ${fn((_) => x)(level + 1)})`;
    },
    a: (t1, t2) => (level) => `(${t1(level)} ${t2(level)})`,
    c: (v) => (_) => `${v}`,
  };

  // tracing
  // returns a value object that remembers the term that produced it
  Lang.Trace = (lang) => ({

  })

  // normalization by evaluation

  // strong normalization
  function freshen(used, n) {
    while (Object.hasOwn(used, n)) n = n + "'";
    return n;
  }
  
  class SimpFn {
    constructor(n, body) {
      this.n = n;
      this.body = body;
    }
    app(arg) {
      return this.body(arg);
    }
    // readBack :: this a->b -> repr (a -> b)
    // this.app :: this a->b -> Simp a -> Simp b
    readBack(used, env) {
      const n0 = freshen(used, this.n);
      const newUsed = { ...used };
      newUsed[n0] = true;
      return Core.Self.fn((x) =>
        this.app(new SimpVar(n0)).readBack(newUsed, env.put(n0, x))
      );
    }
  }
  
  class SimpApp {
    constructor(t1, t2) {
      this.t1 = t1;
      this.t2 = t2;
    }
    app(arg) {
      return new SimpApp(this, arg);
    }
    readBack(used, env) {
      return Core.Self.a(
        this.t1.readBack(used, env),
        this.t2.readBack(used, env)
      );
    }
  }
  
  class SimpVar {
    constructor(n) {
      this.n = n;
    }
    app(arg) {
      return new SimpApp(this, arg);
    }
    readBack(_, env) {
      return env.get(this.n);
    }
  }
  
  class SimpConst {
    constructor(n) {
      this.n = n;
    }
    app(arg) {
      return new SimpApp(this, arg);
    }
    readBack(_u, _e) {
      return Core.Self.c(this.n);
    }
  }
  
  // SimpFn :: (Simp a -> Simp b) -> Simp (a -> b)
  // SimpTerm :: repr a -> Simp a
  // repr a ==> env -> Simp a
  // fn :: ((env -> Simp a) -> env -> Simp b) -> env -> Simp (a -> b)
  // a :: (env -> Simp (a -> b)) -> (env -> Simp a) -> env -> Simp b
  // this does not typecheck unless you know the type of env
  Lang.Simp = {
    fn: (fn) => (env, level) =>
      new SimpFn(level, (x) =>
        fn((env) => env.get(level))(env.put(level, x), level + 1)
      ),
    // env.get(level) must be Simp a, because env.put(x) put that value in
    a: (t1, t2) => (env, level) => t1(env, level).app(t2(env, level)),
    c: (v) => (_e, _l) => new SimpConst(v),
  };
  return Lang;
})();



// nl :: (name a, repr b) -> repr (a -> b)
// v :: name a -> repr a
// env.put :: env -> name a -> repr a -> env
// env.get :: env -> name a -> repr a
const LamNamed = (() => {
  const Lang = {};

  // repr a :: S -> repr a
  // nl :: (name a, S -> repr b) -> S -> repr (a -> b)
  // v :: name a -> S -> repr a
  Lang.Self = {
    nl: (n, t) => (S) => S.nl(n, t(S)),
    v: (n) => (S) => S.v(n),
  };

  // repr a :: env -> repr a
  // nl :: (name a, env -> repr b) -> env -> repr (a -> b)
  // v :: name a -> env -> repr a
  Lang.Compile = (lang) => ({
    nl: (n, t) => (env) => lang.fn((x) => t(env.put(n, x))),
    v: (n) => (env) => env.get(n),
  });

  // repr a :: level -> string
  Lang.Show = {
    nl: (n, t) => (_) => `(λ${n}. ${t})`,
    v: (n) => (_) => `${n}`,
  };

  return Lang;
})();

function combine(...langs) {
  const combined = {};
  combined.Self = merge(...langs.map((l) => l.Self));
  combined.Compile = (lang) => merge(...langs.map((l) => l.Compile(lang)));
  combined.Show = merge(...langs.map((l) => l.Show));
  return combined;
}
