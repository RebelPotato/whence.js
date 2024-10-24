function mkParser(Defs, tracing = 0) {
  function prune(arr, depth = 0) {
    if (Array.isArray(arr)) {
      if (depth > tracing) return "...";
      return arr.map((x) => prune(x, depth + 1));
    }
    return arr;
  }

  function memo(fn) {
    const store = {};
    return function (x) {
      if (store[x] === undefined) store[x] = fn(x);
      return store[x];
    };
  }

  // a result is one of {matched: str, rest: str, trace: [str]} | {error: str, rest: str, trace: [str]}
  function Success(matched, rest, trace) {
    const obj = { matched, rest, trace: prune(trace), failed: false };
    return Object.freeze(obj);
  }
  function Fail(rest, trace) {
    const obj = { rest, trace: prune(trace), failed: true };
    return Object.freeze(obj);
  }

  // utilities
  function trimShow(str, len = 10) {
    return str.length > len ? str.slice(0, len) + "..." : str;
  }

  const id = (x) => x;

  function literal(s, fn = id) {
    return memo((str) => {
      if (str.startsWith(s)) {
        return Success(fn(s), str.slice(s.length), [`literal ${s}`]);
      } else {
        return Fail(str, [
          `literal failed: Expected '${s}' but got '${trimShow(
            str,
            s.length
          )}'`,
        ]);
      }
    });
  }

  function regex(re, fn = id) {
    return memo((str) => {
      const match = str.match(re);
      if (match && match.index === 0) {
        return Success(fn(match[0]), str.slice(match[0].length), [
          `regex ${re} got ${match[0]}`,
        ]);
      } else {
        return Fail(str, [
          `regex failed: Expected '${re}' but got '${trimShow(str)}'`,
        ]);
      }
    });
  }

  function sequence(name, parsers, fn = id) {
    return memo((str) => {
      let rest = str;
      const matched = [];
      const trace = [];
      for (let i = 0; i < parsers.length; i++) {
        const res = parsers[i](rest);
        trace.push(res.trace);
        if (res.failed) {
          return Fail(str, [`${name} sequence failed`, ...trace]);
        }
        matched.push(res.matched);
        rest = res.rest;
      }
      return Success(fn(matched), rest, [name, ...trace]);
    });
  }

  function oneOf(name, parsers, fn = id) {
    return memo((str) => {
      const trace = [];
      for (let i = 0; i < parsers.length; i++) {
        const res = parsers[i](str);
        trace.push(res.trace);
        if (!res.failed) {
          return Success(fn(res.matched), res.rest, [name, ...trace]);
        }
      }
      return Fail(str, [`${name} oneOf failed`, trace]);
    });
  }

  function many(parser, fn = id) {
    return memo((str) => {
      let rest = str;
      const matched = [];
      const trace = ["many"];
      while (true) {
        const res = parser(rest);
        trace.push(res.trace);
        if (res.failed) {
          return Success(fn(matched), rest, trace);
        }
        matched.push(res.matched);
        rest = res.rest;
      }
    });
  }

  function maybe(parser, fn = id) {
    return memo((str) => {
      const res = parser(str);
      if (res.failed) {
        return Success(fn([]), str, ["maybe failed", res.trace]);
      } else {
        return Success(fn([res.matched]), res.rest, ["maybe", res.trace]);
      }
    });
  }

  function not(parser, fn = () => null) {
    return memo((str) => {
      const res = parser(str);
      if (res.failed) {
        return Success(fn(), str, ["not", res.trace]);
      } else {
        return Fail(str, ["not failed", res.trace]);
      }
    });
  }

  const intersperse = (inter, list) =>
    list.flatMap((p) => [inter, p]).concat([inter]);
  function whitespace(str, fn = id) {
    const match = str.match(/\s*/);
    if (match && match.index === 0) {
      return Success(fn(match[0]), str.slice(match[0].length), [`whitespace`]);
    } else {
      return Fail(str, [`whitespace: Got '${trimShow(str)}'`]);
    }
  }
  function wseq(name, parsers, fn = id) {
    return sequence(name, intersperse(whitespace, parsers), (args) =>
      fn(args.filter((_, i) => i % 2 === 1))
    );
  }

  // the actual parsing
  function theorem(str) {
    return wseq(
      "theorem",
      [
        many(wseq("ifs", [term, literal(",")], ([x, _]) => x)),
        maybe(term),
        regex(/⊢|\|-/),
        term,
      ],
      ([ifs, lastIf, _, then]) => ({
        op: "theorem",
        ifs: [...ifs, ...lastIf],
        then,
      })
    )(str);
  }

  function term(str) {
    return oneOf("term", [fn, pi, bin, eq, app, parens, def, variTyped, vari])(
      str
    );
  }
  function eqless(str) {
    return oneOf("eqless", [fn, pi, bin, app, parens, def, variTyped, vari])(
      str
    );
  }
  function binless(str) {
    return oneOf("binless", [fn, pi, app, parens, def, variTyped, vari])(str);
  }
  function appless(str) {
    return oneOf("appless", [fn, pi, parens, def, variTyped, vari])(str);
  }
  // todo: combine fn and pi to add room for forall, exists, etc.
  function fn(str) {
    return wseq(
      "fn",
      [regex(/λ|fn|lambda/), variTyped, literal("."), term],
      ([_, v, __, tm]) => ({
        op: "fn",
        vari: v,
        type: v.type,
        term: tm,
      })
    )(str);
  }
  function app(str) {
    return wseq(
      "app",
      [
        appless,
        appless,
        many(sequence("app2+", [appless, whitespace], ([x, _]) => x)),
      ],
      ([x, arg, args]) => ({
        op: "app",
        x,
        args: [arg, ...args],
      })
    )(str);
  }
  function eq(str) {
    return wseq("eq", [eqless, literal("="), eqless], ([lhs, _, rhs]) => ({
      op: "eq",
      lhs,
      rhs,
    }))(str);
  }
  function vari(str) {
    return sequence(
      "vari",
      [not(reserved), regex(/[a-zA-Z\_][a-zA-Z0-9\_]*/)],
      ([_, x]) => ({
        op: "vari",
        name: x,
      })
    )(str);
  }
  function variTyped(str) {
    return wseq("variTyped", [vari, literal(":"), eqless], ([v, _, ty]) => ({
      op: "vari",
      name: v.name,
      type: ty,
    }))(str);
  }
  function parens(str) {
    return wseq(
      "parens",
      [literal("("), term, literal(")")],
      ([_, x, __]) => x
    )(str);
  }
  function pi(str) {
    return wseq(
      "pi",
      [regex(/Π|Pi/), variTyped, literal("."), term],
      ([_, v, __, tm]) => ({
        op: "pi",
        vari: v,
        type: v.type,
        term: tm,
      })
    )(str);
  }

  function mkBinOp(name, alias) {
    return wseq(name, [binless, literal(alias), binless], ([lhs, _, rhs]) => ({
      op: "bin",
      name,
      lhs,
      rhs,
    }));
  }
  const binParsers = [];
  const binNames = [];
  const constNames = [];
  for (const c of ["Bool", "Type"]) {
    constNames.push(literal(c, (_) => ({ op: "const", name: c })));
  }
  for (const d of Object.keys(Defs)) {
    const names = [d, ...Object.values(Defs[d].alias)];
    if (Defs[d].binop)
      for (const name of names) {
        binParsers.push(mkBinOp(d, name));
        constNames.push(
          literal(`(${name})`, (_) => ({ op: "const", name: d }))
        );
        binNames.push(literal(name));
      }
    else
      for (const name of names)
        constNames.push(literal(name, (_) => ({ op: "const", name: d })));
  }
  const def = oneOf("def", constNames);
  const bin = oneOf("bin", binParsers);
  const reserved = oneOf("reserved", [regex(/λ|fn|lambda|Π|Pi/), def, oneOf("binNames", binNames)]);

  return theorem;
}

function fromJSON(obj, Defs, env) {
  switch (obj.op) {
    case "const": {
      if (obj.name === "Bool") return Kernel.Bool;
      if (obj.name === "Type") return Kernel.Type;
      if (Defs[obj.name] === undefined)
        throw Error(`const ${obj.name} not found`);
      throw Error(`creating const ${obj.name} not implemented`);
    }
    case "vari": {
      if (env[obj.name] === undefined) {
        if (obj.type === undefined)
          throw Error(`variable ${obj.name} not found`);
        env[obj.name] = { type: fromJSON(obj.type, Defs, env) };
      } else if (env[obj.name].vari !== undefined) return env[obj.name].vari;

      const type = env[obj.name].type;
      const v = Kernel.vari(type, obj.name);
      env[obj.name].vari = v;
      return v;
    }
    case "fn": {
      if(obj.type === undefined) throw Error("fn type not found");
      const v = fromJSON(obj.vari, Defs, env);
      const bTerm = fromJSON(obj.term, Defs, env);
      const body = bTerm.hollow(v).orElse(() => (_) => bTerm);
      return Kernel.fn(v.type, body);
    }
    case "pi": {
      if(obj.type === undefined) throw Error("fn type not found");
      const v = fromJSON(obj.vari, Defs, env);
      const bTerm = fromJSON(obj.term, Defs, env);
      const body = bTerm.hollow(v).orElse(() => (_) => bTerm);
      return Kernel.pi(v.type, body);
    }
    case "app": {
      const isConst = obj.x.op === "const";
      let res = fromJSON(obj.x, Defs, env);
      for (const arg of obj.args) {
        const aterm = fromJSON(arg, Defs, env);
        if(isConst) res = res.app(aterm);
        else res = Kernel.app(res, aterm);
      }
      return res;
    }
    case "eq":
      return Kernel.eq(
        fromJSON(obj.lhs, Defs, env),
        fromJSON(obj.rhs, Defs, env)
      );
    case "bin": {
      if (obj.name == "→") return Kernel.Arr(fromJSON(obj.lhs, Defs, env), fromJSON(obj.rhs, Defs, env));
      if (Defs[obj.name] === undefined)
        throw Error(`binary operation ${obj.name} not found`);
      const bin = Defs[obj.name].term;
      const lhs = fromJSON(obj.lhs, Defs, env);
      const rhs = fromJSON(obj.rhs, Defs, env);
      return bin.app(lhs).app(rhs);
    }
    case "theorem": {
      throw Error(
        "theorem not implemented. Perhaps creating theorems from JSON should be banned?"
      );
    }
    default:
      throw Error(`unknown op ${obj.op}`);
  }
}
