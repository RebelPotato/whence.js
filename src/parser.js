function mkParser(Defs, tracing = 0) {
  function prune(arr, depth = 0) {
    if (Array.isArray(arr)) {
      if (depth > tracing) return "...";
      return arr.map((x) => prune(x, depth + 1));
    }
    return arr;
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
    return (str) => {
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
    };
  }

  function regex(re, fn = id) {
    return (str) => {
      const match = str.match(re);
      if (match && match.index === 0) {
        return Success(fn(match[0]), str.slice(match[0].length), [
          `regex ${re}`,
        ]);
      } else {
        return Fail(str, [
          `regex failed: Expected '${re}' but got '${trimShow(str)}'`,
        ]);
      }
    };
  }

  function sequence(name, parsers, fn = id) {
    return (str) => {
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
    };
  }

  function oneOf(name, parsers, fn = id) {
    return (str) => {
      const trace = [];
      for (let i = 0; i < parsers.length; i++) {
        const res = parsers[i](str);
        trace.push(res.trace);
        if (!res.failed) {
          return Success(fn(res.matched), res.rest, [name, ...trace]);
        }
      }
      return Fail(str, [`${name} oneOf failed`, trace]);
    };
  }

  function many(parser, fn = id) {
    return (str) => {
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
    };
  }

  function maybe(parser, fn = id) {
    return (str) => {
      const res = parser(str);
      if (res.failed) {
        return Success(fn([]), str, ["maybe failed", res.trace]);
      } else {
        return Success(fn([res.matched]), res.rest, ["maybe", res.trace]);
      }
    };
  }

  function not(parser, fn = () => null) {
    return (str) => {
      const res = parser(str);
      if (res.failed) {
        return Success(fn(), str, ["not", res.trace]);
      } else {
        return Fail(str, ["not failed", res.trace]);
      }
    };
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
        name: "theorem",
        ifs: [...ifs, ...lastIf],
        then,
      })
    )(str);
  }

  function term(str) {
    return oneOf("term", [parens, lam, pi, bin, eq, def, vari, app])(str);
  }
  function eqless(str) {
    return oneOf("eqless", [parens, lam, pi, bin, def, vari, app])(str);
  }
  function binless(str) {
    return oneOf("binless", [parens, lam, pi, def, vari, app])(str);
  }
  function appless(str) {
    return oneOf("appless", [parens, lam, pi, vari])(str);
  }
  function lam(str) {
    return wseq(
      "lam",
      [regex(/λ|fn|lambda/), vari, literal(":"), term, literal("."), term],
      ([_, v, __, ty, ___, tm]) => ({
        name: "lam",
        vari: v,
        type: ty,
        term: tm,
      })
    )(str);
  }
  function app(str) {
    return wseq("app", [appless, appless, many(appless)], ([x, arg, args]) => ({
      name: "app",
      x,
      args: [arg, ...args],
    }))(str);
  }
  function eq(str) {
    return wseq("eq", [eqless, literal("="), eqless], ([lhs, _, rhs]) => ({
      name: "eq",
      lhs,
      rhs,
    }))(str);
  }
  function vari(str) {
    return sequence(
      "vari",
      [not(oneOf("binNames", binNames)), regex(/[a-zA-Z\_][a-zA-Z0-9\_]*/)],
      ([_, x]) => ({
        name: "vari",
        vari: x,
      })
    )(str);
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
      [regex(/Π|Pi/), vari, literal(":"), term, literal("."), term],
      ([_, v, __, ty, ___, tm]) => ({ name: "pi", vari: v, type: ty, term: tm })
    )(str);
  }

  function mkOp(name, alias, arity) {
    const parsers = [literal(alias)];
    for (let i = 0; i < arity; i++) {
      parsers.push(appless);
    }
    return wseq(name, parsers, ([_, ...args]) => ({
      name,
      args,
    }));
  }
  function mkBinOp(name, alias) {
    return wseq(name, [binless, literal(alias), binless], ([lhs, _, rhs]) => ({
      name,
      lhs,
      rhs,
    }));
  }
  const defParsers = [];
  const binParsers = [];
  const binNames = [];
  for (const c of ["Bool", "Type", "Wat"]) {
    defParsers.push(mkOp(c, c, 0));
  }
  for (const d of Object.keys(Defs)) {
    const names = [d, ...Object.values(Defs[d].alias)];
    const arity = Defs[d].arity;
    if (Defs[d].binop) {
      for (const name of names) {
        binParsers.push(mkBinOp(d, name));
        binNames.push(literal(name));
      }
    } else {
      for (const name of names) defParsers.push(mkOp(d, name, arity));
    }
  }
  const def = oneOf("def", defParsers);
  const bin = oneOf("bin", binParsers);

  return theorem;
}
