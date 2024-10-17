const EqualThms = (() => {
  const { REFL, EAPP, EMP, TRANS, APP, EQ_DEF, de, fn, eq, app } = Kernel;

  // return a theorem, stating that (a term = its weak head normal form)
  function NORM_APP(ap) {
    return ap.match({
      app: (op, arg) =>
        op.match({
          app: () => {
            // op is (op1 arg1)
            const qThm = NORM_APP(op); // |- op1 arg1 = q
            const [_, q] = de("eq", qThm.then);
            const rThm = NORM_APP(app(q, arg)); // |- q arg = r
            return TRANS(EAPP(qThm, REFL(arg)), rThm);
          },
          fn: () => {
            const rThm = APP(op, arg); // |- op arg = r
            const [_, r] = de("eq", rThm.then);
            return TRANS(rThm, NORM_APP(r));
          },
          _: () => REFL(ap),
        }),
      _: () => REFL(ap),
    });
  }

  // |- a = b / |- b = a
  function SYM(thm) {
    const [l, r] = de("eq", thm.then);
    const lthm = REFL(l);
    const eqfn = fn(r.type, (x) => fn(l.type, (y) => eq(x, y)));

    const lem0 = TRANS(EQ_DEF(l, l), EAPP(EAPP(REFL(eqfn), thm), lthm)); // |- (l = l) = ((eqfn r) l)
    return EMP(TRANS(lem0, NORM_APP(app(app(eqfn, r), l))), lthm);
  }

  // Conv = term -> thm
  function CONV_RULE(conv, thm) {
    return EMP(conv(thm.then), thm);
  }

  function OP_CONV(conv) {
    return (thm) => {
      const [op, arg] = de("app", thm.then);
      return AP_TERM(op, conv(arg));
    };
  }

  function ARG_CONV(conv) {
    return (thm) => {
      const [op, arg] = de("app", thm.then);
      return EAPP(conv(op), REFL(arg));
    };
  }

  return { SYM, CONV_RULE, OP_CONV, ARG_CONV, NORM_APP };
})();
