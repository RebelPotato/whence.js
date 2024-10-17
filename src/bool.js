const BoolThms = (() => {
  const {
    Bool,
    Arr,
    Tvar,
    eq,
    fn,
    app,
    vari,
    mkConst,
    mkOp,
    mkBinOp,
    REFL,
    EMP,
    DEDUCT,
    ASSUME,
    TRANS,
    de,
  } = Kernel;
  const { SYM, NORM } = EqualThms;

  // truth
  const [T, T_DEF] = mkConst(
    "T",
    eq(
      fn(Bool, (x) => x),
      fn(Bool, (x) => x)
    )
  );

  const freshT = (name, fn) => fn(Tvar(name));

  const [forallX, FORALL_DEF] = freshT("A", (A) =>
    mkOp(
      "∀",
      1,
      fn(Arr(A, Bool), (p) =>
        eq(
          p,
          fn(A, (_) => T)
        )
      )
    )
  );
  const forall = (body) => forallX(fn(Bool, body));

  const [F, F_DEF] = mkConst(
    "F",
    forall((x) => x)
  );

  const [and, AND_DEF] = mkBinOp(
    "∧",
    fn(Bool, (p) =>
      fn(Bool, (q) =>
        eq(
          fn(Arr(Bool, Arr(Bool, Bool)), (f) => app(app(f, p), q)),
          fn(Arr(Bool, Arr(Bool, Bool)), (f) => app(app(f, T), T))
        )
      )
    )
  );

  const [imp, IMP_DEF] = mkBinOp(
    "⇒",
    fn(Bool, (p) => fn(Bool, (q) => eq(and(p, q), p)))
  );

  const [not, NOT_DEF] = mkOp(
    "¬",
    1,
    fn(Bool, (p) => imp(p, F))
  );

  const [or, OR_DEF] = mkBinOp(
    "∨",
    fn(Bool, (p) =>
      fn(Bool, (q) => forall((r) => imp(imp(p, r), imp(imp(q, r), r))))
    )
  );

  const [existX, EXIST_DEF] = freshT("A", (A) =>
    mkOp(
      "∃",
      1,
      fn(Arr(A, Bool), (p) =>
        forall((q) =>
          imp(
            forall((x) => imp(app(p, x), q)), // if q is the term we want
            q // then q is true
          )
        )
      )
    )
  );
  const exist = (body) => existX(fn(Bool, body));

  // |- T
  const TRUTH = EMP(SYM(T_DEF), REFL(fn(Bool, (x) => x)));
  // A |- (l = T) / A |- l
  const EQT_ELIM = (thm) => EMP(SYM(thm), TRUTH);
  // A |- l / A |- (l = T)
  const EQT_INTRO = (thm) => {
    const l = thm.then;
    const a = vari(Bool);
    const thm1 = DEDUCT(ASSUME(a), TRUTH); // a |- a = T
    const pthm = DEDUCT(EQT_ELIM(ASSUME(thm1.then)), thm1); // |- a = (a = T)
    return EMP(pthm.replace(a, l), thm);
  };

  function DEF_TO_THM(def) {
    return (...args) => {
      const defThm = def(...args);
      const [_, rhs] = de("eq", defThm.then);
      return TRANS(defThm, NORM(rhs));
    };
  }

  const AND_THM = DEF_TO_THM(AND_DEF);
  const IMP_THM = DEF_TO_THM(IMP_DEF);
  const NOT_THM = DEF_TO_THM(NOT_DEF);
  const OR_THM = DEF_TO_THM(OR_DEF);

  return {
    // constants and operations
    T,
    T_DEF,
    forall,
    FORALL_DEF,
    F,
    F_DEF,
    and,
    AND_DEF,
    imp,
    IMP_DEF,
    not,
    NOT_DEF,
    or,
    OR_DEF,
    exist,
    EXIST_DEF,
    // theorems
    TRUTH,
    EQT_ELIM,
    EQT_INTRO,
    AND_THM,
    IMP_THM,
    NOT_THM,
    OR_THM,
  };
})();
