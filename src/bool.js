const BoolThms = (() => {
  const {
    Type,
    Bool,
    Arr,
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
    ABS,
    EAPP,
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

  const [forallX, FORALL_DEF] = mkOp(
    "∀",
    2,
    fn(Type, (A) =>
      fn(Arr(A, Bool), (p) =>
        eq(
          p,
          fn(A, (_) => T)
        )
      )
    )
  );
  const forall = (A, body) => forallX(A, fn(A, body));

  const [F, F_DEF] = mkConst(
    "F",
    forall(Bool, (x) => x)
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
      fn(Bool, (q) => forall(Bool, (r) => imp(imp(p, r), imp(imp(q, r), r))))
    )
  );

  const [existX, EXIST_DEF] = mkOp(
    "∃",
    1,
    fn(Type, (A) =>
      fn(Arr(A, Bool), (p) =>
        forall(Bool, (q) =>
          imp(
            forall(A, (x) => imp(app(p, x), q)), // if q is the term we want
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

  function AND(thm1, thm2) {
    const f = vari(Arr(Bool, Arr(Bool, Bool)));
    const thm = ABS(f, EAPP(EAPP(REFL(f), EQT_INTRO(thm1)), EQT_INTRO(thm2)));
    return EMP(SYM(AND_THM(thm1.then, thm2.then)), thm);
  }

  const K_comb = fn(Bool, (x) => fn(Bool, (_) => x));
  const KI_comb = fn(Bool, (_) => fn(Bool, (y) => y));

  const AND_SEL = (comb) => (thm) => {
    const [p, q] = de("∧", thm.then);
    const lem = EAPP(EMP(AND_THM(p, q), thm), REFL(comb));
    const [lemL, lemR] = de("eq", lem.then);

    return EQT_ELIM(TRANS(SYM(NORM(lemL)), TRANS(lem, NORM(lemR))));
  };

  const AND_L = AND_SEL(K_comb);
  const AND_R = AND_SEL(KI_comb);

  const NOT_INTRO = (thm) => EMP(SYM(NOT_THM(thm.then)), thm);

  // u, A |- t  /  A |- u => t
  function DISCH(u, thm) {
    const lem0 = AND_L(ASSUME(and(u, thm.then))); // u, t |- u
    const lem1 = AND(ASSUME(u), thm); // u, A |- u and t
    const lem2 = DEDUCT(lem1, lem0); // A |- u
    return EMP(SYM(IMP_THM(u, thm.then)), lem2);
  }

  // A |- t1 => t2,   B |- t1  /  A union B |- t2
  function MP(t1impt2thm, t1thm) {
    const [t1, t2] = de("⇒", t1impt2thm.then);
    return AND_L(
      EQT_ELIM(TRANS(EMP(IMP_THM(t1, t2), t1impt2thm), EQT_INTRO(t1thm)))
    );
  }

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
    AND,
    AND_L,
    AND_R,
    NOT_INTRO,
    DISCH,
    MP,
  };
})();
