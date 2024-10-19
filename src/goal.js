const Proof = (() => {
  // proof objects are theorem/term objects reified into ADTs

  // can be read as proof of existence of a term
  function TERM(term) {
    const obj = {
      value: term,
      name: "TERM",
      match: matchOr("TERM", [term], () => obj),
      show: (env = new ShowEnv()) => `TERM: ${term.show(env)}`,
    };
    return Object.freeze(obj);
  }

  // lift a function of theorems/terms to a function of proofs
  function lift(name, arity, fn) {
    return (...args) => {
      if (args.length !== arity) {
        throw new Error(`Arity mismatch: ${name} expects ${arity} arguments`);
      }
      const thm = fn(...args.map((x) => x.value));
      const obj = {
        value: thm,
        name,
        args,
        match: matchOr(name, args, () => obj),
        show: (env = new ShowEnv()) => `${name}: ${thm.show(env)}`,
      };
      return Object.freeze(obj);
    };
  }

  // kernel functions lifted
  const REFL = lift("REFL", 1, Kernel.REFL);
  const TRANS = lift("TRANS", 2, Kernel.TRANS);
  const EAPP = lift("EAPP", 2, Kernel.EAPP);
  const ABS = lift("ABS", 2, Kernel.ABS);
  const APP = lift("APP", 2, Kernel.APP);
  const ASSUME = lift("ASSUME", 1, Kernel.ASSUME);
  const EMP = lift("EMP", 2, Kernel.EMP);
  const DEDUCT = lift("DEDUCT", 2, Kernel.DEDUCT);
  const EQ_DEF = lift("EQ_DEF", 2, Kernel.EQ_DEF);

  return {
    TERM,
    lift,
    REFL,
    TRANS,
    EAPP,
    ABS,
    APP,
    ASSUME,
    EMP,
    DEDUCT,
    EQ_DEF,
  };
})();

const Tactics = (() => {
  // Goal = G Proof [Proofs]

  function Goal(then, todos) {
    const obj = {
      then,
      todos,
      match: matchOr("Goal", [then, todos], () => obj),
      show: (env = new ShowEnv()) => {
        const todoStr = todos.map((t, i) => `${i}. ${t.show(env)}`).join("\n");
        return `? ⊢ ${then.show(env)}\n${todoStr}`;
      },
    };
    return Object.freeze(obj);
  }

  // GoalTree = Node ([Proof] -> Proof) [Node] | ToProve Goal | Done Proof
  function Node(crumb, nodes) {
    const obj = {
      match: matchOr("Node", [crumb, nodes], () => obj),
    };
    return Object.freeze(obj);
  }

  function ToProve(goal) {
    const obj = {
      match: matchOr("ToProve", [goal], () => obj),
    };
    return Object.freeze(obj);
  }

  function Done(proof) {
    const obj = {
      match: matchOr("Done", [proof], () => obj),
    };
    return Object.freeze(obj);
  }

  // GoalPos is a zipper for traversing a goal tree
  function GoalPos(here, before, after, parents) {
    const obj = {
      here,
      before,
      after,
      parents,
      forest: () => {
        const acc = [here, ...after];
        for (const b of before) acc.unshift(b);
        return acc;
      },
      parent: () => {
        if (parents.length === 0) return Maybe.Nothing;
        const [ls, crumb, rs] = parents[0];
        return Maybe.Just(
          GoalPos(Node(crumb, obj.forest()), ls, rs, parents[0])
        );
      },
      next: () => {
        if (after.length === 0) return Maybe.Nothing;
        return Maybe.Just(
          GoalPos(after[0], [here, ...before], after.slice(1), parents)
        );
      },
      firstChild: () =>
        here.match({
          Node: (crumb, nodes) =>
            Maybe.Just(
              GoalPos(nodes[0], [], nodes.slice(1), [
                [before, crumb, after],
                ...parents,
              ])
            ),
          _: () => Maybe.Nothing,
        }),
      replace: (newHere) => GoalPos(newHere, before, after, parents),
      root: () =>
        obj
          .parent()
          .pipe((p) => p.root())
          .orElse(() => obj),
      firstLeaf: () =>
        obj
          .firstChild()
          .pipe((p) => p.firstLeaf())
          .orElse(() => obj),
      nextLeaf: () => {
        const go = (l) => l.next().orElse(() => l.parent().pipe(go)); // visit next node of any parent
        return go(obj).pipe((p) => p.firstLeaf());
      },
    };
    return Object.freeze(obj);
  }

  function walkFrom(node) {
    return GoalPos(node, [], [], []);
  }
  function leaves(node) {
    let pos = walkFrom(node).firstLeaf();
    const acc = [];
    function go(p) {
      acc.push(p);
      p.nextLeaf().pipe(go);
    }
    go(pos);
    return acc;
  }

  function goals(node) {
    return leaves(node).filter((x) =>
      x.here.match({ ToProve: (_) => true, _: () => false })
    );
  }

  // try to prove a term with the given tactic
  // returns a proof if successful
  function prove(term, tactic) {
    if (term.type !== Kernel.Bool)
      return Either.Left("prove: a term to prove must be of type Bool");
    const goal = Goal(term, []);
    return idTac(goal)
      .pipe((n) => by(tactic, n))
      .pipe(justify)
      .pipe((proof) => {
        const thm = proof.value;
        if (thm.ifs.length == 0 && term.eq(thm.then))
          return Either.Right(proof);
        return Either.Left(
          `prove: tried to prove ${term.show()} but actually proved ${thm.show()}`
        );
      });
  }
  function tackle(tactic, pos) {
    return pos.here.match({
      ToProve: (goal) => tactic(goal).map(pos.replace),
      _: () => Either.Left("tackle: not a goal"),
    });
  }
  function by(tactic, node) {
    const gs = goals(node);
    if (gs.length === 0) return Either.Left("by: no goals to prove");
    const g = gs[0];
    return tackle(tactic, g).map((p) => p.root().here);
  }
  function justify(node) {
    return node.match({
      Node: (crumb, nodes) => Either.collect(nodes.map(justify)).map(crumb),
      Done: (proof) => Either.Right(proof),
      _: () => Either.Left("justify: not a proof"),
    });
  }

  // Tactic = Goal -> Either String GoalTree

  const noTac = (_) => Either.Left("noTac failed: noTac always fails");
  const idTac = (goal) => Either.Right(ToProve(goal));

  function acceptTac(proof) {
    return (goal) => {
      if (goal.then.eq(proof.value.then))
        return Either.Right(Node(([x]) => x, [Done(proof)]));
      return Either.Left(
        `acceptTac failed: theorem ${proof.show()} does not prove goal\n${goal.show()}`
      );
    };
  }

  function reflTac(goal) {
    const [l, _] = Kernel.de("eq", goal.then);
    return acceptTac(Proof.REFL(Proof.TERM(l)))(goal);
  }

  return { prove, noTac, idTac, acceptTac, reflTac };
})();
