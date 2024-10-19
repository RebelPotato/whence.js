// unification for unknown variables?
// use microkanren for this?
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
    if (y.has(x))
      throw Error(
        `unify: ${y.show()} contains circular reference to ${x.show()}`
      );
    this.env.set(x, y);
    return this;
  }
  notEmpty(fn, elseFn) {
    if (this.env.size > 0) return fn(this);
    return elseFn();
  }
}