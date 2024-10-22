// proofs are written in a bidirectional stack language
// the stack is a list of terms and theorems
// running forwards builds up a theorem from an initial stack
// running backwards checks that a term forms a valid theorem
const Proof = (() => {
})()

const Definitions = {
  store: {},
  add(name, arity, term, alias = {}) {
    this.store[name] = { arity, term, alias };
  },
  get(name) {
    return this.store[name];
  },
  has(name) {
    return this.store[name] !== undefined;
  }
}