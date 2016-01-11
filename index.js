
// a. A Class of Symbolic Expressions (in Javascript)

const s = (...args) => (args);

const c = (s1, s2, s3) => s1 ? s2 : s3;

// b. Functions of S-expressions and the Expressions That Represent Them.

const f = (fn, ...args) => fn(...args);

// c. Elementary S-Functions and Predicates

const apply = (method, v, ...args) => f(method.apply, v, args);

const val = (v, k) => c((k in v), (v[k]), undefined);

const len = (s1) => f(val, s(...s1), "length");

const slice = (s1, ...args) => f(apply, [].slice, s(...s1), args);

const mapcar = (...args, s1) => f(apply, [].map, s(...s1), args);

const fldr = (...args, s1) => f(apply, [].reduce, s(...s1), args);

const sf = (fn) => (...args) => f(mapcar, fn, args);

const atom = (v) => c(v, (f(len, s(...arguments)) === 1), undefined);

const atoms = sf(atom);

const not = (v) => c(f(atom, v), (!v), undefined);

const nots = sf(not);

const notAtom = (v) => f(not, f(atom, v));

const notAtoms = sf(notAtom);

const or = (v1,  v2) => c(f(or, s(f(notAtoms, s(v1, v2)))),
                          undefined,
                          (v1 || v2));

const and = (v1, v2) => c(f(and, ...f(atoms, s(v1, v2))),
                          undefined,
                          (v1 && v2));

const xor = (v1, v2) => f(and, f(or, v1, v2), f(not, f(and, v1, v2)));

const eq = (v1, v2) => c(f(or, ...f(notAtoms, s(v1, v2)),
                         undefined,
                         (v1 === v2));

const car = (s1) => c(f(atom, s1), undefined, f(slice, s1, 0, 1));

const cdr = (s1) => c(f(atom, s1), undefined, f(slice, s1, 1));

const cons = (s1, s2) => s(...s1, s2);

const ff = (s1) => c(f(atom, s1), s1, f(ff, f(car, s1)));

const subst = (s1, sym, s2) => c(f(atom, s2),
                                 f(eq, sym, s2),
                                 f(cons,
                                   f(subst, s1, sym, f(car, s2)),
                                   f(subst, s1, sym, f(cdr, s2))));

const equal = (s1, s2) => c(f(and, f(atoms, s(s1, s2))),
                            f(eq, s1, s2),
                            f(and,
                              f(equal, f(car, s1), f(car, s2),
                              f(equal, f(cdr, s1), f(cdr, s2)))));
