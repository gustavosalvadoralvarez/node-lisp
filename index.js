
// jshint esnext:true

const NILL = Symbol("NILL");

const sexpr = (head, tail) => return new Map().set(head, tail);

const atom = (x) => sexpr(x, NILL);

const cons = sexpr;

const string$ = (x) => x instanceof String;

const number$ = (x) => x instanceof Number;

const regexp$ = (x) => x instanceof RegExp;

const array$ = (x) => Array.isArray(x);

const map$ = (x) => x instanceof Map;

const symbol$ = (x) => x instanceof Symbol

const set$ = (x) => x instanceof Set;

const object$ = (x) => !array$(x) && !$map(x) && (x instanceof Object);


const lambda$ = (x) => x instanceof Function;

// atom [X] = atom [(X · NILL)] = T
// atom [(X · A)] = F
const atom$ = (x) => {
  if (string$(x) ||
      number$(x) ||
      regexp$(x) ||
      array$(x) ||
      set$(x) ||
      symbol$(x) ||
      set$(x) ||
      object$(x)) return true;
  if (map$(x)) return x.values()[0] === NILL;
  throw new Error("Data type ${ typeof x } not supported.");};


// eq$ [X; X] = T
// eq$ [X; A] = F
// eq$ [X; (X · A)] is undefined.
const eq$ = (x, y) => !(!atom$(x) || !atom$(y)) ? undefined : (x[0] === y[0]);

// car [(X · A)] = X
// car [((X · A) · Y )] = (X · A
const car = (x) => atom$(x) ? undefined : x.keys()[0];

const cdr = (x) => atom$(x) ? undefined : x.values()[0];
const caar = (x) => car(car(x));

const cadr = (x) => car(cdr(x));

const caddr = (x) => car(cdr(cdr(x)));

const cddr = (x) => cdr(cdr(x));


// ff[x] = [atom[x] → x; T → ff[car[x]]]
const ff = function ff(x){
  return (atom$(x) ?
            head(x) :
            ff(car(x)))};

// subst [x; y; z] = [atom [z] →
//                     [eq$ [z; y] → x;
//                     T → z];
//                    T →
//                     cons [subst [x; y; car [z]]; subst [x; y; cdr [z]]]]
const subst = function subst(x, y, z){
  return (atom$(z) ?
            (eq$(z, y) ? x : z) :
            cons(subst(x, y, car(z),
               subst(x, y, cdr(z)))))};

// eq$ual [x; y] = [atom [x] ∧ atom [y] ∧ eq$ [x; y]] ∨
//                [¬ atom [x] ∧¬ atom [y] ∧ eq$ual [car [x]; car [y]] ∧
//                 eq$ual [cdr [x]; cdr [y]]]
const equal$ = function eq$ual(x, y){
  return (atom$(x) && atom$(y) && eq$(x, y)) ||
         (!atom$(x) && !atom$(y) && equal(car(x), car(y)) && equal(cdr(x), cdr(y)))};

// null[x] = atom[x] ∧ eq$[x; NIL]
const nill$ = (x) => !(!atom$(x) || !eq$(tail(x), NILL) || empty$(x));

// append [x; y] = [null[x] → y;
//                  T → cons [car [x];
//                            append [cdr [x]; y]]]
const append = function append(x, y){
  return (nill$(x) ?
            y :
            cons(car(x),
                 append(cdr(x), y))))};

 const member$ = function(x, y){
   return  nill$(y) ?
            !!0 :
            eq$ual$(x, car(y)) ?
              !0 :
              member$(x, cdr(y));}

// among[x; y] = ¬null[y] ∧
//               [eq$ual[x; car[y]] ∨
//               among[x; cdr[y]]]
const among$ = function among(x, y){
  return !nill$(x) &&
          (eq$ual(x, car(y) ||
          among(x, cdr(y))));};

// pair[x; y] = [null[x]∧null[y] → NIL;
//               ¬atom[x]∧¬atom[y] → cons[list[car[x]; car[y]];
//               pair[cdr[x]; cdr[y]]]
const pair = function pair(x, y){
  return nill$(x) && nill$(y) ?
            NILL :
            !(!atom$(x) || !atom$(y)) ?
                cons(list(car(x), car(y)) :
                     pair(cdr(x), cdr(y)))};

// assoc[x; y] = eq$[caar[y]; x] → cadar[y];
//               T → assoc[x; cdr[y]]]
const assoc = function assoc(x, y){
  return eq$(caar(y), x) ?
            cadar(y) :
            assoc(x, cdr(y));};

// sub2[x; z] = [null[x] → z;
//               eq$[caar[x]; z] → cadar[x];
//              T → sub2[cdr[x]; z]]
const sub2 = function(x, z){
  return nill$(x) ?
            y :
            eq$(caar(x), z) ?
              cadar(x) :
              sub2(cdr(x), z);};

// sublis[x; y] = [atom[y] → sub2[x; y];
//                T → cons[sublis[x; car[y]]; sublis[x; cdr[y]]]
const sublis = function sublis(x, y){
  return atom$(y) ?
            sub2(x, y) :
            cons(sublis(x, car(y),
                 sublis(x, cdr(y))));};

const pairlis = function pairlis(x, y, a){
  return empty$(x) ?
            a :
            cons(cons(car(x), car(y)),
                 pairlis(cdr(x), cdr(y), a));};


 // additional m expressions
 const not = (x) => !x;

 const T = () => true;

 const F = () => false;

 const and = function and(n, ...r){
   return n && (empty$(r) ? true : and(...r));};

 const or = function or(n, ...r){
   return n || (empty$(r) ? false : or(...r));};

 const xor = function xor(n, ...r){
   return and(or(n, ...r), not(and(n, ...r)));

 const sub = function sub(n, ...r){
   return n - (empty$(r) ? 0 : sub(...r));};

 const add = function add(n, ...r){
   return n + (empty$(r) ? 0 : add(...r));};

 const sub = function sub(n, ...r){
   return n - (empty$(r) ? 0 : sub(...r));};

 const mult = function mult(n, ...r){
   return n * (empty$(r) ? 1 : mult(...r));};

 const mod = (x, y) => x%y;

 const exp = (x, y) => Math.pow(x, y);

// Name space and environment
const ENV = new Map();

const NS = {};

const NS$ = (x) => (x in NS);

const SNTX = {};

const SNTX$ = (x) => (x in SNTX);

const DTS = {};

const DTS$ = (x) => (x in DTS);

// interpreter m expressions

const define_syntax = (label, m) => {
  const sym = Symbol(label);
  ENV.set(sym, m);
  SNTX[label] = sym;
  return sym;
};

const eval_expr = function eval_syntax(expr, ...env){
  let [λ, env] = [car(expr), cdr(expr)];
  if(SNTX$(λ)) return eval_syntax(ENV.get(SNTX[λ]), ...env);
  if(lambda$(λ)) return λ(...env);
};



const set = (label, x) => {
   const sym = Symbol(label);
   ENV.set(sym, x);
   NS[label] = sym;
   return null;};

// errors (all interpreter errors thrown)

const interpreter_error = (desc) => throw new Error("INTERPRETER ERROR: ${ desc }");

// data types

const list_constructor = function list_constructor(x, a){
  if (empty$(x)) return a;
  return list_constructor(x.slice(1), cons(x[0], a));};

const closure = (x) => () => x;

const CORE_DATA_TYPES = list_constructor([
  // reference types
  cons("number", cons(number$, closure)),
  cons("string", cons(string$, closure)),
  cons("symbol", cons(symbol$, closure)),
  cons("regexp", cons(regexp$, closure)),
  cons("true", closure(true), closure(true)),
  cons("false", closure(true), closure(false)),
  cons("undefined", closure(true), closure(undefined)),
  // collections
  cons("set", cons(set$, (...args) => closure(Set(args)))),
  cons("array", cons(array$, (...args) => closure(args))),
  cons("object", cons((...x) => x.length && x.length%2 === 0,
            (...args) => closure(
            args.reduce((ac, v, i, arr) => {
              if (i%2) ac[v] = arr[i+1];
              return ac; }, {})))),
  // lisp primitives
  cons("lambda", cons((x) => lambda$,
            (x) => closure(cons(
              (x.toString
                .match(/\((.*)\)/)[1]
                .split(",")
                .map((y) => y.trim())),
              x)))),
  cons("atom", cons(atom$, (x) => closure(atom(x)))),
  cons("list", cons(array$, (x) => closure(list_constructor(x, NILL)))),
  cons("quote", cons(() => true, closure)),
  cons("label", string$, closure)],
  NILL);

const type_constructor = (label, type_check, constructor_mexpr) => {
  return (x) => {
    if(type_check(x)) return cons(DTS[label], constructor_mexpr(x));
    interpreter_error("TYPE_ERROR: ${ label } TYPE CHECK FAILED");}};

const define_data_type = (label, mexprs) => {
  DTS[label] = define_syntax(
                label,
                type_constructor(label,
                                 car(mexprs),
                                 cdr(mexprs)));};

const define_data_types = function define_data_types(x){
  let [xcar, xcdr] = [car(x), cdr(x)];
  if ($nill(xcar)) return null;
  define_data_type(caar(x), cddr(x));
  return define_data_types(xcdr);};

const eval_data_value = (x) => {
  let [t, v] = [car(x), cdr(x)];
  if (!DTS$(t)) return interpreter_error(
    "VALUE ERROR: DATA TYPE NOT DEFINED: ${ t }");
  if(!lambda$(v)) return interpreter_error(
    "VALUE ERROR: UNDECLARED VALUE: ${ v } \n"+
    "VALUES MUST BE DECALRED WITH THE FORMS:\n\t"+
    "[TYPE, VAL]\n\t"+
    "(['QUOTE', VAL'])");
  return v();
};


define_data_types(CORE_DATA_TYPES);
