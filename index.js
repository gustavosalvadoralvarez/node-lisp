
// jshint esnext:true

const NILL = Symbol("NILL");

const sexpr = (head, tail) => [head, (tail ? tail : NILL)];

const atom = (x) => sexpr(x);

const cons = sexpr;

const string$ = (x) => x instanceof String;

const number$ = (x) => x instanceof Number;

const regexp$ = (x) => x instanceof RegExp;

const array$ = (x) => Array.isArray(x);

const object$ = (x) => !array$(x) && (x instanceof Object));

const map$ = (x) => x instanceof Map;

const symbol$ = (x) => x instanceof Symbol

const set$ = (x) => x instanceof Set;

const lambda$ = (x) => x instanceof Function;

const label$ = (x) => string$(x) && (x in NS);

// atom [X] = atom [(X · NILL)] = T
// atom [(X · A)] = F
const atom$ = (x) => {
  if (!array$(x)) return true;
  let head = x[0],
      tail = x.length > 1 ? x.slice(1) : null;
  return (!tail || tail === NILL);};

// eq$ [X; X] = T
// eq$ [X; A] = F
// eq$ [X; (X · A)] is undefined.
const eq$ = (x, y) => !(!atom$(x) || !atom$(y)) ? undefined : (x[0] === y[0]);

// car [(X · A)] = X
// car [((X · A) · Y )] = (X · A
const car = (x) => atom$(x) ? undefined : x[0];

const cdr = (x) => {
  return atom$(x) ?
          undefined :
          x.length > 1 ?
            1 in x ? x[1] :
            undefined;};

const caar = (x) => car(car(x));

const cadr = (x) => car(cdr(x));

const caddr = (x) => car(cdr(cdr(x)));

const cddr = (x) => cdr(cdr(x));

const list$ = (x) => {
  let rest = cdr(x);
  return array$(x) && !atom$(x) && (list$(rest) || atom$(rest));
};

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

const empty$ = (x) => !array$(x) || !x.length || nill$(x));


const list = function (head, ...tail) {
  return tail[0] === close ? head : cons(head, list(...tail));

const close = Symbol(")");

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

const quote = (x) => {
  x.QUOTED = true;
  return () => x;};

const quote$ = (x) x && x.QUOTED;

const ENV = new Map();

const NS = {};

const def = (label, x) => {
  const sym = Symbol(label);
  ENV.set(sym, x);
  NS[label] = sym;
  return null;};

const LAMBDA = Symbol("LAMBDA");

const QUOTE = Symbol("QUOTE");

const LABEL = Symbol("LABEL");

const COND = Symbol("COND");

const defn = (name, fn) => def(name, cons(LAMBDA, fn));

const not = (x) => !x;

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

def("define", def);
def("function", defn);
def("(", list);
def(")", close);
def("T", true);
def("F", false);
def("~", not);
def("and", and);
def("or", or);
def("xor", xor);
def("+", add);
def("-", sub);
def("*", mult);
def("EXP", exp);
def("%", mod);
def("lambda", LAMBDA);
def("quote", QUOTE);
def("label", LABEL);
def("cond", COND);
def("NILL", NILL);
def("sexpr", sexpr);
def("atom", (x) => atom(car(x)));
def("cons", (x) => cons(car(x), cadr(x)));
def("car", (x) => caar(x));
def("cdr", (x) => cdar(x));
def("eq?", (x) => eq$(car(x), cadr(x)));
def("string?", string$);
def("number?", number$);
def("regexp?", regexp$);
def("array?", array$);
def("object?", object$);
def("map?", map$);
def("symbol?", symbol$);
def("set?", set$);
def("lambda?", lambda$);
def("label?", label$);
def("atom?", atom$);
def("caar", caar);
def("cadr", cadr);
def("caddr", car);
def("caddr", caddr);
def("list?", list$);


function apply(fn, x, a){
  let fncar = car(fn),
      fncdr = cdr(fn);
  return atom$(fn) ?
          ((fncar in NS) ? ENV.get(NS[fncar]) : apply(evl(fn, a), x, a)) :
        eq$(fncar, LAMBDA) ?
          evl(cadder(fn), pairlis(cadr(fn), x, a))




          fn(...args) : apply(car(fn), ...args)) :
          (label$(fn))

}

function evl()


















def("ff", ff);
def("subst", subst);
def("equal?", equal$);
def("nill?", nill$);
def("empty?", empty$);
def("append", append);
def("member?", member$);
def("among?", among$);
def("pair", pair);
def("assoc", assoc);
def("sub2", sub2);
def("sublis", sublis);
def("pairlis", pairlis);
def("quote", quote);
def("quote?", quote$);
