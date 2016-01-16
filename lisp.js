
// jshint esnext:true


/////////////////////////////////////////////////////////////
//  GLOBAL ENVIRONMENT
////////////////////////////////////////////////////////////

const ENV = (() => {
  let global_env = {};
  return {
    get: (sym) => {
      if (sym in global_env) return car(global_env[sym]);
      return undefined;},
    set: (sym, x) => {
      if (sym in global_env) global_env.concat(x);
      global_env[sym] = [x];
      return null;},
    contains: (x) => x in global_env,
    clear: (sym) => {
      if (sym in global_env) ENV.set(sym, null);},
    delete: (sym) => delete global_env[sym],
    back: (sym, y) => {
      if (sym in global_env) {
        let value = ENV.get(sym),
            ix = value.length - y;
        if (ix > 0) return value[y];
        return undefined;}
      return undefined;},
     "export": () => {
     let _module = {};
     for (let k in global_env){
       _module[k] = global_env[k];}
     return _module;},
    "require": (x) => {
      let _module = x.export();
      if (_module || !(_module instanceof Object)) return module_error(
        "ENV.require", "MODULE EXPORTS NOT FOUND");
      for (let k in _module){
        ENV.set(k, _module[k]);}}};})();

/////////////////////////////////////////////////////////////
//  ERRORS
////////////////////////////////////////////////////////////
// All interpreter errors are thrown.
// Errors are defined into classesd, and produce
// native Error objects whose message has the form
// "INTERPRETER ERROR: ", <error-class>, " : ",
// <name-of-proceeduer>, " : ", <description>

var interpreter_error = (typ) => {
  return (loc, desc) => {
    let err = new Error("INTERPRETER ERROR: ${ typ } @ ${ loc } : ${ desc }");
    throw err;};};

var evaluation_error = interpreter_error("EVALUATION");

var signature_error = interpreter_error("SIGNATURE");

var type_error = interpreter_error("TYPE");

var value_error = interpreter_error("VALUE");

var syntax_error = interpreter_error("SYNTAX");

var module_error = interpreter_error("MODULE");


/////////////////////////////////////////////////////////////
//  PRIMITIVE IDENTITY PREDICATES
////////////////////////////////////////////////////////////

var function$ = (x) => x.prototype === Function.prototype;

var bool$ = (x) => x.prototype === Boolean.prototype;

var string$ = (x) => x.prototype === String.prototype;

var number$ = (x) => x.prototype === Number.prototype;

var regexp$ = (x) => x.prototype === RegExp.prototype;

var symbol$ = (x) => x.prototype === Symbol.prototype;

var map$ = (x) => x.prototype === Map.prototype;

var set$ = (x) => x.prototype === Set.prototype;

var array$ = (x) => x.prototype === Array.prototype;

var object$ = (x) => x.prototype === Object.prototype;

var undefined$ = (x) => x === undefined;

var null$ = (x) => x === null;

// PRIMITIVEs are native data types that evaluate to themselves
// and are wrapped in closures to generate immutability when used
// as VALUES (see bellow). Arrays are excluded due to their role
// as syntax (replacing the parens typical of LISPs). Data in the form
// of native arrays must of QUOTE'd (see bellow), contained in a
// native object or wrapped in a closure.
// <primitive> := <boolean> | <number> | <string> | <function> |
//                <reg-exp> | <symbol> | <set> |
//                <object> | <undefined> | <null>
var primitive$ = (x) => {
  if (string$(x)) return !Symbol.for(x);
  return regexp$(X) ||
         symbol$(X) ||
         boolean$(X) ||
         undefined$(X) ||
         set$(X) ||
         function$(x) ||
         object$(X);};

var array_first = (x) => {
  if (x.length) return x[0];
  return undefined;};

// ATOMS are indivisible data. Since in a LISP code is data and data code,
// functions are both primitive and atomic data like all other data types.
// Syntaxtically an atom is represented by an array with a single item or
// the 'naked' native object instance; Empty arrays are atoms
// <atom> := "[" <primitive> ["," <null>] "]" | <primitive>

var atom$ = (x) => (array$(x) && (!x.length || primitive$(array_first(x))) ||
                    primitive$(x));

// LISTS are tree-like structures of nested lists, each of which has only
// two items: a CAR and a CDR (see bellow); Lists are also called s-expressions.
// <s-expression> := "[", <s-expression> | <atom> | <primitive>, [","
//                      <s-expression> | <primitive>], "]"
var list = (car, cdr) => [car, cdr];

var list$ = (x) => (array$(x) && !atom$(x));

// NILL is true only of empty atoms, i.e. null, and [];
var nill = (x) => x === null || (array$(x) && !x.length);


///////////////////////////////////////////////////////////////////////
//  M-EXPRESSIONS
///////////////////////////////////////////////////////////////////////
// M-EXPRESSIONS are proceedures (lambdas, functions) which operate on
// <s-expressions> to produce a <primitive>, <atom> or <s-expression>
// but are not themselves represented are an <s-expression>

var cons = list;

var car = (x) => !atom$(x) && x[0] || null;

var cdr = (x) => (!atom(x) && x.length > 1) && x.slice(0) || null;

var caar = (x) => car(car(x));

var cddr = (x) => cdr(cdr(x));

var cadr = (x) => car(cdr(x));

var cdar = (x) => cdr(car(x));

var caddr = (x) => car(cdr(x));

var cdaar = (x) => cdr(car(car(x)));

// ff[x] = [atom[x] → x; T → ff[car[x]]]

var first_primitive = function ff(x){
  if (atom$(x)) return x[0];
  return ff(car(x));};

var last_primitive = function ll(x){
  if (atom$(x)) return x[0];
  return ll(cdr(x));};

// subst [x; y; z] = [atom [z] →
//                     [eq$ [z; y] → x;
//                     T → z];
//                    T →
//                     cons [subst [x; y; car [z]]; subst [x; y; cdr [z]]]]
// var subst = function subst(x, y, z){
//   return (atom$(z) ?
//             (eq$(z, y) ? x : z) :
//             cons(subst(x, y, car(z),
//                subst(x, y, cdr(z)))))};
// native tail-recursive implementation (for performance)

var subst = function subst(x, y, z, w){
  let c = w ? cons(z, w) : z; // revaritution strategy
  if (atom$(c)) return (eq$(c, y) ? x : z);
  return subst(x, y, car(c), cdr(c));};

// equal [x; y] = [atom [x] ∧ atom [y] ∧ eq$ [x; y]] ∨
//                [¬ atom [x] ∧¬ atom [y] ∧ eq$ual [car [x]; car [y]] ∧
//                 eq$ual [cdr [x]; cdr [y]]]

var equal$ = function equal$(x, y){
  return (atom$(x) && atom$(y) &&
          eq$(x, y)) ||
         (!atom$(x) && !atom$(y) &&
         equal$(car(x), car(y)) &&
         equal$(cdr(x), cdr(y)));};


// append [x; y] = [null[x] → y;
//                  T → cons [car [x];
//                            append [cdr [x]; y]]]
// var append = function append(x, y){
//   return (nill$(x) ?
//             y :
//             cons(car(x),
//                  append(cdr(x), y))))};
// native tail recursive implementation for performance

var rev = (x) => {
  return reverse_list(cons(cdr(x), car(x)));};
// mutual recursion strategy
var reverse_list = function reverse(x){
  if (atom$(x)) return x;
  return reverse(cdr(x), rev(car(x)));};

var append = (x, y) =>  {
  if(nill$(x)) return y;
  return reverse(cons(reverse(y), x));};

// member[x; y] = ¬null[y] ∧
//               [eq$ual[x; car[y]] ∨
//               member[x; cdr[y]]]

var member$ = function(x, y){
  return!(nill$(y) || !equal$(x, car(y))) || member$(x, cdr(y));};

// pair[x; y] = [null[x]∧null[y] → NIL;
//               ¬atom[x]∧¬atom[y] → cons[list[car[x]; car[y]];
//               pair[cdr[x]; cdr[y]]]
// var pair = function pair(x, y){
//   return nill$(x) && nill$(y) ?
//             null :
//             !(!atom$(x) || !atom$(y)) ?
//                 cons(list(car(x), car(y)) :
//                      pair(cdr(x), cdr(y)))};
// native tail recursive implementation

var list_len = function list_len(x, y=0){
  return y + list_len(cdr(x));};

var car_pair = (x, y) => cons(car(x), car(y));

var pair = function pair(x, y, z){
  if (nill$(x) && nill$(y)) return z;
  if (!z){
    let [len_x, len_y] = [list_len(x), list_len(y)];
    if (!(eq(len_x, len_y))) return signature_error(
      "PAIR",
      "X AND Y MUST BE OF SAME LENGTH, CURRENT: ${ len_x } ',' ${ len_y }");
    return pair(cdr(x), cdr(y), car_pair(x, y));}
  return pair(cdr(x), cdr(y), cons(z, car_pair(x, y)));};

// sub2[x; z] = [null[x] → z;
//               eq$[caar[x]; z] → cadar[x];
//              T → sub2[cdr[x]; z]]

var sub2 = function(x, z){
  if (nill$(x)) return y;
  if (eq$(caar(x), z)) return cadar(x);
  return sub2(cdr(x), z);};

// sublis[x; y] = [atom[y] → sub2[x; y];
//                T → cons[sublis[x; car[y]]; sublis[x; cdr[y]]]
// var sublis = function sublis(x, y){
//   return atom$(y) ?
//             sub2(x, y) :
//             cons(sublis(x, car(y),
//                  sublis(x, cdr(y))));};
// native implementation

var sub_car = (x, y) => sublis(x, car(y));
// multiple mutual
var sub_cdr = (x, y) => sublis(x, cdr(y));
// recursion strategy
var sublis = function sublis(x, y, z){
  let c = z ? cons(y, z) : y;
  if(atom$(c)) return sub2(x, c);
  return sublis(x, sub_car(x, c), sub_cdr(x, c));};

var pairlis = function pairlis(x, y, a){
  return empty$(x) ?
            a :
            cons(cons(car(x), car(y)),
                 pairlis(cdr(x), cdr(y), a));};

var identity = (x) => x;

var not = (x) => bool$(x) && !x || undefined;

var and = function and(n, ...r){
 return n && (r ? and(...r) : true);};

var or = function or(n, ...r){
 return n || (r ? or(...r) : true);};

var xor = function xor(n, ...r){
 return and(or(n, ...r), not(and(n, ...r)));};

var sub = function sub(n, ...r){
 return n - (r ? sub(...r) : 0);};

var add = function add(n, ...r){
 return n + (r ? sub(...r) : 0);};

var mult = function mult(n, ...r){
 return n * (r ? mult(...r) : 1);};

var divd = function divd(n, ...r){
 return n / (r ? divd(...r) : 1);};

var mod = (x, y) => x%y;

var pow = (x, y) => Math.pow(x, y);

var array_first_rest = (x) => [x[0] , x.slice(1)];

var flatten_list = function flatten_list(x, a){
  if(nill$(x)) return a;
  let [first, rest] = array_first_rest(x);
  return flatten_list(rest, cons(a, first));};

var array_to_list = function array_to_list(...x){
  let [first, rest] = array_first_rest(x);
  return flatten_list(rest, first);};


/////////////////////////////////////////////////////////////
//  FORMS
////////////////////////////////////////////////////////////
// FORMS describe the semantics of LISP programs
// ...

var exp_tag = car;

var exp_body = cdr;

var lookup = (tag) => {
  if (ENV.contains(tag)) return ENV.get(tag);
  return evaluation_error("lookup", "${ tag } NOT FOUND IN LOCAL ENV");};

var subcar = (x, y) => cons(y, cdr(x));
// All forms representing proceedures or values(as opposed to data)
// share the same common structure
// <tagged-expression> := "[", <tag>, <primitive>* | <s-expression>*, "]"

var tagged_exp$ = (exp) => ENV.contains(exp_tag(exp));

var λ = (body, args) => cons("LAMBDA", cons((body || () => null), args));

var λ_fn = cdar;

var λ_args = cddr;

var evl_λ_args = (exp, env) => eval_list(λ_args(exp), env);

var λ$ = (x) => !(!(exp_tag(x) === "LAMBDA") ||
                  !function$(λ_fn(x)) ||
                  nill$(λ_args(exp)));

var apply_λ = (exp, env) => λ_fn(exp).apply(undefined,
                              evl_λ_args(λ_args(exp), env));

var eval_list = function evl_list(exp, env, a=[]){
  if (nill$(exp)) return a;
  return evl_list(cdr(exp), a.concat(eval_exp(car(exp), env)));};

function eval_exp(exp, env){
  if (atom$(exp)) return exp;
  if (tagged_exp$) return evl(
    λ(subcar(exp,
             look_up(exp_tag(x)))),
    env);
  if (λ$(exp)) return apply_λ(exp, env);
  return evaluation_error("evl", "UNRECOGNIZED EXPRESSION");}
