
// jshint esnext:true

// errors (all interpreter errors thrown)

const interpreter_error = (typ) => (
  (loc, desc) => throw new Error(
    "INTERPRETER ERROR: ${ typ } @ ${ loc } : ${ desc }"));

const evaluation_error = interpreter_error("EVALUATION");

const signature_error = interpreter_error("SIGNATURE");

const type_error = interpreter_error("TYPE");

const value_error = interpreter_error("VALUE");

const syntax_error = interpreter_error("SYNTAX");


// reference class identity m expressions (prototypal identity)

const lambda$ = (x) => x.prototype === Function.prototype;

const bool$ = (x) => x.prototype === Boolean.prototype;

const string$ = (x) => x.prototype === String.prototype;

const number$ = (x) => x.prototype === Number.prototype;

const regexp$ = (x) => x.prototype === RegExp.prototype;

const symbol$ = (x) => x.prototype === Symbol.prototype;

const map$ = (x) => x.prototype === Map.prototype;

const set$ = (x) => x.prototype === Set.prototype;

const array$ = (x) => x.prototype === Array.prototype;

const object$ = (x) => x.prototype === Object.prototype;

const undefined$ = (x) => x === undefined;

const null$ = (x) => x === null;

// <primitive> := <boolean> | <number> | <string> |
//                <reg-exp> | <symbol> | <set> |
//                <object> | <undefined> | <null>
const primitive$ = (x) => number$(X) ||
                          string$(X) ||
                          regexp$(X) ||
                          symbol$(X) ||
                          boolean$(X) ||
                          undefined$(X) ||
                          set$(X) ||
                          object$(X);

// primitive m expressions

// <s-expression> := "[" <s-expression> | <atom> | <primitive> ","
//                      [<s-expression> | <primitive>] "]"
const sexpr = (head, tail) => [head].concat((tail || []))];

// <atom> := "[" <primitive> ["," <null>] "]" | <primitive>
const atom = (x) => [x];

const cons = sexpr;

// atom [X] = atom [(X · null)] = T
// atom [(X · A)] = F
const atom$ = (x) => {
  if (array$(x)) return x.length < 2 || x[1] === null;
  if (primitive$(x)) return true;
  return false;};

// eq$ [X; X] = T
// eq$ [X; A] = F
// eq$ [X; (X · A)] is undefined.
const eq$ = (x, y) => !(!atom$(x) || !atom$(y)) ? undefined : (x[0] === y[0]);

// car [(X · A)] = X
// car [((X · A) · Y )] = (X · A
const car = (x) => atom$(x) ? undefined : x[0];

const cdr = (x) => atom$(x) ? undefined : x[1];

const caar = (x) => car(car(x));

const cadr = (x) => car(cdr(x));

const caddr = (x) => car(cdr(cdr(x)));

const cddr = (x) => cdr(cdr(x));

// ff[x] = [atom[x] → x; T → ff[car[x]]]
const ff = function ff(x){
  return (atom$(x) ?
            x[0]:
            ff(car(x)))};

// subst [x; y; z] = [atom [z] →
//                     [eq$ [z; y] → x;
//                     T → z];
//                    T →
//                     cons [subst [x; y; car [z]]; subst [x; y; cdr [z]]]]
// const subst = function subst(x, y, z){
//   return (atom$(z) ?
//             (eq$(z, y) ? x : z) :
//             cons(subst(x, y, car(z),
//                subst(x, y, cdr(z)))))};
// native tail-recursive implementation (for performance)
const subst = function(x, y, z, w){
    let c = w ? cons(z, w) : z; // reconstitution strategy
    if (atom$(c)) return (eq$(c, y) ? x : z;
    return subst(x, y, car(c), cdr(c));}

// eq$ual [x; y] = [atom [x] ∧ atom [y] ∧ eq$ [x; y]] ∨
//                [¬ atom [x] ∧¬ atom [y] ∧ eq$ual [car [x]; car [y]] ∧
//                 eq$ual [cdr [x]; cdr [y]]]
const equal$ = function eq$ual(x, y){
  return (atom$(x) && atom$(y) &&
          eq$(x, y)) ||
         (!atom$(x) && !atom$(y) &&
         equal(car(x), car(y)) &&
         equal(cdr(x), cdr(y)))};

// null[x] = atom[x] ∧ eq$[x; NIL]
const nill$ = (x) => !(!atom$(x) || !eq(x, null));

// append [x; y] = [null[x] → y;
//                  T → cons [car [x];
//                            append [cdr [x]; y]]]
// const append = function append(x, y){
//   return (nill$(x) ?
//             y :
//             cons(car(x),
//                  append(cdr(x), y))))};
// native tail recursive implementation for performance
const rev = (x) => {
  return reverse_list(cons(cdr(x), car(x)));
// mutual recursion strategy
const reverse_list = function reverse(x){
  if (!atom$(x)) return x;
  return reverse(cdr(x), rev(car(x)));}
const append = (x, y) =>  {
  if(nill$(x)) return y;
  return reverse(cons(reverse(y), x));

// member[x; y] = ¬null[y] ∧
//               [eq$ual[x; car[y]] ∨
//               member[x; cdr[y]]]
const member$ = function(x, y){
 return  !(nill$(y) || !equal$(x, car(y))) || member$(x, cdr(y));}

// pair[x; y] = [null[x]∧null[y] → NIL;
//               ¬atom[x]∧¬atom[y] → cons[list[car[x]; car[y]];
//               pair[cdr[x]; cdr[y]]]
// const pair = function pair(x, y){
//   return nill$(x) && nill$(y) ?
//             null :
//             !(!atom$(x) || !atom$(y)) ?
//                 cons(list(car(x), car(y)) :
//                      pair(cdr(x), cdr(y)))};
// native tail recursive implementation
const list_len = function list_len(x, y=0){
  return y + list_len(cdr(x));}

const car_pair = (x, y) => cons(car(x), car(y));

const pair = function pair(x, y, z){
  if (nill$(x) && nill$(y)) return z;
  if (!z){
    let [len_x, len_y] = [list_len(x), list_len(y)];
    if (!(eq(len_x, len_y))) return signature_error(
      "PAIR",
      "X AND Y MUST BE OF SAME LENGTH, CURRENT: ${ len_x } ',' ${ len_y }");
    return pair(cdr(x), cdr(y), car_pair(x, y));
  return pair(cdr(x), cdr(y), cons(z, car_pair(x, y)));};

// assoc[x; y] = eq$[caar[y]; x] → cadar[y];
//               T → assoc[x; cdr[y]]]
const assoc = function assoc(x, y){
  if (eq$(caar(y), x)) return cadar(y);
  return assoc(x, cdr(y));
}]

// sub2[x; z] = [null[x] → z;
//               eq$[caar[x]; z] → cadar[x];
//              T → sub2[cdr[x]; z]]
const sub2 = function(x, z){
  if (nill$(x)) return y;
  if (eq$(caar(x), z)) return cadar(x);
  return sub2(cdr(x), z);};


// sublis[x; y] = [atom[y] → sub2[x; y];
//                T → cons[sublis[x; car[y]]; sublis[x; cdr[y]]]
// const sublis = function sublis(x, y){
//   return atom$(y) ?
//             sub2(x, y) :
//             cons(sublis(x, car(y),
//                  sublis(x, cdr(y))));};
// native implementation
const sub_car = (x, y) => sublis(x, car(y));

const sub_cdr = (x, y) => sublis(x, cdr(y));

const sublis = function sublis(x, y, z){
  let c = z ? cons(y, z) : y;
  if(atom$(c)) return sub2(x, c);
  return sublis(x, sub_car(x, c), sub_cdr(x, c));}

const pairlis = function pairlis(x, y, a){
  return empty$(x) ?
            a :
            cons(cons(car(x), car(y)),
                 pairlis(cdr(x), cdr(y), a));};


// additional m expressions
//
const identity = (x) => x;

const atomic_symbol = (x) => {
  if (atom$(x)) return x[0];
  return undefined;
};

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

const empty$ = (x) => x.length === 0;

const array_to_list = function array_to_list(x, a){
  if(empty$(x)) return a;
  return array_to_list(x.slice(1), cons(a, x[0]));};

const list = function list(...x){
  return array_to_list(x.slice(1), x[0]);};

const list_array = function list_array(x) {
  if (atom$(x)) return symbolic_atom(x);
  return [ ...list_array(car(x)), ...list_array(cdr(x))];};


const cond = function cond(x){
  // FORM [[pred, ]]

}




const proc_body = (x) => cdr(x);
const proc_operator = (x) => car(x)
const apply__proc = (x, env) => (
  proc_operator(x).apply(null, evl(proc_body(x), env)));


["LAMBDA", (x, y z) => (function(){
  apply(cond, [apply(eq, [x, y]), z,x]);
})()]



["LAMBDA", ['x', 'y', 'z'], [
  ['IF' ['=', 'x', 'y'],
        'z'
        'x']]][1, 2, 3]


const first_item = (x) => x[0];

const last_item = (x) => x.slice(-1)[0];


// Name space, environment and evaluation

const ENV = (() => {
  let global_env = {}
  return {
    get: (sym) => {
      if (sym in global_env) return last_item(global_env.get(sym));
      return undefined},
    set: (sym, x) => {
      if (sym in global_env) global_env.concat(x);
      global_env[sym] = [x];
      return null;}
    };
  })();

// <exp-tag> := <string>
const exp_tag = (x) => car(x);

const tagged_exp$ = (exp) => {
  if ($atom(exp) || nill$(exp)) return false;
  let tag = car(exp);
  return (string$(tag) &&
         (in_keys(tag, NS) ||
          in_keys(tag, SNTX) ||
          in_keys(DTS))) ?
            tag :
            false;}

// <tag-symbol> := <symbol>
const tag_symbol = (dict) => (tag) => tag in dict ? dict[tag] : false;

const lookup_tag_symbol = (tag_symbol) => ENV.get(tag_symbol);

const is_tag = (y) => (x) => x in Object.keys(y);

// <variable> := "[" <lable-tag> "]"
const NS = {};

const is_NS_tag = is_tag(NS);

const NS_tag_symbol = tag_symbol(NS);

// <syntax> := "[" <syntax-tag> <expr>+ | <syntax-tag> <primitive>+ | <syntax-tag> "]"
const SNTX = {};

const is_SNTX_tag = is_tag(SNTX);

const SNTX_tag_symbol = tag_symbol(SNTX);

// <data-type> := "[" <data-tag> <exp>* | <data-tag> <primitive>* "]"
const DTS = {};

const is_DTS_tag = is_tag(DTS);

const DTS_tag_symbol = tag_symbol(DTS);

const empty_exp$ = (x) => (undefined$(x) ||
                           !car(x) || eq$(cdr(x), null) ||
                           !primitive$(x[0]));

const lambda_exp$ = (x) => car(x) instanceof Function;

function evl(exp, env){
  if (primitive_exp$(exp)) return exp;
  if (tagged_exp$(exp)) {
    let tag = exp_tag(exp);
    if (in_keys(SNTX)) return evl(
      subst(
        lookup_tag_symbol(
          SNTX_tag_symbol(exp)),
          tag,
          exp),
      env);
    if (in_keys(DTS)) return evl(
      subst(
        lookup_tag_symbol(
          DTS_tag_symbol(exp)),
          tag,
          exp),
      env);
    if (in_keys(NS)) return evl(
      subst(
        lookup_tag_symbol(
          SNTX_tag_symbol(exp)),
          tag,
          exp),
      env);
  }
  if (list_exp$(exp)) return evl_list_form(exp, env);
  if (atom$(exp)) return evl_atom(exp);
  if (lambda_exp$(exp)) return apply(exp, env);
  if (empty_exp$(exp)) return empty_exp$(env) ?
    interpreter_error("EVALUATION ERROR: EMPTY EXP AND ENV") :
    evl_env(env);
};

function apply(exp, env){
  return function (...args){
    return x[0].apply(null, evl([], env));
  }
}


// interpreter m expressions









const define_syntax = (label, mexp, evlexp
/*(x, env) -> evl() || primitive || Attay*/) => {
  const sym = Symbol(label);
  ENV.set(sym, mexp);
  SNTX[label] = sym;
  EVL.set(sym, evlexp);
  return sym;
};

// env is an array, dict implied by spread operator (lexical application)

const type_constructor = (label, type_check, constructor_mexpr) => {
  return (x) => {
    if(type_check(x)) return cons(DTS[label], constructor_mexpr(x));
    interpreter_error("TYPE_ERROR: ${ label } TYPE CHECK FAILED");}};

const define_data_type = (x) => {
  let [label, evlexp, type_check, constructor_mexp] = list_array(x);
  DTS[label] = define_syntax(
                label,
                type_constructor(
                  label, type_check, constructor_mexp),
                evlexp);};

const define_data_types = function define_data_types(x){
  let [first, rest] = [car(x), cdr(x)];
  define_data_type(first);
  if (rest) return define_data_types(rest);};

const evl_primitive = (x, env) => evl(false, env.concat(x));

const tagged_list$ = (x) =>

function evl(x, env=[]){
  if(primitive$(x)) return x;
  if(NS$(x)) return evl(ENV.get(NS[x]), env);
  if(SNTX$(x)) return apply(ENV.get(SNTX[x]), evl(env));


}

const evl_atom = (x, env) => env.concat([evl(x.keys()[0], env));

const evl_list = function evl_list(x, env){
  if(!array$(env)) return interpreter_error(
    "IMPLEMENTATION ERROR: ENV MUST BE AN ARRAY");
  if(primitive$(x)) return evl_primitive(x, env);
  if(atom$(x)) return evl_

}
const _list_of_values = function _list_of_values(x, env){
  if (atom$(x)) return x.keys()[0];
  if (primitive$(x)) return
  return [ ...flatten(evl(car))]
}

const evl_list = function evl_list(x, env){
  if(!array$(env)) return interpreter_error(
    "IMPLEMENTATION ERROR: ENV MUST BE AN ARRAY");
  if(!x || nill$(x)) return env;
  return evl_list(cdr(x), env.concat(evl(car(x), env)));}

const evl_operands = (x, env) => {
  if(!array$(env)) return interpreter_error(
    "IMPLEMENTATION ERROR: ENV MUST BE AN ARRAY");
  return evl_list(append(cdr(x), car(x)), env);}

function evl(exp, evn=[]){
  if (primitive$(exp)) return exp;
  let [expcar, expcdr] = [car(exp), cdr(exp)];
  if(SNTX$(expcar)) return EVL.get(SNTX[expcar])(exp, env);
  if($lambda(exprcar)) return apply(expcar, evl_operands(expcdr), env)
  ((application? exp)
   (apply (eval (operator exp) env)
          (list-of-values (operands exp) env)))
}

function apply(λ, env){
  return λ(...env);
}

const set = (label, x) => {
   const sym = Symbol(label);
   ENV.set(sym, x);
   NS[label] = sym;
   return null;};

// DATA
//////////////////////////////////////
// FORM: [DATA-TYPE-TAG, VALUE]


const immutable_tagged_subform = (x) => () => x;
const immutable_tagged_value = (x) => x[1]();

const immutable_data_type = (name, type_check) => list()
const tagged_subform = identity;
const tagged_value = (x) => cdr(x)();




const CORE_DATA_TYPES = list([
  //(LABEL,
  // SUBFORM -> evl -> VALUE,
  // VALUE -> BOOL,
  // FORM -> type_constructor -> SUBFORM)
  //
  // immutable reference types
  list(["number", immutable_tagged_value, number$, immutable_tagged_subform]),
  list(["string", immutable_tagged_value, string$, immutable_tagged_subform]),
  list(["symbol", immutable_tagged_value, symbol$, immutable_tagged_subform]),
  list(["regexp", immutable_tagged_value, regexp$, immutable_tagged_subform]),
  list(["true", immutable_tagged_value, () => (true), () => (true)]),
  list(["false", immutable_tagged_vaue, () => (true),  () => (false)]),
  list(["undefined", immutable_tagged_value, () => (true), () => (undefined)]),
  // immutable collections
  list(["set", immutable_tagged_value, set$,
        (...args) => (immutable_tagged_subform(Set(args)))]),
  list(["array", immutable_tagged_value, array$, (...args) => (immutable_tagged_subform(args))]),
  list(["object", immutable_tagged_value, (...x) => (x.length && x.length%2 === 0)]),
            (...args) => (immutable_tagged_subform(args.reduce((ac, v, i, arr) => {
                                              if (i%2) ac[v] = arr[i+1];
                                              return ac; }, {})))]),
  // lisp primitives
  list(["lambda", tagged_value, lambda$, tagged_subform]),
  list(["atom", tagged_value, atom$, (x) => (atom(x)))]),
  list(["list",  tagged_value, array$, list]),
  list(["quote", tagged_value, () => (true), tagged_subform]),
  list(["label", tagged_value, string$, tagged_subform])]);




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
