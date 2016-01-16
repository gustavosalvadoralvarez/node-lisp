
// jshint esnext:true

// errors (all interpreter errors thrown)
var interpreter_error = (typ) => (
  (loc, desc) => throw new Error(
    "INTERPRETER ERROR: ${ typ } @ ${ loc } : ${ desc }"));

var evaluation_error = interpreter_error("EVALUATION");

var signature_error = interpreter_error("SIGNATURE");

var type_error = interpreter_error("TYPE");

var value_error = interpreter_error("VALUE");

var syntax_error = interpreter_error("SYNTAX");

var module_error = interpreter_error("MODULE");


var ENV = (() => {
  let global_env = {}
  return {
    get: (sym) => {
      if (sym in global_env) return car(global_env[sym]);
      return undefined;},
    set: (sym, x) => {
      if (sym in global_env) global_env.concat(x);
      global_env[sym] = [x];
      return null;},
    contains: (x) => (x in global_env);
    clear: (sym) => {
      if (sym in global_env) ENV.set(sym, null);},
    delete: (sym) => (delete global_env[sym]),
    back: (sym, y) => {
      if (sym in global_env) {
        let value = ENV.get(sym),
            ix = value.length - y;
        if (ix > 0) return value[y];
        return undefined;}
      return undefined;}
    },
    export: () => {
     let _module = {};
     for (let k in global_env){
       _module[k] = global_env[k];
     }
     return _module;
   },
    require: (x) => {
      let _module = x.export();
      if (_module || !(_module instanceof Object)) return module_error(
        "ENV.require", "MODULE EXPORTS NOT FOUND");
      for (let k in _module){
        ENV.set(k, _module[k]);}}})();

// <tag-symbol> := <symbol>
var tag_symbol = (dict) => (tag) => tag in dict ? dict[tag] : false;

var lookup_tag_symbol = (tag_symbol) => ENV.get(tag_symbol);

var is_tag = (y) => (x) => x in Object.keys(y);

// <variable> := "[" <lable-tag> "]"
var NS = {};

var is_NS_tag = is_tag(NS);

var NS_tag_symbol = tag_symbol(NS);

// <syntax> := "[" <syntax-tag> <expr>+ | <syntax-tag> <primitive>+ | <syntax-tag> "]"
var SNTX = {};

var is_SNTX_tag = is_tag(SNTX);

var SNTX_tag_symbol = tag_symbol(SNTX);

// <data-type> := "[" <data-tag> <exp>* | <data-tag> <primitive>* "]"
var DTS = {};

var is_DTS_tag = is_tag(DTS);

var DTS_tag_symbol = tag_symbol(DTS);

var empty_exp$ = (x) => (undefined$(x) ||
                           !car(x) || eq$(cdr(x), null) ||
                           !primitive$(x[0]));

// reference class identity m expressions (prototypal identity)

var lambda$ = (x) => x.prototype === Function.prototype;

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

// <primitive> := <boolean> | <number> | <string> |
//                <reg-exp> | <symbol> | <set> |
//                <object> | <undefined> | <null>
var primitive$ = (x) => {
  if (string$(x)) return !Symbol.for(x);
  return regexp$(X) ||
         symbol$(X) ||
         boolean$(X) ||
         undefined$(X) ||
         set$(X) ||
         object$(X);};

// primitive m expressions



// atom [X] = atom [(X · null)] = T
// atom [(X · A)] = F
//

// <atom> := "[" <primitive> ["," <null>] "]" | <primitive>

var atomic_symbol = (x) => {
  if (array$(x) && x.length) return x[0];
  return x;};

var atom$ = (x) => {
  if (array$(x)) return x.length < 2 || x[1] === null;
  if (primitive$(x)) return true;
  return false;};


// <s-expression> := "[", <s-expression> | <atom> | <primitive>, [","
//                      <s-expression> | <primitive>], "]"
var sexp = (head, tail) => {
  var exp = [head].concat((tail || null))];
  exp[Symbol.toPrimitive] = () => (env) => evl(exp, env);
  return exp};

// eq$ [X; X] = T
// eq$ [X; A] = F
// eq$ [X; (X · A)] is undefined.
var eq$ = (x, y) => !(!atom$(x) || !atom$(y)) ? undefined : (x[0] === y[0]);

// car [(X · A)] = X
// car [((X · A) · Y )] = (X · A
var car = (x) => atom$(x) ? undefined : x[0];

var cdr = (x) => atom$(x) ? undefined : x[1];

var caar = (x) => car(car(x));

var cadr = (x) => car(cdr(x));

var caddr = (x) => car(cdr(cdr(x)));

var cddr = (x) => cdr(cdr(x));

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
var subst = function(x, y, z, w){
    let c = w ? cons(z, w) : z; // revaritution strategy
    if (atom$(c)) return (eq$(c, y) ? x : z;
    return subst(x, y, car(c), cdr(c));}

// equal [x; y] = [atom [x] ∧ atom [y] ∧ eq$ [x; y]] ∨
//                [¬ atom [x] ∧¬ atom [y] ∧ eq$ual [car [x]; car [y]] ∧
//                 eq$ual [cdr [x]; cdr [y]]]
var equal$ = function equal$(x, y){
  return (atom$(x) && atom$(y) &&
          eq$(x, y)) ||
         (!atom$(x) && !atom$(y) &&
         equal$(car(x), car(y)) &&
         equal$(cdr(x), cdr(y)))};

// null[x] = atom[x] ∧ eq$[x; NIL]
var nill$ = (x) => !(!atom$(x) || !eq(x, null));

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
  return reverse_list(cons(cdr(x), car(x)));
// mutual recursion strategy
var reverse_list = function reverse(x){
  if (!atom$(x)) return x;
  return reverse(cdr(x), rev(car(x)));}
var append = (x, y) =>  {
  if(nill$(x)) return y;
  return reverse(cons(reverse(y), x));

// member[x; y] = ¬null[y] ∧
//               [eq$ual[x; car[y]] ∨
//               member[x; cdr[y]]]
var member$ = function(x, y){
 return  !(nill$(y) || !equal$(x, car(y))) || member$(x, cdr(y));};

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
  return y + list_len(cdr(x));}

var car_pair = (x, y) => cons(car(x), car(y));

var pair = function pair(x, y, z){
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
var assoc = function assoc(x, y){
  if (eq$(caar(y), x)) return cadar(y);
  return assoc(x, cdr(y));
}]

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

var sub_cdr = (x, y) => sublis(x, cdr(y));

var sublis = function sublis(x, y, z){
  let c = z ? cons(y, z) : y;
  if(atom$(c)) return sub2(x, c);
  return sublis(x, sub_car(x, c), sub_cdr(x, c));};

var pairlis = function pairlis(x, y, a){
  return empty$(x) ?
            a :
            cons(cons(car(x), car(y)),
                 pairlis(cdr(x), cdr(y), a));};

// additional m expressions
//
//
var identity = (x) => x;

var not = (x) => bool$(x) && !x || undefined;

var T = () =>  true;

var F = () => false;

var and = function and(n, ...r){
  return n && (r ? and(...r) : true);};

var or = function or(n, ...r){
  return n || (r ? or(...r) : true);};

var xor = function xor(n, ...r){
  return and(or(n, ...r), not(and(n, ...r)));

var sub = function sub(n, ...r){
  return n - (empty$(r) ? 0 : sub(...r));};

var add = function add(n, ...r){
  return n + (empty$(r) ? 0 : add(...r));};

var sub = function sub(n, ...r){
  return n - (empty$(r) ? 0 : sub(...r));};

var mult = function mult(n, ...r){
  return n * (empty$(r) ? 1 : mult(...r));};

var mod = (x, y) => x%y;

var exp = (x, y) => Math.pow(x, y);

var empty$ = (x) => x.length === 0;

var array_first_rest = (x) => return [x.slice(0, 1), x.slice(1)];

var array_to_list = function array_to_list(x, a){
  if(empty$(x)) return a;
  let [first, rest] = array_first_rest(x);
  first.isList = true;
  return array_to_list(rest, cons(a, first));};

var list = function list(...x){
  let [first, rest] = array_first_rest(x);
  first.isList = true;
  return array_to_list(rest, first);};

var list_array = function list_array(x) {
  if (atom$(x)) return symbolic_atom(x);
  return [ ...list_array(car(x)), ...list_array(cdr(x))];};

// Name space, environment and evaluation

// <exp-tag> := <string>
var exp_tag = (x) => car(x);

var env_exp$ = (x) => {
  let tag = exp_tag(x);
  return symbol$(tag) && ENV.contains(tag)};

var tagged_exp$ = (exp) => {
  if ($atom(exp) || nill$(exp)) return false;
  let tag = car(exp);
  return (string$(tag) &&
         (in_keys(tag, NS) ||
          in_keys(tag, SNTX) ||
          in_keys(DTS))) ?
            tag :
            false;};

var list_exp$ = (x) => x.isList || false;

var lambda_exp$ = (x) => car(x) instanceof Function;

var missing$ = (x) => nill$(x) || undefined$(x);

var sub_tag = (exp, y) => return cons(y, cdr(x));

function evl(exp, env){
  if (primitive_exp$(exp)) return exp;
  if (atom$(exp)) return atomic_symbol(exp);
  if (lambda_exp$(exp)) return apply(exp, env);
  if (env_exp$(exp)) return evl(sub_tag(exp, lookup_tag_symbol(exp_tag(exp))));
  if (tagged_exp$(exp)) {
    let tag = exp_tag(exp);
    if (in_keys(SNTX)) return evl(
      sub_tag(
        lookup_tag_symbol(
          SNTX_tag_symbol(exp))
          exp),
      env);
    if (in_keys(DTS)) return evl(
      sub_tag(
        lookup_tag_symbol(
          DTS_tag_symbol(exp))
          exp),
      env);
    if (in_keys(NS)) return evl(
      sub_tag(
        lookup_tag_symbol(
          NS_tag_symbol(exp))
          exp),
      env);}
  if (list_exp$(exp)) return exp.toPrimitive("default");
  if (missing$(exp)) {
    if (missing$(env)) return interpreter_error(
      "EVALUATION ERROR: MISSING EXP AND ENV");
    return evl_env(env);}};


function apply(exp, env){
  let λ = atomic_symbol(exp);
  if (!lambda$(λ)) return evaluation_error("APPLY",
    "EXP MUST BE AN ATOMIC SYMBOL THAT EVALUATES TO A NATIVE FUNCTION");
  let closure = (args) => {
    let bindings = evl(null, args);
    return λ.apply(null, bindings);}
  if (missing$(env)) return closure;
  return closure(env);};


// interpreter m expressions









var define_syntax = (label, mexp, evlexp
/*(x, env) -> evl() || primitive || Attay*/) => {
  var sym = Symbol(label);
  ENV.set(sym, mexp);
  SNTX[label] = sym;
  EVL.set(sym, evlexp);
  return sym;
};

// env is an array, dict implied by spread operator (lexical application)

var type_varructor = (label, type_check, varructor_mexpr) => {
  return (x) => {
    if(type_check(x)) return cons(DTS[label], varructor_mexpr(x));
    interpreter_error("TYPE_ERROR: ${ label } TYPE CHECK FAILED");}};

var define_data_type = (x) => {
  let [label, evlexp, type_check, varructor_mexp] = list_array(x);
  DTS[label] = define_syntax(
                label,
                type_varructor(
                  label, type_check, varructor_mexp),
                evlexp);};

var define_data_types = function define_data_types(x){
  let [first, rest] = [car(x), cdr(x)];
  define_data_type(first);
  if (rest) return define_data_types(rest);};

var evl_primitive = (x, env) => evl(false, env.concat(x));

var tagged_list$ = (x) =>

function evl(x, env=[]){
  if(primitive$(x)) return x;
  if(NS$(x)) return evl(ENV.get(NS[x]), env);
  if(SNTX$(x)) return apply(ENV.get(SNTX[x]), evl(env));


}

var evl_atom = (x, env) => env.concat([evl(x.keys()[0], env));

var evl_list = function evl_list(x, env){
  if(!array$(env)) return interpreter_error(
    "IMPLEMENTATION ERROR: ENV MUST BE AN ARRAY");
  if(primitive$(x)) return evl_primitive(x, env);
  if(atom$(x)) return evl_

}
var _list_of_values = function _list_of_values(x, env){
  if (atom$(x)) return x.keys()[0];
  if (primitive$(x)) return
  return [ ...flatten(evl(car))]
}

var evl_list = function evl_list(x, env){
  if(!array$(env)) return interpreter_error(
    "IMPLEMENTATION ERROR: ENV MUST BE AN ARRAY");
  if(!x || nill$(x)) return env;
  return evl_list(cdr(x), env.concat(evl(car(x), env)));}

var evl_operands = (x, env) => {
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

var set = (label, x) => {
   var sym = Symbol(label);
   ENV.set(sym, x);
   NS[label] = sym;
   return null;};

// DATA
//////////////////////////////////////
// FORM: [DATA-TYPE-TAG, VALUE]


var immutable_tagged_subform = (x) => () => x;
var immutable_tagged_value = (x) => x[1]();

var immutable_data_type = (name, type_check) => list()
var tagged_subform = identity;
var tagged_value = (x) => cdr(x)();




var CORE_DATA_TYPES = list([
  //(LABEL,
  // SUBFORM -> evl -> VALUE,
  // VALUE -> BOOL,
  // FORM -> type_varructor -> SUBFORM)
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




var eval_data_value = (x) => {
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
