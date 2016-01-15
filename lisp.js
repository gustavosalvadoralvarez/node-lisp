
// jshint esnext:true

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

var tagbol$ = (x) => x.prototype === tagbol.prototype;

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
//                <reg-exp> | <tagbol> | <set> |
//                <object> | <undefined> | <null>

var primitive$ = (x) => {
  if (string$(x)) return !tagbol.for(x);
  return regexp$(X) ||
         tagbol$(X) ||
         boolean$(X) ||
         undefined$(X) ||
         set$(X) ||
         function$(x) ||
         object$(X);};

// ATOMS are indivisible data. Since in a LISP code is data and data code,
// functions are both primitive and atomic data like all other data types.
// Syntaxtically an atom is represented by an array with a single item or
// the 'naked' native object instance; Empty arrays are atoms
// <atom> := "[" <primitive> ["," <null>] "]" | <primitive>

var atom$ = (x) => (array$(x) && (!x.length || primitive$(x[0]) ||
                    primitive$(x)));

// LISTS are tree-like structures of nested lists, each of which has only
// two items: a CAR and a CDR (see bellow); Lists are also called s-expressions.
// <s-expression> := "[", <s-expression> | <atom> | <primitive>, [","
//                      <s-expression> | <primitive>], "]"
var cons = (car, cdr) => [car, cdr];

var list$ = (x) => (array$(x) && !atom$(x));

// NILL is true only of empty atoms, i.e. null, and [];
var nill$ = (x) => x === null || (array$(x) && !x.length);

///////////////////////////////////////////////////////////////////////
//  M-EXPRESSIONS
///////////////////////////////////////////////////////////////////////
// M-EXPRESSIONS are proceedures (lambdas, functions) which operate on
// <s-expressions> to produce a <primitive>, <atom> or <s-expression>
// but are not themselves represented are an <s-expression>

var car = (x) => !atom$(x) && x[0] || null;

var cdr = (x) => (!atom(x) && x.length > 1) && x.slice(0) || null;

var caar = (x) => car(car(x));

var cddr = (x) => cdr(cdr(x));

var cadr = (x) => car(cdr(x));

var cdar = (x) => cdr(car(x));

var caddr = (x) => car(cdr(x));

var cdaar = (x) => cdr(car(car(x)));

/////////////////////////////////////////////////////////////
//  FORMS
////////////////////////////////////////////////////////////
// FORMS describe the semantics of LISP programs
// ...

var exp_tag = car;

var exp_body = cdr;

var lookup = (exp, env) => {
  if (env.contains(tag)) return cons(env.get(tag), exp_body(exp));
  return evaluation_error("lookup", "${ tag } NOT FOUND IN LOCAL ENV");};

// All forms representing proceedures or values(as opposed to data)
// share the same common structure
// <tagged-expression> := "[", <tag>, <primitive>* | <s-expression>*, "]"

var tagged_exp$ = (exp, env) => env.contains(exp_tag(exp));

// LAMBDA EXPRESSIONS

var λ = (body, args) => cons("LAMBDA", cons((body || () => null), args));

var λ_fn = cdar;

var λ_args = cddr;

var evl_λ_args = (exp, env) => eval_list(λ_args(exp), env);

var λ$ = (x) => !(!(exp_tag(x) === "LAMBDA") ||
                  !function$(λ_fn(x)) ||
                  nill$(λ_args(exp)));

var apply_λ = (exp, env) => λ_fn(exp).apply(undefined,
                              evl_λ_args(λ_args(exp), env));

// EVALUATION

var eval_atom = (exp, env) => {
  let symbol = atomic_symbol(exp);
  if (env.contains(atomic_symbol)) return env.get(atomic_symbol);
  return atomic_symbol;};

var eval_list = function evl_list(exp, env, a=[]){
  if (nill$(exp)) return a;
  return evl_list(cdr(exp), a.concat(eval_exp(car(exp), env)));};

module.exports = function eval_exp(exp, env){
  if (atom$(exp)) return evl_atom(exp, env);
  if (tagged_exp$(exp, env)) return evl(λ(look_up(exp_tag(x)), env));
  if (λ$(exp)) return apply_λ(exp, env);
  return evaluation_error("evl", "UNRECOGNIZED EXPRESSION");};
