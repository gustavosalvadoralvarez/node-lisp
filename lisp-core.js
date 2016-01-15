// jshint esnext:true


const core = require("./env")();

var interpreter_error = (typ) => {
  return (loc, desc) => {
    let err = new Error("INTERPRETER ERROR: ${ typ } @ ${ loc } : ${ desc }");
    throw err;};};
core.set("error", (t, l, d) => interpreter_error(t)(l, d));

var evaluation_error = interpreter_error("EVALUATION");
core.set("eval-error", evaluation_error);

var signature_error = interpreter_error("SIGNATURE");
core.set("sig-error", signature_error);

var type_error = interpreter_error("TYPE");
core.set("type-error", type_error);

var value_error = interpreter_error("VALUE");
core.set("value-error", value_error);

var syntax_error = interpreter_error("SYNTAX");
core.set("syntax-error", syntax_error);

var module_error = interpreter_error("MODULE");
core.set("module-error", module_error);

var function$ = (x) => x.prototype === Function.prototype;
core.set("function?", function$);

var func = (x) => () => function$(x) && x || type_error("function", x);
core.set('function', func);

var bool$ = (x) => x.prototype === Boolean.prototype;
core.set("boolean?", bool$);

var bool = (x) => () => boolean$(x) && x || type_error("boolean", x);
core.set('boolean', bool);

var string$ = (x) => x.prototype === String.prototype;
core.set("string?", string$);

var str = (x) => () => string$(x) && x || type_error("string", x);
core.set('string', str);

var number$ = (x) => x.prototype === Number.prototype;
core.set("number?", number$);

var num = (x) => () => number$(x) && x || type_error("number", x);
core.set('number', num);

var regexp$ = (x) => x.prototype === RegExp.prototype;
core.set("regexp?", regexp$);

var regexp = (x) => () => regexp$(x) && x || type_error("regexp", x);
core.set('regexp', regexp);

var symbol$ = (x) => x.prototype === Symbol.prototype;
core.set("symbol?", symbol$);

var sym = (x) => () => symbol$(x) && x || type_error("symbol", x);
core.set('symbol', func);

var map$ = (x) => x.prototype === Map.prototype;
core.set("map?", map$);

var map = (x) => () => map$(x) && x || type_error("map", x);
core.set('map', map);

var set$ = (x) => x.prototype === Set.prototype;
core.set("set?", set$);

var set = (x) => () => set$(x) && x || type_error("set", x);
core.set('set', func);

var array$ = (x) => x.prototype === Array.prototype;
core.set("array?", array$);

var object$ = (x) => x.prototype === Object.prototype;
core.set("object?", object$);

var obj = (x) => () => object$(x) && x || type_error("object", x);
core.set('object', obj);

var undefined$ = (x) => x === undefined;
core.set("undefined?", undefined$);

var undef = (x) => () => undefined;
core.set('undefined', undef);

var null$ = (x) => x === null;
core.set("null?", null$);

var nul = (x) => () => null;
core.set('nul', nul);

var primitive$ = (x) => {
  if (string$(x)) return !tagbol.for(x);
  return regexp$(X) ||
         tagbol$(X) ||
         boolean$(X) ||
         undefined$(X) ||
         set$(X) ||
         function$(x) ||
         object$(X);};
core.set("primitive?", primitive$);

var array_first = (x) => {
  if (x.length) return x[0];
  return undefined;};

var atom$ = (x) => (array$(x) && (!x.length || primitive$(array_first(x))) ||
                    primitive$(x));
core.set("atom?", atom$);

var cons = (car, cdr) => [car, cdr];
core.set("cons", cons);

var make_list = function make_list(x, a){
  if (nill$(x)) return a;
  return make_list(x.slice(1), cons(a, x[0]));};

var list = (...x) => make_list(x.slice(1), x[0]);
core.set("list", list);

var list$ = (x) => (array$(x) && !atom$(x));
core.set("list?", list$);

var nill$ = (x) => null$(x) || (array$(x) && !x.length);
core.set("nill?", nill$);

var car = (x) => !atom$(x) && x[0] || null;
core.set("car", car);

var cdr = (x) => (!atom(x) && x.length > 1) && x.slice(0) || null;
core.set("cdr", cdr);

var caar = (x) => car(car(x));
core.set("caar", caar);

var cddr = (x) => cdr(cdr(x));
core.set("cddr", cddr);

var cadr = (x) => car(cdr(x));
core.set("cadr", cadr);

var cdar = (x) => cdr(car(x));
core.set("cdar", cdar);

var caddr = (x) => car(cdr(x));
core.set("caddr", caddr);

var cdaar = (x) => cdr(car(car(x)));
core.set("cdaar", cdaar);

var quote = (x) => () => x;
core.set("'", quote);

var first_primitive = function ff(x){
  if (atom$(x)) return x[0];
  return ff(car(x));};
core.set("fp", first_primitive);

var last_primitive = function ll(x){
  if (atom$(x)) return x[0];
  return ll(cdr(x));};
core.set("lp", last_primitive);

var subst = function subst(x, y, z, w){
  let c = w ? cons(z, w) : z;
  if (atom$(c)) return (eq$(c, y) ? x : z);
  return subst(x, y, car(c), cdr(c));};
core.set("subst", subst);

var equal$ = function equal$(x, y){
  return (atom$(x) && atom$(y) &&
          eq$(x, y)) ||
         (!atom$(x) && !atom$(y) &&
         equal$(car(x), car(y)) &&
         equal$(cdr(x), cdr(y)));};
core.set("equal?", equal$);

var rev = (x) => {
  return reverse_list(cons(cdr(x), car(x)));};

var reverse_list = function reverse(x){
  if (atom$(x)) return x;
  return reverse(cdr(x), rev(car(x)));};
core.set("reverse", reverse_list);

var append = (x, y) =>  {
  if(nill$(x)) return y;
  return reverse(cons(reverse(y), x));};
core.set("append", first_primitive);

var member$ = function(x, y){
  return!(nill$(y) || !equal$(x, car(y))) || member$(x, cdr(y));};
core.set("member?", member$);

var list_len = function list_len(x, y=0){
  return y + list_len(cdr(x));};
core.set("len", member$);

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
core.set("pair?", member$);

var sub2 = function(x, z){
  if (nill$(x)) return y;
  if (eq$(caar(x), z)) return cadar(x);
  return sub2(cdr(x), z);};

var sub_car = (x, y) => sublis(x, car(y));

var sub_cdr = (x, y) => sublis(x, cdr(y));

var sublis = function sublis(x, y, z){
  let c = z ? cons(y, z) : y;
  if(atom$(c)) return sub2(x, c);
  return sublis(x, sub_car(x, c), sub_cdr(x, c));};
core.set("sublist", sublist);

var pairlis = function pairlis(x, y, a){
  return empty$(x) ?
            a :
            cons(cons(car(x), car(y)),
                 pairlis(cdr(x), cdr(y), a));};
core.set("pairlis", pairlis);

var identity = (x) => x;
core.set("identity", identity);

var not = (x) => bool$(x) && !x || undefined;
core.set("not", not);

var and = function and(n, ...r){
 return n && (r ? and(...r) : true);};
core.set("and", sublist);

var or = function or(n, ...r){
 return n || (r ? or(...r) : true);};
core.set("or", or);

var xor = function xor(n, ...r){
 return and(or(n, ...r), not(and(n, ...r)));};
core.set("xor", xor);

var sub = function sub(n, ...r){
 return n - (r ? sub(...r) : 0);};
core.set("-", sub);

var add = function add(n, ...r){
 return n + (r ? sub(...r) : 0);};
core.set("+", add);

var mult = function mult(n, ...r){
 return n * (r ? mult(...r) : 1);};
core.set("*", mult);

var divd = function divd(n, ...r){
 return n / (r ? divd(...r) : 1);};
core.set("/", sublist);

var mod = (x, y) => x%y;
core.set("mod", sublist);

var pow = (x, y) => Math.pow(x, y);
core.set("pow", sublist);

var array_first_rest = (x) => [x[0] , x.slice(1)];

var flatten_list = function flatten_list(x, a){
  if(nill$(x)) return a;
  let [first, rest] = array_first_rest(x);
  return flatten_list(rest, cons(a, first));};
core.set("flatten", sublist);

var array_to_list = function array_to_list(...x){
  let [first, rest] = array_first_rest(x);
  return flatten_list(rest, first);};
core.set("as-list", sublist);

module.exports = core;
