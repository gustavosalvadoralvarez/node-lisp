// jshint esnext:true

module.exports = function env_factory(env_arr=[]){
  const _env = {};
  env_arr.prototype.get = (tag) => {
    if (tag in _env) return _env[tag]();
    return undefined;};
  env_arr.prototype.set = (tag, x) => {
    tag = tag instanceof String && tag || tag.toString;
    _env[tag] = () => x;
    return null;};
  env_arr.prototype.unbound_values = () => env_arr.reduce(
    (a, x) => { a.concat(x); return a;}, []);
  env_arr.prototype.contains = (x) => (x in _env);
  env_arr.prototype.delete = (tag) => delete _env[tag];
  env_arr.prototype.export = () => _env;
  env_arr.prototype.require = (x) => {
    let _module = x.export();
    if (_module || !(_module instanceof Object)) return module_error(
      "env.require", "MODULE EXPORTS NOT FOUND");
    for (let k in _module){ _env[k] = _module[k];}};
  return env_arr;};
