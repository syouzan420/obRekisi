"use strict";
var __haste_prog_id = '0870242b5abba043a99bf7360bb15a39b3d0e101377808bdeaf92d209ad912de';
var __haste_script_elem = typeof document == 'object' ? document.currentScript : null;
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined' && typeof global !== 'undefined') window = global;
window['__haste_crypto'] = window.crypto || window.msCrypto;
if(window['__haste_crypto'] && !window['__haste_crypto'].subtle && window.crypto.webkitSubtle) {
    window['__haste_crypto'].subtle = window.crypto.webkitSubtle;
}

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(738919189, 2683596561, true)
  var y = new Long(3648966346, 573393410, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var len = buffer.byteLength;
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': len % 2 ? null : new Int16Array(buffer)
        , 'i32': len % 4 ? null : new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': len % 2 ? null : new Uint16Array(buffer)
        , 'w32': len % 4 ? null : new Uint32Array(buffer)
        , 'f32': len % 4 ? null : new Float32Array(buffer)
        , 'f64': len % 8 ? null : new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __isUndef = function(x) {return typeof x == 'undefined';}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

/* Code for creating and querying the static pointer table. */
window.__hs_spt = [];

function __spt_insert(ptr) {
    ptr = E(B(ptr));
    var ks = [ (ptr.a.a.low>>>0).toString(16)
             , (ptr.a.a.high>>>0).toString(16)
             , (ptr.a.b.low>>>0).toString(16)
             , (ptr.a.b.high>>>0).toString(16)
             ]
    var key = ks.join();
    window.__hs_spt[key] = ptr;
}

function hs_spt_lookup(k) {
    var ks = [ k['v']['w32'][0].toString(16)
             , k['v']['w32'][1].toString(16)
             , k['v']['w32'][2].toString(16)
             , k['v']['w32'][3].toString(16)
             ]
    var key = ks.join();
    return window.__hs_spt[key];
}

var _0=function(_1,_2,_){var _3=B(A1(_1,_)),_4=B(A1(_2,_));return _3;},_5=function(_6,_7,_){var _8=B(A1(_6,_)),_9=B(A1(_7,_));return new T(function(){return B(A1(_8,_9));});},_a=function(_b,_c,_){var _d=B(A1(_c,_));return _b;},_e=function(_f,_g,_){var _h=B(A1(_g,_));return new T(function(){return B(A1(_f,_h));});},_i=new T2(0,_e,_a),_j=function(_k,_){return _k;},_l=function(_m,_n,_){var _o=B(A1(_m,_));return new F(function(){return A1(_n,_);});},_p=new T5(0,_i,_j,_5,_l,_0),_q=new T(function(){return B(unCStr("base"));}),_r=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_s=new T(function(){return B(unCStr("IOException"));}),_t=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_q,_r,_s),_u=__Z,_v=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_t,_u,_u),_w=function(_x){return E(_v);},_y=function(_z){return E(E(_z).a);},_A=function(_B,_C,_D){var _E=B(A1(_B,_)),_F=B(A1(_C,_)),_G=hs_eqWord64(_E.a,_F.a);if(!_G){return __Z;}else{var _H=hs_eqWord64(_E.b,_F.b);return (!_H)?__Z:new T1(1,_D);}},_I=function(_J){var _K=E(_J);return new F(function(){return _A(B(_y(_K.a)),_w,_K.b);});},_L=new T(function(){return B(unCStr(": "));}),_M=new T(function(){return B(unCStr(")"));}),_N=new T(function(){return B(unCStr(" ("));}),_O=function(_P,_Q){var _R=E(_P);return (_R._==0)?E(_Q):new T2(1,_R.a,new T(function(){return B(_O(_R.b,_Q));}));},_S=new T(function(){return B(unCStr("interrupted"));}),_T=new T(function(){return B(unCStr("resource vanished"));}),_U=new T(function(){return B(unCStr("unsatisified constraints"));}),_V=new T(function(){return B(unCStr("user error"));}),_W=new T(function(){return B(unCStr("permission denied"));}),_X=new T(function(){return B(unCStr("illegal operation"));}),_Y=new T(function(){return B(unCStr("end of file"));}),_Z=new T(function(){return B(unCStr("resource exhausted"));}),_10=new T(function(){return B(unCStr("resource busy"));}),_11=new T(function(){return B(unCStr("does not exist"));}),_12=new T(function(){return B(unCStr("already exists"));}),_13=new T(function(){return B(unCStr("timeout"));}),_14=new T(function(){return B(unCStr("unsupported operation"));}),_15=new T(function(){return B(unCStr("hardware fault"));}),_16=new T(function(){return B(unCStr("inappropriate type"));}),_17=new T(function(){return B(unCStr("invalid argument"));}),_18=new T(function(){return B(unCStr("failed"));}),_19=new T(function(){return B(unCStr("protocol error"));}),_1a=new T(function(){return B(unCStr("system error"));}),_1b=function(_1c,_1d){switch(E(_1c)){case 0:return new F(function(){return _O(_12,_1d);});break;case 1:return new F(function(){return _O(_11,_1d);});break;case 2:return new F(function(){return _O(_10,_1d);});break;case 3:return new F(function(){return _O(_Z,_1d);});break;case 4:return new F(function(){return _O(_Y,_1d);});break;case 5:return new F(function(){return _O(_X,_1d);});break;case 6:return new F(function(){return _O(_W,_1d);});break;case 7:return new F(function(){return _O(_V,_1d);});break;case 8:return new F(function(){return _O(_U,_1d);});break;case 9:return new F(function(){return _O(_1a,_1d);});break;case 10:return new F(function(){return _O(_19,_1d);});break;case 11:return new F(function(){return _O(_18,_1d);});break;case 12:return new F(function(){return _O(_17,_1d);});break;case 13:return new F(function(){return _O(_16,_1d);});break;case 14:return new F(function(){return _O(_15,_1d);});break;case 15:return new F(function(){return _O(_14,_1d);});break;case 16:return new F(function(){return _O(_13,_1d);});break;case 17:return new F(function(){return _O(_T,_1d);});break;default:return new F(function(){return _O(_S,_1d);});}},_1e=new T(function(){return B(unCStr("}"));}),_1f=new T(function(){return B(unCStr("{handle: "));}),_1g=function(_1h,_1i,_1j,_1k,_1l,_1m){var _1n=new T(function(){var _1o=new T(function(){var _1p=new T(function(){var _1q=E(_1k);if(!_1q._){return E(_1m);}else{var _1r=new T(function(){return B(_O(_1q,new T(function(){return B(_O(_M,_1m));},1)));},1);return B(_O(_N,_1r));}},1);return B(_1b(_1i,_1p));}),_1s=E(_1j);if(!_1s._){return E(_1o);}else{return B(_O(_1s,new T(function(){return B(_O(_L,_1o));},1)));}}),_1t=E(_1l);if(!_1t._){var _1u=E(_1h);if(!_1u._){return E(_1n);}else{var _1v=E(_1u.a);if(!_1v._){var _1w=new T(function(){var _1x=new T(function(){return B(_O(_1e,new T(function(){return B(_O(_L,_1n));},1)));},1);return B(_O(_1v.a,_1x));},1);return new F(function(){return _O(_1f,_1w);});}else{var _1y=new T(function(){var _1z=new T(function(){return B(_O(_1e,new T(function(){return B(_O(_L,_1n));},1)));},1);return B(_O(_1v.a,_1z));},1);return new F(function(){return _O(_1f,_1y);});}}}else{return new F(function(){return _O(_1t.a,new T(function(){return B(_O(_L,_1n));},1));});}},_1A=function(_1B){var _1C=E(_1B);return new F(function(){return _1g(_1C.a,_1C.b,_1C.c,_1C.d,_1C.f,_u);});},_1D=function(_1E){return new T2(0,_1F,_1E);},_1G=function(_1H,_1I,_1J){var _1K=E(_1I);return new F(function(){return _1g(_1K.a,_1K.b,_1K.c,_1K.d,_1K.f,_1J);});},_1L=function(_1M,_1N){var _1O=E(_1M);return new F(function(){return _1g(_1O.a,_1O.b,_1O.c,_1O.d,_1O.f,_1N);});},_1P=44,_1Q=93,_1R=91,_1S=function(_1T,_1U,_1V){var _1W=E(_1U);if(!_1W._){return new F(function(){return unAppCStr("[]",_1V);});}else{var _1X=new T(function(){var _1Y=new T(function(){var _1Z=function(_20){var _21=E(_20);if(!_21._){return E(new T2(1,_1Q,_1V));}else{var _22=new T(function(){return B(A2(_1T,_21.a,new T(function(){return B(_1Z(_21.b));})));});return new T2(1,_1P,_22);}};return B(_1Z(_1W.b));});return B(A2(_1T,_1W.a,_1Y));});return new T2(1,_1R,_1X);}},_23=function(_24,_25){return new F(function(){return _1S(_1L,_24,_25);});},_26=new T3(0,_1G,_1A,_23),_1F=new T(function(){return new T5(0,_w,_26,_1D,_I,_1A);}),_27=new T(function(){return E(_1F);}),_28=function(_29){return E(E(_29).c);},_2a=__Z,_2b=7,_2c=function(_2d){return new T6(0,_2a,_2b,_u,_2d,_2a,_2a);},_2e=function(_2f,_){var _2g=new T(function(){return B(A2(_28,_27,new T(function(){return B(A1(_2c,_2f));})));});return new F(function(){return die(_2g);});},_2h=function(_2i,_){return new F(function(){return _2e(_2i,_);});},_2j=function(_2k){return new F(function(){return A1(_2h,_2k);});},_2l=function(_2m,_2n,_){var _2o=B(A1(_2m,_));return new F(function(){return A2(_2n,_2o,_);});},_2p=new T5(0,_p,_2l,_l,_j,_2j),_2q=function(_2r){return E(_2r);},_2s=new T2(0,_2p,_2q),_2t=new T2(0,_2s,_j),_2u=0,_2v=function(_){return _2u;},_2w=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_2x=new T(function(){return eval("(function(ctx){ctx.save();})");}),_2y=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_2z=function(_2A,_2B,_2C,_2D,_){var _2E=__app1(E(_2x),_2D),_2F=__app3(E(_2y),_2D,E(_2A),E(_2B)),_2G=B(A2(_2C,_2D,_)),_2H=__app1(E(_2w),_2D);return new F(function(){return _2v(_);});},_2I=new T(function(){return eval("(function(e){e.width = e.width;})");}),_2J=new T1(0,10),_2K=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_2L=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_2M=function(_2N,_2O,_){var _2P=__app1(E(_2K),_2O),_2Q=B(A2(_2N,_2O,_)),_2R=__app1(E(_2L),_2O);return new F(function(){return _2v(_);});},_2S=new T(function(){return eval("(function(ctx, x, y, radius, fromAngle, toAngle){ctx.arc(x, y, radius, fromAngle, toAngle);})");}),_2T=0,_2U=6.283185307179586,_2V=new T(function(){return eval("(function(ctx,x,y){ctx.moveTo(x,y);})");}),_2W=function(_2X,_2Y,_2Z,_30,_){var _31=__app3(E(_2V),_30,_2X+_2Z,_2Y),_32=__apply(E(_2S),new T2(1,_2U,new T2(1,_2T,new T2(1,_2Z,new T2(1,_2Y,new T2(1,_2X,new T2(1,_30,_u)))))));return new F(function(){return _2v(_);});},_33=function(_34,_){return new F(function(){return _2W(0,0,3,E(_34),_);});},_35=function(_36,_){return new F(function(){return _2M(_33,E(_36),_);});},_37=",",_38="rgba(",_39=new T(function(){return toJSStr(_u);}),_3a="rgb(",_3b=")",_3c=new T2(1,_3b,_u),_3d=function(_3e){var _3f=E(_3e);if(!_3f._){var _3g=jsCat(new T2(1,_3a,new T2(1,new T(function(){return String(_3f.a);}),new T2(1,_37,new T2(1,new T(function(){return String(_3f.b);}),new T2(1,_37,new T2(1,new T(function(){return String(_3f.c);}),_3c)))))),E(_39));return E(_3g);}else{var _3h=jsCat(new T2(1,_38,new T2(1,new T(function(){return String(_3f.a);}),new T2(1,_37,new T2(1,new T(function(){return String(_3f.b);}),new T2(1,_37,new T2(1,new T(function(){return String(_3f.c);}),new T2(1,_37,new T2(1,new T(function(){return String(_3f.d);}),_3c)))))))),E(_39));return E(_3h);}},_3i="strokeStyle",_3j="fillStyle",_3k=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_3l=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_3m=function(_3n,_3o){var _3p=new T(function(){return B(_3d(_3n));});return function(_3q,_){var _3r=E(_3q),_3s=E(_3j),_3t=E(_3k),_3u=__app2(_3t,_3r,_3s),_3v=E(_3i),_3w=__app2(_3t,_3r,_3v),_3x=E(_3p),_3y=E(_3l),_3z=__app3(_3y,_3r,_3s,_3x),_3A=__app3(_3y,_3r,_3v,_3x),_3B=B(A2(_3o,_3r,_)),_3C=String(_3u),_3D=__app3(_3y,_3r,_3s,_3C),_3E=String(_3w),_3F=__app3(_3y,_3r,_3v,_3E);return new F(function(){return _2v(_);});};},_3G=new T3(0,200,100,0),_3H=new T(function(){return B(_3m(_3G,_35));}),_3I=new T(function(){return B(unCStr("base"));}),_3J=new T(function(){return B(unCStr("Control.Exception.Base"));}),_3K=new T(function(){return B(unCStr("PatternMatchFail"));}),_3L=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3I,_3J,_3K),_3M=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3L,_u,_u),_3N=function(_3O){return E(_3M);},_3P=function(_3Q){var _3R=E(_3Q);return new F(function(){return _A(B(_y(_3R.a)),_3N,_3R.b);});},_3S=function(_3T){return E(E(_3T).a);},_3U=function(_3V){return new T2(0,_3W,_3V);},_3X=function(_3Y,_3Z){return new F(function(){return _O(E(_3Y).a,_3Z);});},_40=function(_41,_42){return new F(function(){return _1S(_3X,_41,_42);});},_43=function(_44,_45,_46){return new F(function(){return _O(E(_45).a,_46);});},_47=new T3(0,_43,_3S,_40),_3W=new T(function(){return new T5(0,_3N,_47,_3U,_3P,_3S);}),_48=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_49=function(_4a,_4b){return new F(function(){return die(new T(function(){return B(A2(_28,_4b,_4a));}));});},_4c=function(_4d,_4e){return new F(function(){return _49(_4d,_4e);});},_4f=function(_4g,_4h){var _4i=E(_4h);if(!_4i._){return new T2(0,_u,_u);}else{var _4j=_4i.a;if(!B(A1(_4g,_4j))){return new T2(0,_u,_4i);}else{var _4k=new T(function(){var _4l=B(_4f(_4g,_4i.b));return new T2(0,_4l.a,_4l.b);});return new T2(0,new T2(1,_4j,new T(function(){return E(E(_4k).a);})),new T(function(){return E(E(_4k).b);}));}}},_4m=32,_4n=new T(function(){return B(unCStr("\n"));}),_4o=function(_4p){return (E(_4p)==124)?false:true;},_4q=function(_4r,_4s){var _4t=B(_4f(_4o,B(unCStr(_4r)))),_4u=_4t.a,_4v=function(_4w,_4x){var _4y=new T(function(){var _4z=new T(function(){return B(_O(_4s,new T(function(){return B(_O(_4x,_4n));},1)));});return B(unAppCStr(": ",_4z));},1);return new F(function(){return _O(_4w,_4y);});},_4A=E(_4t.b);if(!_4A._){return new F(function(){return _4v(_4u,_u);});}else{if(E(_4A.a)==124){return new F(function(){return _4v(_4u,new T2(1,_4m,_4A.b));});}else{return new F(function(){return _4v(_4u,_u);});}}},_4B=function(_4C){return new F(function(){return _4c(new T1(0,new T(function(){return B(_4q(_4C,_48));})),_3W);});},_4D=function(_4E){return new F(function(){return _4B("jsEther.hs:(92,1)-(98,107)|function setAccelX");});},_4F=new T(function(){return B(_4D(_));}),_4G=function(_4H,_4I,_4J){var _4K=E(_4H);if(!_4K._){return E(_4F);}else{var _4L=_4K.a,_4M=_4K.b,_4N=function(_4O){var _4P=E(_4J);if(!_4P._){return E(_4F);}else{var _4Q=_4P.a,_4R=new T(function(){var _4S=E(_4L);return {_:0,a:_4S.a,b:_4S.b,c:_4S.c,d:_4S.d,e:_4S.e,f:_4S.f,g:new T(function(){var _4T=E(_4I),_4U=E(_4T.e),_4V=E(_4Q),_4W=E(_4V.e);return  -1*(_4U-20)*(E(_4T.c)-E(_4T.a))/_4U+(_4W-20)*(E(_4V.c)-E(_4V.a))/_4W;}),h:new T(function(){var _4X=E(_4I),_4Y=E(_4X.e),_4Z=E(_4Q),_50=E(_4Z.e);return  -1*(_4Y-20)*(E(_4X.d)-E(_4X.b))/_4Y+(_50-20)*(E(_4Z.d)-E(_4Z.b))/_50;})};});return new T2(1,_4R,new T(function(){return B(_4G(_4M,_4Q,_4P.b));}));}};if(!E(_4M)._){if(!E(_4J)._){var _51=new T(function(){var _52=E(_4L);return {_:0,a:_52.a,b:_52.b,c:_52.c,d:_52.d,e:_52.e,f:_52.f,g:new T(function(){var _53=E(_4I),_54=E(_53.e);return  -1*(_54-20)*(E(_53.c)-E(_53.a))/_54;}),h:new T(function(){var _55=E(_4I),_56=E(_55.e);return  -1*(_56-20)*(E(_55.d)-E(_55.b))/_56;})};});return new T2(1,_51,_u);}else{return new F(function(){return _4N(_);});}}else{return new F(function(){return _4N(_);});}}},_57=function(_58){var _59=E(_58);if(!_59._){return __Z;}else{var _5a=new T(function(){var _5b=E(_59.a),_5c=E(_5b.a);if(!_5c._){return E(_4F);}else{var _5d=E(_5b.b);if(!_5d._){return E(_4F);}else{var _5e=_5d.a,_5f=new T(function(){var _5g=E(_5c.a);return {_:0,a:_5g.a,b:_5g.b,c:_5g.c,d:_5g.d,e:_5g.e,f:_5g.f,g:new T(function(){var _5h=E(_5e),_5i=E(_5h.e);return (_5i-20)*(E(_5h.c)-E(_5h.a))/_5i;}),h:new T(function(){var _5j=E(_5e),_5k=E(_5j.e);return (_5k-20)*(E(_5j.d)-E(_5j.b))/_5k;})};});return new T2(1,_5f,new T(function(){return B(_4G(_5c.b,_5e,_5d.b));}));}}});return new T2(1,_5a,new T(function(){return B(_57(_59.b));}));}},_5l=function(_5m){return new F(function(){return _4B("jsEther.hs:(101,1)-(107,112)|function setAccelY");});},_5n=new T(function(){return B(_5l(_));}),_5o=function(_5p,_5q,_5r){var _5s=E(_5p);if(!_5s._){return E(_5n);}else{var _5t=_5s.a,_5u=_5s.b,_5v=function(_5w){var _5x=E(_5r);if(!_5x._){return E(_5n);}else{var _5y=_5x.a,_5z=new T(function(){var _5A=E(_5t);return {_:0,a:_5A.a,b:_5A.b,c:_5A.c,d:_5A.d,e:_5A.e,f:_5A.f,g:new T(function(){var _5B=E(_5q),_5C=E(_5B.e),_5D=E(_5y),_5E=E(_5D.e);return E(_5A.g)+ -1*(_5C-20)*(E(_5B.c)-E(_5B.a))/_5C+(_5E-20)*(E(_5D.c)-E(_5D.a))/_5E;}),h:new T(function(){var _5F=E(_5q),_5G=E(_5F.e),_5H=E(_5y),_5I=E(_5H.e);return E(_5A.h)+ -1*(_5G-20)*(E(_5F.d)-E(_5F.b))/_5G+(_5I-20)*(E(_5H.d)-E(_5H.b))/_5I;})};});return new T2(1,_5z,new T(function(){return B(_5o(_5u,_5y,_5x.b));}));}};if(!E(_5u)._){if(!E(_5r)._){var _5J=new T(function(){var _5K=E(_5t);return {_:0,a:_5K.a,b:_5K.b,c:_5K.c,d:_5K.d,e:_5K.e,f:_5K.f,g:new T(function(){var _5L=E(_5q),_5M=E(_5L.e);return E(_5K.g)+ -1*(_5M-20)*(E(_5L.c)-E(_5L.a))/_5M;}),h:new T(function(){var _5N=E(_5q),_5O=E(_5N.e);return E(_5K.h)+ -1*(_5O-20)*(E(_5N.d)-E(_5N.b))/_5O;})};});return new T2(1,_5J,_u);}else{return new F(function(){return _5v(_);});}}else{return new F(function(){return _5v(_);});}}},_5P=function(_5Q){var _5R=E(_5Q);if(!_5R._){return __Z;}else{var _5S=new T(function(){var _5T=E(_5R.a),_5U=E(_5T.a);if(!_5U._){return E(_5n);}else{var _5V=E(_5T.b);if(!_5V._){return E(_5n);}else{var _5W=_5V.a,_5X=new T(function(){var _5Y=E(_5U.a);return {_:0,a:_5Y.a,b:_5Y.b,c:_5Y.c,d:_5Y.d,e:_5Y.e,f:_5Y.f,g:new T(function(){var _5Z=E(_5W),_60=E(_5Z.e);return E(_5Y.g)+(_60-20)*(E(_5Z.c)-E(_5Z.a))/_60;}),h:new T(function(){var _61=E(_5W),_62=E(_61.e);return E(_5Y.h)+(_62-20)*(E(_61.d)-E(_61.b))/_62;})};});return new T2(1,_5X,new T(function(){return B(_5o(_5U.b,_5W,_5V.b));}));}}});return new T2(1,_5S,new T(function(){return B(_5P(_5R.b));}));}},_63=function(_64){return new F(function(){return _4B("jsEther.hs:(110,1)-(116,108)|function setAccelY2");});},_65=new T(function(){return B(_63(_));}),_66=function(_67,_68,_69){var _6a=E(_67);if(!_6a._){return E(_65);}else{var _6b=_6a.a,_6c=_6a.b,_6d=function(_6e){var _6f=E(_69);if(!_6f._){return E(_65);}else{var _6g=_6f.a,_6h=new T(function(){var _6i=E(_6b);return {_:0,a:_6i.a,b:_6i.b,c:_6i.c,d:_6i.d,e:_6i.e,f:_6i.f,g:new T(function(){var _6j=E(_68),_6k=E(_6j.e),_6l=E(_6g),_6m=E(_6l.e);return  -1*(_6k-20)*(E(_6j.c)-E(_6j.a))/_6k+(_6m-20)*(E(_6l.c)-E(_6l.a))/_6m;}),h:new T(function(){var _6n=E(_68),_6o=E(_6n.e),_6p=E(_6g),_6q=E(_6p.e);return  -1*(_6o-20)*(E(_6n.d)-E(_6n.b))/_6o+(_6q-20)*(E(_6p.d)-E(_6p.b))/_6q;})};});return new T2(1,_6h,new T(function(){return B(_66(_6c,_6g,_6f.b));}));}};if(!E(_6c)._){if(!E(_69)._){var _6r=new T(function(){var _6s=E(_6b);return {_:0,a:_6s.a,b:_6s.b,c:_6s.c,d:_6s.d,e:_6s.e,f:_6s.f,g:new T(function(){var _6t=E(_68),_6u=E(_6t.e);return  -1*(_6u-20)*(E(_6t.c)-E(_6t.a))/_6u;}),h:new T(function(){var _6v=E(_68),_6w=E(_6v.e);return  -1*(_6w-20)*(E(_6v.d)-E(_6v.b))/_6w;})};});return new T2(1,_6r,_u);}else{return new F(function(){return _6d(_);});}}else{return new F(function(){return _6d(_);});}}},_6x=function(_6y){var _6z=E(_6y);if(!_6z._){return __Z;}else{var _6A=new T(function(){var _6B=E(_6z.a),_6C=E(_6B.a);if(!_6C._){return E(_65);}else{var _6D=E(_6B.b);if(!_6D._){return E(_65);}else{var _6E=_6D.a,_6F=new T(function(){var _6G=E(_6C.a);return {_:0,a:_6G.a,b:_6G.b,c:_6G.c,d:_6G.d,e:_6G.e,f:_6G.f,g:new T(function(){var _6H=E(_6E),_6I=E(_6H.e);return (_6I-20)*(E(_6H.c)-E(_6H.a))/_6I;}),h:new T(function(){var _6J=E(_6E),_6K=E(_6J.e);return (_6K-20)*(E(_6J.d)-E(_6J.b))/_6K;})};});return new T2(1,_6F,new T(function(){return B(_66(_6C.b,_6E,_6D.b));}));}}});return new T2(1,_6A,new T(function(){return B(_6x(_6z.b));}));}},_6L=function(_6M){var _6N=E(_6M);if(!_6N._){return __Z;}else{var _6O=new T(function(){var _6P=E(_6N.a),_6Q=_6P.a,_6R=_6P.b,_6S=_6P.c,_6T=_6P.d;return new T5(0,_6Q,_6R,_6S,_6T,new T(function(){var _6U=E(_6S)-E(_6Q),_6V=E(_6T)-E(_6R);return Math.sqrt(_6U*_6U+_6V*_6V);}));});return new T2(1,_6O,new T(function(){return B(_6L(_6N.b));}));}},_6W=function(_6X){var _6Y=E(_6X);return (_6Y._==0)?__Z:new T2(1,new T(function(){return B(_6L(_6Y.a));}),new T(function(){return B(_6W(_6Y.b));}));},_6Z=function(_70,_71){var _72=E(_71);if(!_72._){var _73=new T(function(){var _74=E(_70),_75=_74.e,_76=_74.f;return {_:0,a:_74.a,b:_74.b,c:new T(function(){return E(_74.c)+E(_75)*0.1;}),d:new T(function(){return E(_74.d)+E(_76)*0.1;}),e:_75,f:_76,g:_74.g,h:_74.h};});return new T2(0,_73,_u);}else{var _77=new T(function(){var _78=E(_70),_79=_78.e,_7a=_78.f;return {_:0,a:_78.a,b:_78.b,c:new T(function(){return E(_78.c)+E(_79)*0.1;}),d:new T(function(){return E(_78.d)+E(_7a)*0.1;}),e:_79,f:_7a,g:_78.g,h:_78.h};});return new T2(0,_77,new T(function(){var _7b=B(_6Z(_72.a,_72.b));return new T2(1,_7b.a,_7b.b);}));}},_7c=new T(function(){return B(_4B("jsEther.hs:(141,1)-(143,61)|function setPosition"));}),_7d=function(_7e){var _7f=E(_7e);if(!_7f._){return E(_7c);}else{var _7g=_7f.a,_7h=E(_7f.b);if(!_7h._){var _7i=new T(function(){var _7j=E(_7g),_7k=_7j.e,_7l=_7j.f;return {_:0,a:_7j.a,b:_7j.b,c:new T(function(){return E(_7j.c)+E(_7k)*0.1;}),d:new T(function(){return E(_7j.d)+E(_7l)*0.1;}),e:_7k,f:_7l,g:_7j.g,h:_7j.h};});return new T2(0,_7i,_u);}else{var _7m=new T(function(){var _7n=E(_7g),_7o=_7n.e,_7p=_7n.f;return {_:0,a:_7n.a,b:_7n.b,c:new T(function(){return E(_7n.c)+E(_7o)*0.1;}),d:new T(function(){return E(_7n.d)+E(_7p)*0.1;}),e:_7o,f:_7p,g:_7n.g,h:_7n.h};});return new T2(0,_7m,new T(function(){var _7q=B(_6Z(_7h.a,_7h.b));return new T2(1,_7q.a,_7q.b);}));}}},_7r=function(_7s){var _7t=B(_7d(_7s));return new T2(1,_7t.a,_7t.b);},_7u=function(_7v){var _7w=E(_7v);return (_7w._==0)?__Z:new T2(1,new T(function(){return B(_7r(_7w.a));}),new T(function(){return B(_7u(_7w.b));}));},_7x=function(_7y){return new F(function(){return _4B("jsEther.hs:(177,1)-(179,63)|function setSpringX");});},_7z=new T(function(){return B(_7x(_));}),_7A=function(_7B,_7C,_7D){var _7E=E(_7D);if(!_7E._){return __Z;}else{var _7F=E(_7C);if(!_7F._){return E(_7z);}else{var _7G=_7F.a,_7H=new T(function(){return new T5(0,new T(function(){return E(E(_7B).c)+1;}),new T(function(){return E(E(_7B).d);}),new T(function(){return E(E(_7G).c)-1;}),new T(function(){return E(E(_7G).d);}),E(_7E.a).e);});return new T2(1,_7H,new T(function(){return B(_7A(_7G,_7F.b,_7E.b));}));}}},_7I=function(_7J,_7K){var _7L=E(_7K);if(!_7L._){return __Z;}else{var _7M=E(_7J);if(!_7M._){return E(_7z);}else{var _7N=_7M.a,_7O=E(_7M.b);if(!_7O._){return E(_7z);}else{var _7P=_7O.a,_7Q=new T(function(){return new T5(0,new T(function(){return E(E(_7N).c)+1;}),new T(function(){return E(E(_7N).d);}),new T(function(){return E(E(_7P).c)-1;}),new T(function(){return E(E(_7P).d);}),E(_7L.a).e);});return new T2(1,_7Q,new T(function(){return B(_7A(_7P,_7O.b,_7L.b));}));}}}},_7R=function(_7S){var _7T=E(_7S);return new F(function(){return _7I(_7T.a,_7T.b);});},_7U=function(_7V){var _7W=E(_7V);return (_7W._==0)?__Z:new T2(1,new T(function(){return B(_7R(_7W.a));}),new T(function(){return B(_7U(_7W.b));}));},_7X=function(_7Y){return new F(function(){return _4B("jsEther.hs:(187,1)-(189,63)|function setSpringY");});},_7Z=new T(function(){return B(_7X(_));}),_80=function(_81,_82,_83){var _84=E(_83);if(!_84._){return __Z;}else{var _85=E(_82);if(!_85._){return E(_7Z);}else{var _86=_85.a,_87=new T(function(){return new T5(0,new T(function(){return E(E(_81).c);}),new T(function(){return E(E(_81).d)+1;}),new T(function(){return E(E(_86).c);}),new T(function(){return E(E(_86).d)-1;}),E(_84.a).e);});return new T2(1,_87,new T(function(){return B(_80(_86,_85.b,_84.b));}));}}},_88=function(_89,_8a){var _8b=E(_8a);if(!_8b._){return __Z;}else{var _8c=E(_89);if(!_8c._){return E(_7Z);}else{var _8d=_8c.a,_8e=E(_8c.b);if(!_8e._){return E(_7Z);}else{var _8f=_8e.a,_8g=new T(function(){return new T5(0,new T(function(){return E(E(_8d).c);}),new T(function(){return E(E(_8d).d)+1;}),new T(function(){return E(E(_8f).c);}),new T(function(){return E(E(_8f).d)-1;}),E(_8b.a).e);});return new T2(1,_8g,new T(function(){return B(_80(_8f,_8e.b,_8b.b));}));}}}},_8h=function(_8i){var _8j=E(_8i);return new F(function(){return _88(_8j.a,_8j.b);});},_8k=function(_8l){var _8m=E(_8l);return (_8m._==0)?__Z:new T2(1,new T(function(){return B(_8h(_8m.a));}),new T(function(){return B(_8k(_8m.b));}));},_8n=function(_8o){return E(E(_8o).a);},_8p=function(_8q){return E(E(_8q).a);},_8r=function(_8s){return E(E(_8s).b);},_8t=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_8u=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_8v=function(_){return new F(function(){return __jsNull();});},_8w=function(_8x){var _8y=B(A1(_8x,_));return E(_8y);},_8z=new T(function(){return B(_8w(_8v));}),_8A=new T(function(){return E(_8z);}),_8B=function(_8C){return E(E(_8C).b);},_8D=function(_8E){return E(E(_8E).b);},_8F=function(_8G,_8H,_8I){var _8J=B(_8n(_8G)),_8K=new T(function(){return B(_8B(_8J));}),_8L=function(_8M){var _8N=function(_){var _8O=E(_8H);if(!_8O._){var _8P=B(A1(_8M,_2u)),_8Q=__createJSFunc(0,function(_){var _8R=B(A1(_8P,_));return _8A;}),_8S=__app2(E(_8u),_8O.a,_8Q);return new T(function(){var _8T=Number(_8S),_8U=jsTrunc(_8T);return new T2(0,_8U,E(_8O));});}else{var _8V=B(A1(_8M,_2u)),_8W=__createJSFunc(0,function(_){var _8X=B(A1(_8V,_));return _8A;}),_8Y=__app2(E(_8t),_8O.a,_8W);return new T(function(){var _8Z=Number(_8Y),_90=jsTrunc(_8Z);return new T2(0,_90,E(_8O));});}};return new F(function(){return A1(_8K,_8N);});},_91=new T(function(){return B(A2(_8D,_8G,function(_92){return E(_8I);}));});return new F(function(){return A3(_8r,B(_8p(_8J)),_91,_8L);});},_93=function(_94){var _95=E(_94);if(!_95._){return __Z;}else{var _96=new T(function(){var _97=E(_95.a),_98=_97.g,_99=_97.h;return {_:0,a:_97.a,b:_97.b,c:_97.c,d:_97.d,e:new T(function(){return E(_97.e)+E(_98)*0.1;}),f:new T(function(){return E(_97.f)+E(_99)*0.1;}),g:_98,h:_99};});return new T2(1,_96,new T(function(){return B(_93(_95.b));}));}},_9a=function(_9b){var _9c=E(_9b);return (_9c._==0)?__Z:new T2(1,new T(function(){return B(_93(_9c.a));}),new T(function(){return B(_9a(_9c.b));}));},_9d=function(_9e){while(1){var _9f=B((function(_9g){var _9h=E(_9g);if(!_9h._){return __Z;}else{var _9i=_9h.b,_9j=E(_9h.a);if(!_9j._){_9e=_9i;return __continue;}else{return new T2(1,_9j.b,new T(function(){return B(_9d(_9i));}));}}})(_9e));if(_9f!=__continue){return _9f;}}},_9k=function(_9l){while(1){var _9m=B((function(_9n){var _9o=E(_9n);if(!_9o._){return __Z;}else{var _9p=_9o.b,_9q=E(_9o.a);if(!_9q._){_9l=_9p;return __continue;}else{return new T2(1,_9q.a,new T(function(){return B(_9k(_9p));}));}}})(_9l));if(_9m!=__continue){return _9m;}}},_9r=function(_9s){while(1){var _9t=B((function(_9u){var _9v=E(_9u);if(!_9v._){return __Z;}else{var _9w=_9v.b,_9x=E(_9v.a);if(!_9x._){_9s=_9w;return __continue;}else{var _9y=new T(function(){return B(_9r(new T2(1,_9x.b,new T(function(){return B(_9d(_9w));}))));});return new T2(1,new T2(1,_9x.a,new T(function(){return B(_9k(_9w));})),_9y);}}})(_9s));if(_9t!=__continue){return _9t;}}},_9z=function(_9A,_9B){var _9C=E(_9A);if(!_9C._){return __Z;}else{var _9D=E(_9B);return (_9D._==0)?__Z:new T2(1,new T2(0,_9C.a,_9D.a),new T(function(){return B(_9z(_9C.b,_9D.b));}));}},_9E=function(_9F,_9G,_9H,_9I,_9J,_){var _9K=E(_2I),_9L=__app1(_9K,_9G),_9M=function(_9N,_9O,_9P,_){while(1){var _9Q=B((function(_9R,_9S,_9T,_){var _9U=E(_9R);if(!_9U._){return _2u;}else{var _9V=_9U.a,_9W=B(_2z(new T(function(){return E(E(_9V).c)+30;},1),new T(function(){return E(E(_9V).d)+30;},1),_3H,_9S,_)),_9X=_9S,_9Y=_;_9N=_9U.b;_9O=_9X;_9P=_9Y;return __continue;}})(_9N,_9O,_9P,_));if(_9Q!=__continue){return _9Q;}}},_9Z=function(_a0,_a1,_){while(1){var _a2=B((function(_a3,_a4,_){var _a5=E(_a3);if(!_a5._){return _2u;}else{var _a6=_a5.b,_a7=E(_a5.a);if(!_a7._){var _a8=_a4;_a0=_a6;_a1=_a8;return __continue;}else{var _a9=_a7.a,_aa=E(_a4),_ab=B(_2z(new T(function(){return E(E(_a9).c)+30;},1),new T(function(){return E(E(_a9).d)+30;},1),_3H,_aa,_)),_ac=B(_9M(_a7.b,_aa,_,_));_a0=_a6;_a1=_aa;return __continue;}}})(_a0,_a1,_));if(_a2!=__continue){return _a2;}}},_ad=B(_9Z(_9H,_9F,_)),_ae=function(_){var _af=E(_9J);if(!_af._){var _ag=new T(function(){return B(_7u(B(_9a(B(_57(B(_9z(_9H,_9I))))))));}),_ah=function(_ai,_aj,_ak,_){while(1){var _al=B((function(_am,_an,_ao,_){var _ap=E(_am);if(!_ap._){return _2u;}else{var _aq=_ap.a,_ar=B(_2z(new T(function(){return E(E(_aq).c)+30;},1),new T(function(){return E(E(_aq).d)+30;},1),_3H,_an,_)),_as=_an,_at=_;_ai=_ap.b;_aj=_as;_ak=_at;return __continue;}})(_ai,_aj,_ak,_));if(_al!=__continue){return _al;}}},_au=function(_av,_aw,_){while(1){var _ax=B((function(_ay,_az,_){var _aA=E(_ay);if(!_aA._){return _2u;}else{var _aB=_aA.b,_aC=E(_aA.a);if(!_aC._){var _aD=_az;_av=_aB;_aw=_aD;return __continue;}else{var _aE=_aC.a,_aF=E(_az),_aG=B(_2z(new T(function(){return E(E(_aE).c)+30;},1),new T(function(){return E(E(_aE).d)+30;},1),_3H,_aF,_)),_aH=B(_ah(_aC.b,_aF,_,_));_av=_aB;_aw=_aF;return __continue;}}})(_av,_aw,_));if(_ax!=__continue){return _ax;}}},_aI=function(_aJ,_aK,_aL,_aM,_){var _aN=__app1(_9K,_aK),_aO=B(_au(_aL,_aJ,_)),_aP=function(_){var _aQ=new T(function(){return B(_7u(B(_9a(B(_57(B(_9z(_aL,_aM))))))));});return new F(function(){return _aI(_aJ,_aK,_aQ,new T(function(){return B(_6W(B(_7U(B(_9z(_aQ,_aM))))));}),_);});},_aR=B(A(_8F,[_2t,_2J,_aP,_]));return _2u;};return new F(function(){return _aI(_9F,_9G,_ag,new T(function(){return B(_6W(B(_7U(B(_9z(_ag,_9I))))));}),_);});}else{var _aS=E(_9I);if(!_aS._){var _aT=new T(function(){return B(_7u(B(_9a(B(_9r(B(_6x(B(_9z(B(_9r(_9H)),_af))))))))));}),_aU=function(_aV,_aW,_aX,_){while(1){var _aY=B((function(_aZ,_b0,_b1,_){var _b2=E(_aZ);if(!_b2._){return _2u;}else{var _b3=_b2.a,_b4=B(_2z(new T(function(){return E(E(_b3).c)+30;},1),new T(function(){return E(E(_b3).d)+30;},1),_3H,_b0,_)),_b5=_b0,_b6=_;_aV=_b2.b;_aW=_b5;_aX=_b6;return __continue;}})(_aV,_aW,_aX,_));if(_aY!=__continue){return _aY;}}},_b7=function(_b8,_b9,_){while(1){var _ba=B((function(_bb,_bc,_){var _bd=E(_bb);if(!_bd._){return _2u;}else{var _be=_bd.b,_bf=E(_bd.a);if(!_bf._){var _bg=_bc;_b8=_be;_b9=_bg;return __continue;}else{var _bh=_bf.a,_bi=E(_bc),_bj=B(_2z(new T(function(){return E(E(_bh).c)+30;},1),new T(function(){return E(E(_bh).d)+30;},1),_3H,_bi,_)),_bk=B(_aU(_bf.b,_bi,_,_));_b8=_be;_b9=_bi;return __continue;}}})(_b8,_b9,_));if(_ba!=__continue){return _ba;}}},_bl=function(_bm,_bn,_bo,_bp,_){var _bq=__app1(_9K,_bn),_br=B(_b7(_bo,_bm,_)),_bs=function(_){var _bt=new T(function(){return B(_7u(B(_9a(B(_57(B(_9z(_bo,_bp))))))));});return new F(function(){return _bl(_bm,_bn,_bt,new T(function(){return B(_6W(B(_7U(B(_9z(_bt,_bp))))));}),_);});},_bu=B(A(_8F,[_2t,_2J,_bs,_]));return _2u;},_bv=function(_bw,_bx,_by,_bz,_){var _bA=__app1(_9K,_bx),_bB=B(_b7(_by,_bw,_)),_bC=function(_){var _bD=E(_bz);if(!_bD._){var _bE=new T(function(){return B(_7u(B(_9a(B(_57(B(_9z(_by,_u))))))));});return new F(function(){return _bl(_bw,_bx,_bE,new T(function(){return B(_6W(B(_7U(B(_9z(_bE,_u))))));}),_);});}else{var _bF=new T(function(){return B(_7u(B(_9a(B(_9r(B(_6x(B(_9z(B(_9r(_by)),_bD))))))))));});return new F(function(){return _bv(_bw,_bx,_bF,new T(function(){return B(_6W(B(_8k(B(_9z(B(_9r(_bF)),_bD))))));},1),_);});}},_bG=B(A(_8F,[_2t,_2J,_bC,_]));return _2u;};return new F(function(){return _bv(_9F,_9G,_aT,new T(function(){return B(_6W(B(_8k(B(_9z(B(_9r(_aT)),_af))))));},1),_);});}else{var _bH=new T(function(){return B(_7u(B(_9a(B(_9r(B(_5P(B(_9z(B(_9r(B(_57(B(_9z(_9H,_aS)))))),_af))))))))));}),_bI=function(_bJ,_bK,_bL,_){while(1){var _bM=B((function(_bN,_bO,_bP,_){var _bQ=E(_bN);if(!_bQ._){return _2u;}else{var _bR=_bQ.a,_bS=B(_2z(new T(function(){return E(E(_bR).c)+30;},1),new T(function(){return E(E(_bR).d)+30;},1),_3H,_bO,_)),_bT=_bO,_bU=_;_bJ=_bQ.b;_bK=_bT;_bL=_bU;return __continue;}})(_bJ,_bK,_bL,_));if(_bM!=__continue){return _bM;}}},_bV=function(_bW,_bX,_){while(1){var _bY=B((function(_bZ,_c0,_){var _c1=E(_bZ);if(!_c1._){return _2u;}else{var _c2=_c1.b,_c3=E(_c1.a);if(!_c3._){var _c4=_c0;_bW=_c2;_bX=_c4;return __continue;}else{var _c5=_c3.a,_c6=E(_c0),_c7=B(_2z(new T(function(){return E(E(_c5).c)+30;},1),new T(function(){return E(E(_c5).d)+30;},1),_3H,_c6,_)),_c8=B(_bI(_c3.b,_c6,_,_));_bW=_c2;_bX=_c6;return __continue;}}})(_bW,_bX,_));if(_bY!=__continue){return _bY;}}},_c9=function(_ca,_cb,_cc,_cd,_){var _ce=__app1(_9K,_cb),_cf=B(_bV(_cc,_ca,_)),_cg=function(_){var _ch=new T(function(){return B(_7u(B(_9a(B(_57(B(_9z(_cc,_cd))))))));});return new F(function(){return _c9(_ca,_cb,_ch,new T(function(){return B(_6W(B(_7U(B(_9z(_ch,_cd))))));}),_);});},_ci=B(A(_8F,[_2t,_2J,_cg,_]));return _2u;},_cj=function(_ck,_cl,_cm,_cn,_){var _co=__app1(_9K,_cl),_cp=B(_bV(_cm,_ck,_)),_cq=function(_){var _cr=E(_cn);if(!_cr._){var _cs=new T(function(){return B(_7u(B(_9a(B(_57(B(_9z(_cm,_u))))))));});return new F(function(){return _c9(_ck,_cl,_cs,new T(function(){return B(_6W(B(_7U(B(_9z(_cs,_u))))));}),_);});}else{var _ct=new T(function(){return B(_7u(B(_9a(B(_9r(B(_6x(B(_9z(B(_9r(_cm)),_cr))))))))));});return new F(function(){return _cj(_ck,_cl,_ct,new T(function(){return B(_6W(B(_8k(B(_9z(B(_9r(_ct)),_cr))))));},1),_);});}},_cu=B(A(_8F,[_2t,_2J,_cq,_]));return _2u;},_cv=function(_cw,_cx,_cy,_cz,_cA,_){var _cB=__app1(_9K,_cx),_cC=B(_bV(_cy,_cw,_)),_cD=function(_){var _cE=E(_cA);if(!_cE._){var _cF=new T(function(){return B(_7u(B(_9a(B(_57(B(_9z(_cy,_cz))))))));});return new F(function(){return _c9(_cw,_cx,_cF,new T(function(){return B(_6W(B(_7U(B(_9z(_cF,_cz))))));}),_);});}else{var _cG=E(_cz);if(!_cG._){var _cH=new T(function(){return B(_7u(B(_9a(B(_9r(B(_6x(B(_9z(B(_9r(_cy)),_cE))))))))));});return new F(function(){return _cj(_cw,_cx,_cH,new T(function(){return B(_6W(B(_8k(B(_9z(B(_9r(_cH)),_cE))))));},1),_);});}else{var _cI=new T(function(){return B(_7u(B(_9a(B(_9r(B(_5P(B(_9z(B(_9r(B(_57(B(_9z(_cy,_cG)))))),_cE))))))))));});return new F(function(){return _cv(_cw,_cx,_cI,new T(function(){return B(_6W(B(_7U(B(_9z(_cI,_cG))))));}),new T(function(){return B(_6W(B(_8k(B(_9z(B(_9r(_cI)),_cE))))));},1),_);});}}},_cJ=B(A(_8F,[_2t,_2J,_cD,_]));return _2u;};return new F(function(){return _cv(_9F,_9G,_bH,new T(function(){return B(_6W(B(_7U(B(_9z(_bH,_aS))))));}),new T(function(){return B(_6W(B(_8k(B(_9z(B(_9r(_bH)),_af))))));},1),_);});}}},_cK=B(A(_8F,[_2t,_2J,_ae,_]));return _2u;},_cL=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_cM=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_cN=function(_cO,_){var _cP=__app1(E(_cM),_cO);if(!_cP){return _2a;}else{var _cQ=__app1(E(_cL),_cO);return new T1(1,new T2(0,_cQ,_cO));}},_cR=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_cS=function(_cT,_cU){return new F(function(){return A2(_8B,_cT,function(_){var _cV=__app1(E(_cR),toJSStr(E(_cU))),_cW=__eq(_cV,E(_8A));if(!E(_cW)){var _cX=__isUndef(_cV);if(!E(_cX)){return new F(function(){return _cN(_cV,_);});}else{return _2a;}}else{return _2a;}});});},_cY=20,_cZ=21,_d0=0,_d1=function(_d2,_d3,_d4,_d5,_d6,_d7){var _d8=E(_d2);if(!_d8){return __Z;}else{var _d9=new T(function(){return B(_d1(_d8-1|0,new T(function(){return E(_d3)+20+2;}),_d4,new T(function(){return E(_d3)+40+2;}),_d6,_d7));});return new T2(1,new T5(0,_d3,_d4,_d5,_d6,_d7),_d9);}},_da=function(_db,_dc,_dd,_de,_df,_dg,_dh){var _di=E(_db);if(!_di){return __Z;}else{var _dj=E(_dc);return (_dj==0)?__Z:new T2(1,new T(function(){return B(_d1(_di,_dd,_de,_df,_dg,_dh));}),new T(function(){return B(_da(_di,_dj-1|0,_dd,_de+20+2,_df,_de+20+2,_dh));}));}},_dk=function(_dl,_dm,_dn,_do,_dp,_dq){var _dr=E(_dl);if(!_dr){return __Z;}else{var _ds=E(_dm);return (_ds==0)?__Z:new T2(1,new T(function(){return B(_d1(_dr,_dn,_do,_dp,_d0,_dq));}),new T(function(){return B(_da(_dr,_ds-1|0,_dn,_do+20+2,_dp,_do+20+2,_dq));}));}},_dt=new T(function(){return B(_4B("Text\\ParserCombinators\\ReadP.hs:(128,3)-(151,52)|function <|>"));}),_du=function(_dv,_dw){while(1){var _dx=B((function(_dy,_dz){var _dA=E(_dy);switch(_dA._){case 0:var _dB=E(_dz);if(!_dB._){return __Z;}else{_dv=B(A1(_dA.a,_dB.a));_dw=_dB.b;return __continue;}break;case 1:var _dC=B(A1(_dA.a,_dz)),_dD=_dz;_dv=_dC;_dw=_dD;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_dA.a,_dz),new T(function(){return B(_du(_dA.b,_dz));}));default:return E(_dA.a);}})(_dv,_dw));if(_dx!=__continue){return _dx;}}},_dE=function(_dF,_dG){var _dH=function(_dI){var _dJ=E(_dG);if(_dJ._==3){return new T2(3,_dJ.a,new T(function(){return B(_dE(_dF,_dJ.b));}));}else{var _dK=E(_dF);if(_dK._==2){return E(_dJ);}else{var _dL=E(_dJ);if(_dL._==2){return E(_dK);}else{var _dM=function(_dN){var _dO=E(_dL);if(_dO._==4){var _dP=function(_dQ){return new T1(4,new T(function(){return B(_O(B(_du(_dK,_dQ)),_dO.a));}));};return new T1(1,_dP);}else{var _dR=E(_dK);if(_dR._==1){var _dS=_dR.a,_dT=E(_dO);if(!_dT._){return new T1(1,function(_dU){return new F(function(){return _dE(B(A1(_dS,_dU)),_dT);});});}else{var _dV=function(_dW){return new F(function(){return _dE(B(A1(_dS,_dW)),new T(function(){return B(A1(_dT.a,_dW));}));});};return new T1(1,_dV);}}else{var _dX=E(_dO);if(!_dX._){return E(_dt);}else{var _dY=function(_dZ){return new F(function(){return _dE(_dR,new T(function(){return B(A1(_dX.a,_dZ));}));});};return new T1(1,_dY);}}}},_e0=E(_dK);switch(_e0._){case 1:var _e1=E(_dL);if(_e1._==4){var _e2=function(_e3){return new T1(4,new T(function(){return B(_O(B(_du(B(A1(_e0.a,_e3)),_e3)),_e1.a));}));};return new T1(1,_e2);}else{return new F(function(){return _dM(_);});}break;case 4:var _e4=_e0.a,_e5=E(_dL);switch(_e5._){case 0:var _e6=function(_e7){var _e8=new T(function(){return B(_O(_e4,new T(function(){return B(_du(_e5,_e7));},1)));});return new T1(4,_e8);};return new T1(1,_e6);case 1:var _e9=function(_ea){var _eb=new T(function(){return B(_O(_e4,new T(function(){return B(_du(B(A1(_e5.a,_ea)),_ea));},1)));});return new T1(4,_eb);};return new T1(1,_e9);default:return new T1(4,new T(function(){return B(_O(_e4,_e5.a));}));}break;default:return new F(function(){return _dM(_);});}}}}},_ec=E(_dF);switch(_ec._){case 0:var _ed=E(_dG);if(!_ed._){var _ee=function(_ef){return new F(function(){return _dE(B(A1(_ec.a,_ef)),new T(function(){return B(A1(_ed.a,_ef));}));});};return new T1(0,_ee);}else{return new F(function(){return _dH(_);});}break;case 3:return new T2(3,_ec.a,new T(function(){return B(_dE(_ec.b,_dG));}));default:return new F(function(){return _dH(_);});}},_eg=new T(function(){return B(unCStr("("));}),_eh=new T(function(){return B(unCStr(")"));}),_ei=function(_ej,_ek){while(1){var _el=E(_ej);if(!_el._){return (E(_ek)._==0)?true:false;}else{var _em=E(_ek);if(!_em._){return false;}else{if(E(_el.a)!=E(_em.a)){return false;}else{_ej=_el.b;_ek=_em.b;continue;}}}}},_en=function(_eo,_ep){return E(_eo)!=E(_ep);},_eq=function(_er,_es){return E(_er)==E(_es);},_et=new T2(0,_eq,_en),_eu=function(_ev,_ew){while(1){var _ex=E(_ev);if(!_ex._){return (E(_ew)._==0)?true:false;}else{var _ey=E(_ew);if(!_ey._){return false;}else{if(E(_ex.a)!=E(_ey.a)){return false;}else{_ev=_ex.b;_ew=_ey.b;continue;}}}}},_ez=function(_eA,_eB){return (!B(_eu(_eA,_eB)))?true:false;},_eC=new T2(0,_eu,_ez),_eD=function(_eE,_eF){var _eG=E(_eE);switch(_eG._){case 0:return new T1(0,function(_eH){return new F(function(){return _eD(B(A1(_eG.a,_eH)),_eF);});});case 1:return new T1(1,function(_eI){return new F(function(){return _eD(B(A1(_eG.a,_eI)),_eF);});});case 2:return new T0(2);case 3:return new F(function(){return _dE(B(A1(_eF,_eG.a)),new T(function(){return B(_eD(_eG.b,_eF));}));});break;default:var _eJ=function(_eK){var _eL=E(_eK);if(!_eL._){return __Z;}else{var _eM=E(_eL.a);return new F(function(){return _O(B(_du(B(A1(_eF,_eM.a)),_eM.b)),new T(function(){return B(_eJ(_eL.b));},1));});}},_eN=B(_eJ(_eG.a));return (_eN._==0)?new T0(2):new T1(4,_eN);}},_eO=new T0(2),_eP=function(_eQ){return new T2(3,_eQ,_eO);},_eR=function(_eS,_eT){var _eU=E(_eS);if(!_eU){return new F(function(){return A1(_eT,_2u);});}else{var _eV=new T(function(){return B(_eR(_eU-1|0,_eT));});return new T1(0,function(_eW){return E(_eV);});}},_eX=function(_eY,_eZ,_f0){var _f1=new T(function(){return B(A1(_eY,_eP));}),_f2=function(_f3,_f4,_f5,_f6){while(1){var _f7=B((function(_f8,_f9,_fa,_fb){var _fc=E(_f8);switch(_fc._){case 0:var _fd=E(_f9);if(!_fd._){return new F(function(){return A1(_eZ,_fb);});}else{var _fe=_fa+1|0,_ff=_fb;_f3=B(A1(_fc.a,_fd.a));_f4=_fd.b;_f5=_fe;_f6=_ff;return __continue;}break;case 1:var _fg=B(A1(_fc.a,_f9)),_fh=_f9,_fe=_fa,_ff=_fb;_f3=_fg;_f4=_fh;_f5=_fe;_f6=_ff;return __continue;case 2:return new F(function(){return A1(_eZ,_fb);});break;case 3:var _fi=new T(function(){return B(_eD(_fc,_fb));});return new F(function(){return _eR(_fa,function(_fj){return E(_fi);});});break;default:return new F(function(){return _eD(_fc,_fb);});}})(_f3,_f4,_f5,_f6));if(_f7!=__continue){return _f7;}}};return function(_fk){return new F(function(){return _f2(_f1,_fk,0,_f0);});};},_fl=function(_fm){return new F(function(){return A1(_fm,_u);});},_fn=function(_fo,_fp){var _fq=function(_fr){var _fs=E(_fr);if(!_fs._){return E(_fl);}else{var _ft=_fs.a;if(!B(A1(_fo,_ft))){return E(_fl);}else{var _fu=new T(function(){return B(_fq(_fs.b));}),_fv=function(_fw){var _fx=new T(function(){return B(A1(_fu,function(_fy){return new F(function(){return A1(_fw,new T2(1,_ft,_fy));});}));});return new T1(0,function(_fz){return E(_fx);});};return E(_fv);}}};return function(_fA){return new F(function(){return A2(_fq,_fA,_fp);});};},_fB=new T0(6),_fC=function(_fD){return E(E(_fD).a);},_fE=function(_fF,_fG,_fH){while(1){var _fI=E(_fH);if(!_fI._){return false;}else{if(!B(A3(_fC,_fF,_fG,_fI.a))){_fH=_fI.b;continue;}else{return true;}}}},_fJ=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_fK=function(_fL){return new F(function(){return _fE(_et,_fL,_fJ);});},_fM=new T(function(){return B(unCStr("valDig: Bad base"));}),_fN=new T(function(){return B(err(_fM));}),_fO=function(_fP,_fQ){var _fR=function(_fS,_fT){var _fU=E(_fS);if(!_fU._){var _fV=new T(function(){return B(A1(_fT,_u));});return function(_fW){return new F(function(){return A1(_fW,_fV);});};}else{var _fX=E(_fU.a),_fY=function(_fZ){var _g0=new T(function(){return B(_fR(_fU.b,function(_g1){return new F(function(){return A1(_fT,new T2(1,_fZ,_g1));});}));}),_g2=function(_g3){var _g4=new T(function(){return B(A1(_g0,_g3));});return new T1(0,function(_g5){return E(_g4);});};return E(_g2);};switch(E(_fP)){case 8:if(48>_fX){var _g6=new T(function(){return B(A1(_fT,_u));});return function(_g7){return new F(function(){return A1(_g7,_g6);});};}else{if(_fX>55){var _g8=new T(function(){return B(A1(_fT,_u));});return function(_g9){return new F(function(){return A1(_g9,_g8);});};}else{return new F(function(){return _fY(_fX-48|0);});}}break;case 10:if(48>_fX){var _ga=new T(function(){return B(A1(_fT,_u));});return function(_gb){return new F(function(){return A1(_gb,_ga);});};}else{if(_fX>57){var _gc=new T(function(){return B(A1(_fT,_u));});return function(_gd){return new F(function(){return A1(_gd,_gc);});};}else{return new F(function(){return _fY(_fX-48|0);});}}break;case 16:if(48>_fX){if(97>_fX){if(65>_fX){var _ge=new T(function(){return B(A1(_fT,_u));});return function(_gf){return new F(function(){return A1(_gf,_ge);});};}else{if(_fX>70){var _gg=new T(function(){return B(A1(_fT,_u));});return function(_gh){return new F(function(){return A1(_gh,_gg);});};}else{return new F(function(){return _fY((_fX-65|0)+10|0);});}}}else{if(_fX>102){if(65>_fX){var _gi=new T(function(){return B(A1(_fT,_u));});return function(_gj){return new F(function(){return A1(_gj,_gi);});};}else{if(_fX>70){var _gk=new T(function(){return B(A1(_fT,_u));});return function(_gl){return new F(function(){return A1(_gl,_gk);});};}else{return new F(function(){return _fY((_fX-65|0)+10|0);});}}}else{return new F(function(){return _fY((_fX-97|0)+10|0);});}}}else{if(_fX>57){if(97>_fX){if(65>_fX){var _gm=new T(function(){return B(A1(_fT,_u));});return function(_gn){return new F(function(){return A1(_gn,_gm);});};}else{if(_fX>70){var _go=new T(function(){return B(A1(_fT,_u));});return function(_gp){return new F(function(){return A1(_gp,_go);});};}else{return new F(function(){return _fY((_fX-65|0)+10|0);});}}}else{if(_fX>102){if(65>_fX){var _gq=new T(function(){return B(A1(_fT,_u));});return function(_gr){return new F(function(){return A1(_gr,_gq);});};}else{if(_fX>70){var _gs=new T(function(){return B(A1(_fT,_u));});return function(_gt){return new F(function(){return A1(_gt,_gs);});};}else{return new F(function(){return _fY((_fX-65|0)+10|0);});}}}else{return new F(function(){return _fY((_fX-97|0)+10|0);});}}}else{return new F(function(){return _fY(_fX-48|0);});}}break;default:return E(_fN);}}},_gu=function(_gv){var _gw=E(_gv);if(!_gw._){return new T0(2);}else{return new F(function(){return A1(_fQ,_gw);});}};return function(_gx){return new F(function(){return A3(_fR,_gx,_2q,_gu);});};},_gy=8,_gz=16,_gA=function(_gB){var _gC=function(_gD){return new F(function(){return A1(_gB,new T1(5,new T2(0,_gy,_gD)));});},_gE=function(_gF){return new F(function(){return A1(_gB,new T1(5,new T2(0,_gz,_gF)));});},_gG=function(_gH){switch(E(_gH)){case 79:return new T1(1,B(_fO(_gy,_gC)));case 88:return new T1(1,B(_fO(_gz,_gE)));case 111:return new T1(1,B(_fO(_gy,_gC)));case 120:return new T1(1,B(_fO(_gz,_gE)));default:return new T0(2);}};return function(_gI){return (E(_gI)==48)?E(new T1(0,_gG)):new T0(2);};},_gJ=function(_gK){return new T1(0,B(_gA(_gK)));},_gL=false,_gM=true,_gN=function(_gO){var _gP=new T(function(){return B(A1(_gO,_gy));}),_gQ=new T(function(){return B(A1(_gO,_gz));});return function(_gR){switch(E(_gR)){case 79:return E(_gP);case 88:return E(_gQ);case 111:return E(_gP);case 120:return E(_gQ);default:return new T0(2);}};},_gS=function(_gT){return new T1(0,B(_gN(_gT)));},_gU=10,_gV=function(_gW){return new F(function(){return A1(_gW,_gU);});},_gX=function(_gY,_gZ){var _h0=jsShowI(_gY);return new F(function(){return _O(fromJSStr(_h0),_gZ);});},_h1=41,_h2=40,_h3=function(_h4,_h5,_h6){if(_h5>=0){return new F(function(){return _gX(_h5,_h6);});}else{if(_h4<=6){return new F(function(){return _gX(_h5,_h6);});}else{return new T2(1,_h2,new T(function(){var _h7=jsShowI(_h5);return B(_O(fromJSStr(_h7),new T2(1,_h1,_h6)));}));}}},_h8=function(_h9){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_h3(9,_h9,_u));}))));});},_ha=function(_hb){var _hc=E(_hb);if(!_hc._){return E(_hc.a);}else{return new F(function(){return I_toInt(_hc.a);});}},_hd=function(_he,_hf){var _hg=E(_he);if(!_hg._){var _hh=_hg.a,_hi=E(_hf);return (_hi._==0)?_hh<=_hi.a:I_compareInt(_hi.a,_hh)>=0;}else{var _hj=_hg.a,_hk=E(_hf);return (_hk._==0)?I_compareInt(_hj,_hk.a)<=0:I_compare(_hj,_hk.a)<=0;}},_hl=function(_hm){return new T0(2);},_hn=function(_ho){var _hp=E(_ho);if(!_hp._){return E(_hl);}else{var _hq=_hp.a,_hr=E(_hp.b);if(!_hr._){return E(_hq);}else{var _hs=new T(function(){return B(_hn(_hr));}),_ht=function(_hu){return new F(function(){return _dE(B(A1(_hq,_hu)),new T(function(){return B(A1(_hs,_hu));}));});};return E(_ht);}}},_hv=function(_hw,_hx){var _hy=function(_hz,_hA,_hB){var _hC=E(_hz);if(!_hC._){return new F(function(){return A1(_hB,_hw);});}else{var _hD=E(_hA);if(!_hD._){return new T0(2);}else{if(E(_hC.a)!=E(_hD.a)){return new T0(2);}else{var _hE=new T(function(){return B(_hy(_hC.b,_hD.b,_hB));});return new T1(0,function(_hF){return E(_hE);});}}}};return function(_hG){return new F(function(){return _hy(_hw,_hG,_hx);});};},_hH=new T(function(){return B(unCStr("SO"));}),_hI=14,_hJ=function(_hK){var _hL=new T(function(){return B(A1(_hK,_hI));});return new T1(1,B(_hv(_hH,function(_hM){return E(_hL);})));},_hN=new T(function(){return B(unCStr("SOH"));}),_hO=1,_hP=function(_hQ){var _hR=new T(function(){return B(A1(_hQ,_hO));});return new T1(1,B(_hv(_hN,function(_hS){return E(_hR);})));},_hT=function(_hU){return new T1(1,B(_eX(_hP,_hJ,_hU)));},_hV=new T(function(){return B(unCStr("NUL"));}),_hW=0,_hX=function(_hY){var _hZ=new T(function(){return B(A1(_hY,_hW));});return new T1(1,B(_hv(_hV,function(_i0){return E(_hZ);})));},_i1=new T(function(){return B(unCStr("STX"));}),_i2=2,_i3=function(_i4){var _i5=new T(function(){return B(A1(_i4,_i2));});return new T1(1,B(_hv(_i1,function(_i6){return E(_i5);})));},_i7=new T(function(){return B(unCStr("ETX"));}),_i8=3,_i9=function(_ia){var _ib=new T(function(){return B(A1(_ia,_i8));});return new T1(1,B(_hv(_i7,function(_ic){return E(_ib);})));},_id=new T(function(){return B(unCStr("EOT"));}),_ie=4,_if=function(_ig){var _ih=new T(function(){return B(A1(_ig,_ie));});return new T1(1,B(_hv(_id,function(_ii){return E(_ih);})));},_ij=new T(function(){return B(unCStr("ENQ"));}),_ik=5,_il=function(_im){var _in=new T(function(){return B(A1(_im,_ik));});return new T1(1,B(_hv(_ij,function(_io){return E(_in);})));},_ip=new T(function(){return B(unCStr("ACK"));}),_iq=6,_ir=function(_is){var _it=new T(function(){return B(A1(_is,_iq));});return new T1(1,B(_hv(_ip,function(_iu){return E(_it);})));},_iv=new T(function(){return B(unCStr("BEL"));}),_iw=7,_ix=function(_iy){var _iz=new T(function(){return B(A1(_iy,_iw));});return new T1(1,B(_hv(_iv,function(_iA){return E(_iz);})));},_iB=new T(function(){return B(unCStr("BS"));}),_iC=8,_iD=function(_iE){var _iF=new T(function(){return B(A1(_iE,_iC));});return new T1(1,B(_hv(_iB,function(_iG){return E(_iF);})));},_iH=new T(function(){return B(unCStr("HT"));}),_iI=9,_iJ=function(_iK){var _iL=new T(function(){return B(A1(_iK,_iI));});return new T1(1,B(_hv(_iH,function(_iM){return E(_iL);})));},_iN=new T(function(){return B(unCStr("LF"));}),_iO=10,_iP=function(_iQ){var _iR=new T(function(){return B(A1(_iQ,_iO));});return new T1(1,B(_hv(_iN,function(_iS){return E(_iR);})));},_iT=new T(function(){return B(unCStr("VT"));}),_iU=11,_iV=function(_iW){var _iX=new T(function(){return B(A1(_iW,_iU));});return new T1(1,B(_hv(_iT,function(_iY){return E(_iX);})));},_iZ=new T(function(){return B(unCStr("FF"));}),_j0=12,_j1=function(_j2){var _j3=new T(function(){return B(A1(_j2,_j0));});return new T1(1,B(_hv(_iZ,function(_j4){return E(_j3);})));},_j5=new T(function(){return B(unCStr("CR"));}),_j6=13,_j7=function(_j8){var _j9=new T(function(){return B(A1(_j8,_j6));});return new T1(1,B(_hv(_j5,function(_ja){return E(_j9);})));},_jb=new T(function(){return B(unCStr("SI"));}),_jc=15,_jd=function(_je){var _jf=new T(function(){return B(A1(_je,_jc));});return new T1(1,B(_hv(_jb,function(_jg){return E(_jf);})));},_jh=new T(function(){return B(unCStr("DLE"));}),_ji=16,_jj=function(_jk){var _jl=new T(function(){return B(A1(_jk,_ji));});return new T1(1,B(_hv(_jh,function(_jm){return E(_jl);})));},_jn=new T(function(){return B(unCStr("DC1"));}),_jo=17,_jp=function(_jq){var _jr=new T(function(){return B(A1(_jq,_jo));});return new T1(1,B(_hv(_jn,function(_js){return E(_jr);})));},_jt=new T(function(){return B(unCStr("DC2"));}),_ju=18,_jv=function(_jw){var _jx=new T(function(){return B(A1(_jw,_ju));});return new T1(1,B(_hv(_jt,function(_jy){return E(_jx);})));},_jz=new T(function(){return B(unCStr("DC3"));}),_jA=19,_jB=function(_jC){var _jD=new T(function(){return B(A1(_jC,_jA));});return new T1(1,B(_hv(_jz,function(_jE){return E(_jD);})));},_jF=new T(function(){return B(unCStr("DC4"));}),_jG=20,_jH=function(_jI){var _jJ=new T(function(){return B(A1(_jI,_jG));});return new T1(1,B(_hv(_jF,function(_jK){return E(_jJ);})));},_jL=new T(function(){return B(unCStr("NAK"));}),_jM=21,_jN=function(_jO){var _jP=new T(function(){return B(A1(_jO,_jM));});return new T1(1,B(_hv(_jL,function(_jQ){return E(_jP);})));},_jR=new T(function(){return B(unCStr("SYN"));}),_jS=22,_jT=function(_jU){var _jV=new T(function(){return B(A1(_jU,_jS));});return new T1(1,B(_hv(_jR,function(_jW){return E(_jV);})));},_jX=new T(function(){return B(unCStr("ETB"));}),_jY=23,_jZ=function(_k0){var _k1=new T(function(){return B(A1(_k0,_jY));});return new T1(1,B(_hv(_jX,function(_k2){return E(_k1);})));},_k3=new T(function(){return B(unCStr("CAN"));}),_k4=24,_k5=function(_k6){var _k7=new T(function(){return B(A1(_k6,_k4));});return new T1(1,B(_hv(_k3,function(_k8){return E(_k7);})));},_k9=new T(function(){return B(unCStr("EM"));}),_ka=25,_kb=function(_kc){var _kd=new T(function(){return B(A1(_kc,_ka));});return new T1(1,B(_hv(_k9,function(_ke){return E(_kd);})));},_kf=new T(function(){return B(unCStr("SUB"));}),_kg=26,_kh=function(_ki){var _kj=new T(function(){return B(A1(_ki,_kg));});return new T1(1,B(_hv(_kf,function(_kk){return E(_kj);})));},_kl=new T(function(){return B(unCStr("ESC"));}),_km=27,_kn=function(_ko){var _kp=new T(function(){return B(A1(_ko,_km));});return new T1(1,B(_hv(_kl,function(_kq){return E(_kp);})));},_kr=new T(function(){return B(unCStr("FS"));}),_ks=28,_kt=function(_ku){var _kv=new T(function(){return B(A1(_ku,_ks));});return new T1(1,B(_hv(_kr,function(_kw){return E(_kv);})));},_kx=new T(function(){return B(unCStr("GS"));}),_ky=29,_kz=function(_kA){var _kB=new T(function(){return B(A1(_kA,_ky));});return new T1(1,B(_hv(_kx,function(_kC){return E(_kB);})));},_kD=new T(function(){return B(unCStr("RS"));}),_kE=30,_kF=function(_kG){var _kH=new T(function(){return B(A1(_kG,_kE));});return new T1(1,B(_hv(_kD,function(_kI){return E(_kH);})));},_kJ=new T(function(){return B(unCStr("US"));}),_kK=31,_kL=function(_kM){var _kN=new T(function(){return B(A1(_kM,_kK));});return new T1(1,B(_hv(_kJ,function(_kO){return E(_kN);})));},_kP=new T(function(){return B(unCStr("SP"));}),_kQ=32,_kR=function(_kS){var _kT=new T(function(){return B(A1(_kS,_kQ));});return new T1(1,B(_hv(_kP,function(_kU){return E(_kT);})));},_kV=new T(function(){return B(unCStr("DEL"));}),_kW=127,_kX=function(_kY){var _kZ=new T(function(){return B(A1(_kY,_kW));});return new T1(1,B(_hv(_kV,function(_l0){return E(_kZ);})));},_l1=new T2(1,_kX,_u),_l2=new T2(1,_kR,_l1),_l3=new T2(1,_kL,_l2),_l4=new T2(1,_kF,_l3),_l5=new T2(1,_kz,_l4),_l6=new T2(1,_kt,_l5),_l7=new T2(1,_kn,_l6),_l8=new T2(1,_kh,_l7),_l9=new T2(1,_kb,_l8),_la=new T2(1,_k5,_l9),_lb=new T2(1,_jZ,_la),_lc=new T2(1,_jT,_lb),_ld=new T2(1,_jN,_lc),_le=new T2(1,_jH,_ld),_lf=new T2(1,_jB,_le),_lg=new T2(1,_jv,_lf),_lh=new T2(1,_jp,_lg),_li=new T2(1,_jj,_lh),_lj=new T2(1,_jd,_li),_lk=new T2(1,_j7,_lj),_ll=new T2(1,_j1,_lk),_lm=new T2(1,_iV,_ll),_ln=new T2(1,_iP,_lm),_lo=new T2(1,_iJ,_ln),_lp=new T2(1,_iD,_lo),_lq=new T2(1,_ix,_lp),_lr=new T2(1,_ir,_lq),_ls=new T2(1,_il,_lr),_lt=new T2(1,_if,_ls),_lu=new T2(1,_i9,_lt),_lv=new T2(1,_i3,_lu),_lw=new T2(1,_hX,_lv),_lx=new T2(1,_hT,_lw),_ly=new T(function(){return B(_hn(_lx));}),_lz=new T1(0,1114111),_lA=34,_lB=39,_lC=92,_lD=function(_lE){return new T1(0,_lE);},_lF=function(_lG,_lH){while(1){var _lI=E(_lG);if(!_lI._){return E(_lH);}else{var _lJ=_lH+1|0;_lG=_lI.b;_lH=_lJ;continue;}}},_lK=function(_lL,_lM){var _lN=E(_lM);return (_lN._==0)?__Z:new T2(1,new T(function(){return B(A1(_lL,_lN.a));}),new T(function(){return B(_lK(_lL,_lN.b));}));},_lO=function(_lP){return new F(function(){return _lD(E(_lP));});},_lQ=new T(function(){return B(unCStr("this should not happen"));}),_lR=new T(function(){return B(err(_lQ));}),_lS=function(_lT,_lU){while(1){var _lV=E(_lT);if(!_lV._){var _lW=_lV.a,_lX=E(_lU);if(!_lX._){var _lY=_lX.a,_lZ=addC(_lW,_lY);if(!E(_lZ.b)){return new T1(0,_lZ.a);}else{_lT=new T1(1,I_fromInt(_lW));_lU=new T1(1,I_fromInt(_lY));continue;}}else{_lT=new T1(1,I_fromInt(_lW));_lU=_lX;continue;}}else{var _m0=E(_lU);if(!_m0._){_lT=_lV;_lU=new T1(1,I_fromInt(_m0.a));continue;}else{return new T1(1,I_add(_lV.a,_m0.a));}}}},_m1=function(_m2,_m3){while(1){var _m4=E(_m2);if(!_m4._){var _m5=_m4.a,_m6=E(_m3);if(!_m6._){var _m7=_m6.a;if(!(imul(_m5,_m7)|0)){return new T1(0,imul(_m5,_m7)|0);}else{_m2=new T1(1,I_fromInt(_m5));_m3=new T1(1,I_fromInt(_m7));continue;}}else{_m2=new T1(1,I_fromInt(_m5));_m3=_m6;continue;}}else{var _m8=E(_m3);if(!_m8._){_m2=_m4;_m3=new T1(1,I_fromInt(_m8.a));continue;}else{return new T1(1,I_mul(_m4.a,_m8.a));}}}},_m9=function(_ma,_mb){var _mc=E(_mb);if(!_mc._){return __Z;}else{var _md=E(_mc.b);return (_md._==0)?E(_lR):new T2(1,B(_lS(B(_m1(_mc.a,_ma)),_md.a)),new T(function(){return B(_m9(_ma,_md.b));}));}},_me=new T1(0,0),_mf=function(_mg,_mh,_mi){while(1){var _mj=B((function(_mk,_ml,_mm){var _mn=E(_mm);if(!_mn._){return E(_me);}else{if(!E(_mn.b)._){return E(_mn.a);}else{var _mo=E(_ml);if(_mo<=40){var _mp=function(_mq,_mr){while(1){var _ms=E(_mr);if(!_ms._){return E(_mq);}else{var _mt=B(_lS(B(_m1(_mq,_mk)),_ms.a));_mq=_mt;_mr=_ms.b;continue;}}};return new F(function(){return _mp(_me,_mn);});}else{var _mu=B(_m1(_mk,_mk));if(!(_mo%2)){var _mv=B(_m9(_mk,_mn));_mg=_mu;_mh=quot(_mo+1|0,2);_mi=_mv;return __continue;}else{var _mv=B(_m9(_mk,new T2(1,_me,_mn)));_mg=_mu;_mh=quot(_mo+1|0,2);_mi=_mv;return __continue;}}}}})(_mg,_mh,_mi));if(_mj!=__continue){return _mj;}}},_mw=function(_mx,_my){return new F(function(){return _mf(_mx,new T(function(){return B(_lF(_my,0));},1),B(_lK(_lO,_my)));});},_mz=function(_mA){var _mB=new T(function(){return B(A1(_mA,_iw));}),_mC=new T(function(){return B(A1(_mA,_iC));}),_mD=new T(function(){return B(A1(_mA,_iI));}),_mE=new T(function(){return B(A1(_mA,_iO));}),_mF=new T(function(){return B(A1(_mA,_iU));}),_mG=new T(function(){return B(A1(_mA,_j0));}),_mH=new T(function(){return B(A1(_mA,_j6));}),_mI=new T(function(){return B(A1(_mA,_lC));}),_mJ=new T(function(){return B(A1(_mA,_lB));}),_mK=new T(function(){return B(A1(_mA,_lA));}),_mL=new T(function(){var _mM=function(_mN){var _mO=new T(function(){return B(_lD(E(_mN)));}),_mP=function(_mQ){var _mR=B(_mw(_mO,_mQ));if(!B(_hd(_mR,_lz))){return new T0(2);}else{return new F(function(){return A1(_mA,new T(function(){var _mS=B(_ha(_mR));if(_mS>>>0>1114111){return B(_h8(_mS));}else{return _mS;}}));});}};return new T1(1,B(_fO(_mN,_mP)));},_mT=new T(function(){var _mU=new T(function(){return B(A1(_mA,_kK));}),_mV=new T(function(){return B(A1(_mA,_kE));}),_mW=new T(function(){return B(A1(_mA,_ky));}),_mX=new T(function(){return B(A1(_mA,_ks));}),_mY=new T(function(){return B(A1(_mA,_km));}),_mZ=new T(function(){return B(A1(_mA,_kg));}),_n0=new T(function(){return B(A1(_mA,_ka));}),_n1=new T(function(){return B(A1(_mA,_k4));}),_n2=new T(function(){return B(A1(_mA,_jY));}),_n3=new T(function(){return B(A1(_mA,_jS));}),_n4=new T(function(){return B(A1(_mA,_jM));}),_n5=new T(function(){return B(A1(_mA,_jG));}),_n6=new T(function(){return B(A1(_mA,_jA));}),_n7=new T(function(){return B(A1(_mA,_ju));}),_n8=new T(function(){return B(A1(_mA,_jo));}),_n9=new T(function(){return B(A1(_mA,_ji));}),_na=new T(function(){return B(A1(_mA,_jc));}),_nb=new T(function(){return B(A1(_mA,_hI));}),_nc=new T(function(){return B(A1(_mA,_iq));}),_nd=new T(function(){return B(A1(_mA,_ik));}),_ne=new T(function(){return B(A1(_mA,_ie));}),_nf=new T(function(){return B(A1(_mA,_i8));}),_ng=new T(function(){return B(A1(_mA,_i2));}),_nh=new T(function(){return B(A1(_mA,_hO));}),_ni=new T(function(){return B(A1(_mA,_hW));}),_nj=function(_nk){switch(E(_nk)){case 64:return E(_ni);case 65:return E(_nh);case 66:return E(_ng);case 67:return E(_nf);case 68:return E(_ne);case 69:return E(_nd);case 70:return E(_nc);case 71:return E(_mB);case 72:return E(_mC);case 73:return E(_mD);case 74:return E(_mE);case 75:return E(_mF);case 76:return E(_mG);case 77:return E(_mH);case 78:return E(_nb);case 79:return E(_na);case 80:return E(_n9);case 81:return E(_n8);case 82:return E(_n7);case 83:return E(_n6);case 84:return E(_n5);case 85:return E(_n4);case 86:return E(_n3);case 87:return E(_n2);case 88:return E(_n1);case 89:return E(_n0);case 90:return E(_mZ);case 91:return E(_mY);case 92:return E(_mX);case 93:return E(_mW);case 94:return E(_mV);case 95:return E(_mU);default:return new T0(2);}};return B(_dE(new T1(0,function(_nl){return (E(_nl)==94)?E(new T1(0,_nj)):new T0(2);}),new T(function(){return B(A1(_ly,_mA));})));});return B(_dE(new T1(1,B(_eX(_gS,_gV,_mM))),_mT));});return new F(function(){return _dE(new T1(0,function(_nm){switch(E(_nm)){case 34:return E(_mK);case 39:return E(_mJ);case 92:return E(_mI);case 97:return E(_mB);case 98:return E(_mC);case 102:return E(_mG);case 110:return E(_mE);case 114:return E(_mH);case 116:return E(_mD);case 118:return E(_mF);default:return new T0(2);}}),_mL);});},_nn=function(_no){return new F(function(){return A1(_no,_2u);});},_np=function(_nq){var _nr=E(_nq);if(!_nr._){return E(_nn);}else{var _ns=E(_nr.a),_nt=_ns>>>0,_nu=new T(function(){return B(_np(_nr.b));});if(_nt>887){var _nv=u_iswspace(_ns);if(!E(_nv)){return E(_nn);}else{var _nw=function(_nx){var _ny=new T(function(){return B(A1(_nu,_nx));});return new T1(0,function(_nz){return E(_ny);});};return E(_nw);}}else{var _nA=E(_nt);if(_nA==32){var _nB=function(_nC){var _nD=new T(function(){return B(A1(_nu,_nC));});return new T1(0,function(_nE){return E(_nD);});};return E(_nB);}else{if(_nA-9>>>0>4){if(E(_nA)==160){var _nF=function(_nG){var _nH=new T(function(){return B(A1(_nu,_nG));});return new T1(0,function(_nI){return E(_nH);});};return E(_nF);}else{return E(_nn);}}else{var _nJ=function(_nK){var _nL=new T(function(){return B(A1(_nu,_nK));});return new T1(0,function(_nM){return E(_nL);});};return E(_nJ);}}}}},_nN=function(_nO){var _nP=new T(function(){return B(_nN(_nO));}),_nQ=function(_nR){return (E(_nR)==92)?E(_nP):new T0(2);},_nS=function(_nT){return E(new T1(0,_nQ));},_nU=new T1(1,function(_nV){return new F(function(){return A2(_np,_nV,_nS);});}),_nW=new T(function(){return B(_mz(function(_nX){return new F(function(){return A1(_nO,new T2(0,_nX,_gM));});}));}),_nY=function(_nZ){var _o0=E(_nZ);if(_o0==38){return E(_nP);}else{var _o1=_o0>>>0;if(_o1>887){var _o2=u_iswspace(_o0);return (E(_o2)==0)?new T0(2):E(_nU);}else{var _o3=E(_o1);return (_o3==32)?E(_nU):(_o3-9>>>0>4)?(E(_o3)==160)?E(_nU):new T0(2):E(_nU);}}};return new F(function(){return _dE(new T1(0,function(_o4){return (E(_o4)==92)?E(new T1(0,_nY)):new T0(2);}),new T1(0,function(_o5){var _o6=E(_o5);if(E(_o6)==92){return E(_nW);}else{return new F(function(){return A1(_nO,new T2(0,_o6,_gL));});}}));});},_o7=function(_o8,_o9){var _oa=new T(function(){return B(A1(_o9,new T1(1,new T(function(){return B(A1(_o8,_u));}))));}),_ob=function(_oc){var _od=E(_oc),_oe=E(_od.a);if(E(_oe)==34){if(!E(_od.b)){return E(_oa);}else{return new F(function(){return _o7(function(_of){return new F(function(){return A1(_o8,new T2(1,_oe,_of));});},_o9);});}}else{return new F(function(){return _o7(function(_og){return new F(function(){return A1(_o8,new T2(1,_oe,_og));});},_o9);});}};return new F(function(){return _nN(_ob);});},_oh=function(_oi){var _oj=function(_ok){return new F(function(){return A1(_oi,new T1(1,_ok));});};return function(_ol){return (E(_ol)==46)?new T1(1,B(_fO(_gU,_oj))):new T0(2);};},_om=function(_on){return new T1(0,B(_oh(_on)));},_oo=new T1(0,1),_op=new T1(0,2147483647),_oq=new T(function(){return B(_lS(_op,_oo));}),_or=function(_os){var _ot=E(_os);if(!_ot._){var _ou=E(_ot.a);return (_ou==( -2147483648))?E(_oq):new T1(0, -_ou);}else{return new T1(1,I_negate(_ot.a));}},_ov=new T1(0,10),_ow=function(_ox){var _oy=new T(function(){var _oz=new T(function(){var _oA=function(_oB){return new F(function(){return A1(_ox,new T1(1,new T(function(){return B(_mw(_ov,_oB));})));});};return new T1(1,B(_fO(_gU,_oA)));}),_oC=function(_oD){if(E(_oD)==43){var _oE=function(_oF){return new F(function(){return A1(_ox,new T1(1,new T(function(){return B(_mw(_ov,_oF));})));});};return new T1(1,B(_fO(_gU,_oE)));}else{return new T0(2);}},_oG=function(_oH){if(E(_oH)==45){var _oI=function(_oJ){return new F(function(){return A1(_ox,new T1(1,new T(function(){return B(_or(B(_mw(_ov,_oJ))));})));});};return new T1(1,B(_fO(_gU,_oI)));}else{return new T0(2);}};return B(_dE(B(_dE(new T1(0,_oG),new T1(0,_oC))),_oz));});return new F(function(){return _dE(new T1(0,function(_oK){return (E(_oK)==101)?E(_oy):new T0(2);}),new T1(0,function(_oL){return (E(_oL)==69)?E(_oy):new T0(2);}));});},_oM=function(_oN){return new F(function(){return A1(_oN,_2a);});},_oO=function(_oP){return new F(function(){return A1(_oP,_2a);});},_oQ=function(_oR){var _oS=function(_oT){var _oU=function(_oV){return new T1(1,B(_eX(_ow,_oO,function(_oW){return new F(function(){return A1(_oR,new T1(5,new T3(1,_oT,_oV,_oW)));});})));};return new T1(1,B(_eX(_om,_oM,_oU)));};return new F(function(){return _fO(_gU,_oS);});},_oX=function(_oY){return new T1(1,B(_oQ(_oY)));},_oZ=new T(function(){return B(unCStr("_\'"));}),_p0=function(_p1){var _p2=u_iswalnum(_p1);if(!E(_p2)){return new F(function(){return _fE(_et,_p1,_oZ);});}else{return true;}},_p3=function(_p4){return new F(function(){return _p0(E(_p4));});},_p5=new T(function(){return B(unCStr(",;()[]{}`"));}),_p6=new T(function(){return B(unCStr(".."));}),_p7=new T(function(){return B(unCStr("::"));}),_p8=new T(function(){return B(unCStr("=>"));}),_p9=new T2(1,_p8,_u),_pa=new T(function(){return B(unCStr("~"));}),_pb=new T2(1,_pa,_p9),_pc=new T(function(){return B(unCStr("@"));}),_pd=new T2(1,_pc,_pb),_pe=new T(function(){return B(unCStr("->"));}),_pf=new T2(1,_pe,_pd),_pg=new T(function(){return B(unCStr("<-"));}),_ph=new T2(1,_pg,_pf),_pi=new T(function(){return B(unCStr("|"));}),_pj=new T2(1,_pi,_ph),_pk=new T(function(){return B(unCStr("\\"));}),_pl=new T2(1,_pk,_pj),_pm=new T(function(){return B(unCStr("="));}),_pn=new T2(1,_pm,_pl),_po=new T2(1,_p7,_pn),_pp=new T2(1,_p6,_po),_pq=function(_pr){var _ps=new T(function(){return B(A1(_pr,_fB));}),_pt=new T(function(){var _pu=new T(function(){var _pv=function(_pw){var _px=new T(function(){return B(A1(_pr,new T1(0,_pw)));});return new T1(0,function(_py){return (E(_py)==39)?E(_px):new T0(2);});};return B(_mz(_pv));}),_pz=function(_pA){var _pB=E(_pA);switch(E(_pB)){case 39:return new T0(2);case 92:return E(_pu);default:var _pC=new T(function(){return B(A1(_pr,new T1(0,_pB)));});return new T1(0,function(_pD){return (E(_pD)==39)?E(_pC):new T0(2);});}},_pE=new T(function(){var _pF=new T(function(){return B(_o7(_2q,_pr));}),_pG=new T(function(){var _pH=new T(function(){var _pI=new T(function(){var _pJ=function(_pK){var _pL=E(_pK),_pM=u_iswalpha(_pL);return (E(_pM)==0)?(E(_pL)==95)?new T1(1,B(_fn(_p3,function(_pN){return new F(function(){return A1(_pr,new T1(3,new T2(1,_pL,_pN)));});}))):new T0(2):new T1(1,B(_fn(_p3,function(_pO){return new F(function(){return A1(_pr,new T1(3,new T2(1,_pL,_pO)));});})));};return B(_dE(new T1(0,_pJ),new T(function(){return new T1(1,B(_eX(_gJ,_oX,_pr)));})));}),_pP=function(_pQ){return (!B(_fE(_et,_pQ,_fJ)))?new T0(2):new T1(1,B(_fn(_fK,function(_pR){var _pS=new T2(1,_pQ,_pR);if(!B(_fE(_eC,_pS,_pp))){return new F(function(){return A1(_pr,new T1(4,_pS));});}else{return new F(function(){return A1(_pr,new T1(2,_pS));});}})));};return B(_dE(new T1(0,_pP),_pI));});return B(_dE(new T1(0,function(_pT){if(!B(_fE(_et,_pT,_p5))){return new T0(2);}else{return new F(function(){return A1(_pr,new T1(2,new T2(1,_pT,_u)));});}}),_pH));});return B(_dE(new T1(0,function(_pU){return (E(_pU)==34)?E(_pF):new T0(2);}),_pG));});return B(_dE(new T1(0,function(_pV){return (E(_pV)==39)?E(new T1(0,_pz)):new T0(2);}),_pE));});return new F(function(){return _dE(new T1(1,function(_pW){return (E(_pW)._==0)?E(_ps):new T0(2);}),_pt);});},_pX=0,_pY=function(_pZ,_q0){var _q1=new T(function(){var _q2=new T(function(){var _q3=function(_q4){var _q5=new T(function(){var _q6=new T(function(){return B(A1(_q0,_q4));});return B(_pq(function(_q7){var _q8=E(_q7);return (_q8._==2)?(!B(_ei(_q8.a,_eh)))?new T0(2):E(_q6):new T0(2);}));}),_q9=function(_qa){return E(_q5);};return new T1(1,function(_qb){return new F(function(){return A2(_np,_qb,_q9);});});};return B(A2(_pZ,_pX,_q3));});return B(_pq(function(_qc){var _qd=E(_qc);return (_qd._==2)?(!B(_ei(_qd.a,_eg)))?new T0(2):E(_q2):new T0(2);}));}),_qe=function(_qf){return E(_q1);};return function(_qg){return new F(function(){return A2(_np,_qg,_qe);});};},_qh=function(_qi,_qj){var _qk=function(_ql){var _qm=new T(function(){return B(A1(_qi,_ql));}),_qn=function(_qo){return new F(function(){return _dE(B(A1(_qm,_qo)),new T(function(){return new T1(1,B(_pY(_qk,_qo)));}));});};return E(_qn);},_qp=new T(function(){return B(A1(_qi,_qj));}),_qq=function(_qr){return new F(function(){return _dE(B(A1(_qp,_qr)),new T(function(){return new T1(1,B(_pY(_qk,_qr)));}));});};return E(_qq);},_qs=function(_qt,_qu){var _qv=function(_qw,_qx){var _qy=function(_qz){return new F(function(){return A1(_qx,new T(function(){return  -E(_qz);}));});},_qA=new T(function(){return B(_pq(function(_qB){return new F(function(){return A3(_qt,_qB,_qw,_qy);});}));}),_qC=function(_qD){return E(_qA);},_qE=function(_qF){return new F(function(){return A2(_np,_qF,_qC);});},_qG=new T(function(){return B(_pq(function(_qH){var _qI=E(_qH);if(_qI._==4){var _qJ=E(_qI.a);if(!_qJ._){return new F(function(){return A3(_qt,_qI,_qw,_qx);});}else{if(E(_qJ.a)==45){if(!E(_qJ.b)._){return E(new T1(1,_qE));}else{return new F(function(){return A3(_qt,_qI,_qw,_qx);});}}else{return new F(function(){return A3(_qt,_qI,_qw,_qx);});}}}else{return new F(function(){return A3(_qt,_qI,_qw,_qx);});}}));}),_qK=function(_qL){return E(_qG);};return new T1(1,function(_qM){return new F(function(){return A2(_np,_qM,_qK);});});};return new F(function(){return _qh(_qv,_qu);});},_qN=function(_qO){var _qP=E(_qO);if(!_qP._){var _qQ=_qP.b,_qR=new T(function(){return B(_mf(new T(function(){return B(_lD(E(_qP.a)));}),new T(function(){return B(_lF(_qQ,0));},1),B(_lK(_lO,_qQ))));});return new T1(1,_qR);}else{return (E(_qP.b)._==0)?(E(_qP.c)._==0)?new T1(1,new T(function(){return B(_mw(_ov,_qP.a));})):__Z:__Z;}},_qS=function(_qT,_qU){return new T0(2);},_qV=function(_qW){var _qX=E(_qW);if(_qX._==5){var _qY=B(_qN(_qX.a));if(!_qY._){return E(_qS);}else{var _qZ=new T(function(){return B(_ha(_qY.a));});return function(_r0,_r1){return new F(function(){return A1(_r1,_qZ);});};}}else{return E(_qS);}},_r2=function(_r3){var _r4=function(_r5){return E(new T2(3,_r3,_eO));};return new T1(1,function(_r6){return new F(function(){return A2(_np,_r6,_r4);});});},_r7=new T(function(){return B(A3(_qs,_qV,_pX,_r2));}),_r8=new T(function(){return B(unCStr(": empty list"));}),_r9=new T(function(){return B(unCStr("Prelude."));}),_ra=function(_rb){return new F(function(){return err(B(_O(_r9,new T(function(){return B(_O(_rb,_r8));},1))));});},_rc=new T(function(){return B(unCStr("head"));}),_rd=new T(function(){return B(_ra(_rc));}),_re=function(_rf,_rg){return E(_rf);},_rh=new T(function(){return B(unCStr("5 5"));}),_ri=function(_rj,_rk){var _rl=E(_rk);if(!_rl._){return new T2(0,_u,_u);}else{var _rm=_rl.a;if(!B(A1(_rj,_rm))){var _rn=new T(function(){var _ro=B(_ri(_rj,_rl.b));return new T2(0,_ro.a,_ro.b);});return new T2(0,new T2(1,_rm,new T(function(){return E(E(_rn).a);})),new T(function(){return E(E(_rn).b);}));}else{return new T2(0,_u,_rl);}}},_rp=function(_rq,_rr){while(1){var _rs=E(_rr);if(!_rs._){return __Z;}else{if(!B(A1(_rq,_rs.a))){return E(_rs);}else{_rr=_rs.b;continue;}}}},_rt=function(_ru){var _rv=_ru>>>0;if(_rv>887){var _rw=u_iswspace(_ru);return (E(_rw)==0)?false:true;}else{var _rx=E(_rv);return (_rx==32)?true:(_rx-9>>>0>4)?(E(_rx)==160)?true:false:true;}},_ry=function(_rz){return new F(function(){return _rt(E(_rz));});},_rA=function(_rB,_rC,_rD){var _rE=function(_rF){var _rG=B(_rp(_ry,_rF));if(!_rG._){return E(_rC);}else{var _rH=new T(function(){var _rI=B(_ri(_ry,_rG));return new T2(0,_rI.a,_rI.b);});return new F(function(){return A2(_rB,new T(function(){return E(E(_rH).a);}),new T(function(){return B(_rE(E(_rH).b));}));});}};return new F(function(){return _rE(_rD);});},_rJ=new T(function(){return B(_rA(_re,_rd,_rh));}),_rK=new T(function(){return B(_du(_r7,_rJ));}),_rL=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_rM=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_rN=function(_rO){while(1){var _rP=B((function(_rQ){var _rR=E(_rQ);if(!_rR._){return __Z;}else{var _rS=_rR.b,_rT=E(_rR.a);if(!E(_rT.b)._){return new T2(1,_rT.a,new T(function(){return B(_rN(_rS));}));}else{_rO=_rS;return __continue;}}})(_rO));if(_rP!=__continue){return _rP;}}},_rU=new T(function(){var _rV=B(_rN(_rK));if(!_rV._){return B(err(_rM));}else{if(!E(_rV.b)._){return E(_rV.a);}else{return B(err(_rL));}}}),_rW=new T(function(){return B(unCStr("tail"));}),_rX=new T(function(){return B(_ra(_rW));}),_rY=function(_rZ){var _s0=B(_rp(_ry,_rZ));if(!_s0._){return __Z;}else{var _s1=new T(function(){var _s2=B(_ri(_ry,_s0));return new T2(0,_s2.a,_s2.b);});return new T2(1,new T(function(){return E(E(_s1).a);}),new T(function(){return B(_rY(E(_s1).b));}));}},_s3=new T(function(){var _s4=B(_rY(_rh));if(!_s4._){return E(_rX);}else{var _s5=E(_s4.b);if(!_s5._){return E(_rd);}else{return E(_s5.a);}}}),_s6=new T(function(){return B(_du(_r7,_s3));}),_s7=new T(function(){var _s8=B(_rN(_s6));if(!_s8._){return B(err(_rM));}else{if(!E(_s8.b)._){return E(_s8.a);}else{return B(err(_rL));}}}),_s9=1,_sa=new T(function(){return B(_dk(E(_rU)-1|0,_s7,_s9,0,_cZ,_cY));}),_sb=0,_sc=new T(function(){return B(unCStr("0 0 10 0"));}),_sd=new T(function(){return B(_rY(_sc));}),_se=new T(function(){return B(err(_rL));}),_sf=new T(function(){return B(err(_rM));}),_sg=function(_sh){return new F(function(){return _4B("jsEther.hs:(76,1)-(79,69)|function makeList");});},_si=new T(function(){return B(_sg(_));}),_sj=function(_sk,_sl){var _sm=function(_sn,_so){var _sp=function(_sq){return new F(function(){return A1(_so,new T(function(){return  -E(_sq);}));});},_sr=new T(function(){return B(_pq(function(_ss){return new F(function(){return A3(_sk,_ss,_sn,_sp);});}));}),_st=function(_su){return E(_sr);},_sv=function(_sw){return new F(function(){return A2(_np,_sw,_st);});},_sx=new T(function(){return B(_pq(function(_sy){var _sz=E(_sy);if(_sz._==4){var _sA=E(_sz.a);if(!_sA._){return new F(function(){return A3(_sk,_sz,_sn,_so);});}else{if(E(_sA.a)==45){if(!E(_sA.b)._){return E(new T1(1,_sv));}else{return new F(function(){return A3(_sk,_sz,_sn,_so);});}}else{return new F(function(){return A3(_sk,_sz,_sn,_so);});}}}else{return new F(function(){return A3(_sk,_sz,_sn,_so);});}}));}),_sB=function(_sC){return E(_sx);};return new T1(1,function(_sD){return new F(function(){return A2(_np,_sD,_sB);});});};return new F(function(){return _qh(_sm,_sl);});},_sE=new T(function(){return B(unCStr("NaN"));}),_sF=new T(function(){return B(unCStr("Infinity"));}),_sG=new T(function(){return 1/0;}),_sH=function(_sI,_sJ){return new F(function(){return A1(_sJ,_sG);});},_sK=new T(function(){return 0/0;}),_sL=function(_sM,_sN){return new F(function(){return A1(_sN,_sK);});},_sO=1024,_sP= -1021,_sQ=new T(function(){return B(unCStr("base"));}),_sR=new T(function(){return B(unCStr("GHC.Exception"));}),_sS=new T(function(){return B(unCStr("ArithException"));}),_sT=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_sQ,_sR,_sS),_sU=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_sT,_u,_u),_sV=function(_sW){return E(_sU);},_sX=function(_sY){var _sZ=E(_sY);return new F(function(){return _A(B(_y(_sZ.a)),_sV,_sZ.b);});},_t0=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_t1=new T(function(){return B(unCStr("denormal"));}),_t2=new T(function(){return B(unCStr("divide by zero"));}),_t3=new T(function(){return B(unCStr("loss of precision"));}),_t4=new T(function(){return B(unCStr("arithmetic underflow"));}),_t5=new T(function(){return B(unCStr("arithmetic overflow"));}),_t6=function(_t7,_t8){switch(E(_t7)){case 0:return new F(function(){return _O(_t5,_t8);});break;case 1:return new F(function(){return _O(_t4,_t8);});break;case 2:return new F(function(){return _O(_t3,_t8);});break;case 3:return new F(function(){return _O(_t2,_t8);});break;case 4:return new F(function(){return _O(_t1,_t8);});break;default:return new F(function(){return _O(_t0,_t8);});}},_t9=function(_ta){return new F(function(){return _t6(_ta,_u);});},_tb=function(_tc,_td,_te){return new F(function(){return _t6(_td,_te);});},_tf=function(_tg,_th){return new F(function(){return _1S(_t6,_tg,_th);});},_ti=new T3(0,_tb,_t9,_tf),_tj=new T(function(){return new T5(0,_sV,_ti,_tk,_sX,_t9);}),_tk=function(_4e){return new T2(0,_tj,_4e);},_tl=3,_tm=new T(function(){return B(_tk(_tl));}),_tn=new T(function(){return die(_tm);}),_to=function(_tp,_tq){var _tr=E(_tp);if(!_tr._){var _ts=_tr.a,_tt=E(_tq);return (_tt._==0)?_ts==_tt.a:(I_compareInt(_tt.a,_ts)==0)?true:false;}else{var _tu=_tr.a,_tv=E(_tq);return (_tv._==0)?(I_compareInt(_tu,_tv.a)==0)?true:false:(I_compare(_tu,_tv.a)==0)?true:false;}},_tw=new T1(0,0),_tx=function(_ty,_tz){while(1){var _tA=E(_ty);if(!_tA._){var _tB=E(_tA.a);if(_tB==( -2147483648)){_ty=new T1(1,I_fromInt( -2147483648));continue;}else{var _tC=E(_tz);if(!_tC._){return new T1(0,_tB%_tC.a);}else{_ty=new T1(1,I_fromInt(_tB));_tz=_tC;continue;}}}else{var _tD=_tA.a,_tE=E(_tz);return (_tE._==0)?new T1(1,I_rem(_tD,I_fromInt(_tE.a))):new T1(1,I_rem(_tD,_tE.a));}}},_tF=function(_tG,_tH){if(!B(_to(_tH,_tw))){return new F(function(){return _tx(_tG,_tH);});}else{return E(_tn);}},_tI=function(_tJ,_tK){while(1){if(!B(_to(_tK,_tw))){var _tL=_tK,_tM=B(_tF(_tJ,_tK));_tJ=_tL;_tK=_tM;continue;}else{return E(_tJ);}}},_tN=function(_tO){var _tP=E(_tO);if(!_tP._){var _tQ=E(_tP.a);return (_tQ==( -2147483648))?E(_oq):(_tQ<0)?new T1(0, -_tQ):E(_tP);}else{var _tR=_tP.a;return (I_compareInt(_tR,0)>=0)?E(_tP):new T1(1,I_negate(_tR));}},_tS=function(_tT,_tU){while(1){var _tV=E(_tT);if(!_tV._){var _tW=E(_tV.a);if(_tW==( -2147483648)){_tT=new T1(1,I_fromInt( -2147483648));continue;}else{var _tX=E(_tU);if(!_tX._){return new T1(0,quot(_tW,_tX.a));}else{_tT=new T1(1,I_fromInt(_tW));_tU=_tX;continue;}}}else{var _tY=_tV.a,_tZ=E(_tU);return (_tZ._==0)?new T1(0,I_toInt(I_quot(_tY,I_fromInt(_tZ.a)))):new T1(1,I_quot(_tY,_tZ.a));}}},_u0=5,_u1=new T(function(){return B(_tk(_u0));}),_u2=new T(function(){return die(_u1);}),_u3=function(_u4,_u5){if(!B(_to(_u5,_tw))){var _u6=B(_tI(B(_tN(_u4)),B(_tN(_u5))));return (!B(_to(_u6,_tw)))?new T2(0,B(_tS(_u4,_u6)),B(_tS(_u5,_u6))):E(_tn);}else{return E(_u2);}},_u7=new T1(0,1),_u8=new T(function(){return B(unCStr("Negative exponent"));}),_u9=new T(function(){return B(err(_u8));}),_ua=new T1(0,2),_ub=new T(function(){return B(_to(_ua,_tw));}),_uc=function(_ud,_ue){while(1){var _uf=E(_ud);if(!_uf._){var _ug=_uf.a,_uh=E(_ue);if(!_uh._){var _ui=_uh.a,_uj=subC(_ug,_ui);if(!E(_uj.b)){return new T1(0,_uj.a);}else{_ud=new T1(1,I_fromInt(_ug));_ue=new T1(1,I_fromInt(_ui));continue;}}else{_ud=new T1(1,I_fromInt(_ug));_ue=_uh;continue;}}else{var _uk=E(_ue);if(!_uk._){_ud=_uf;_ue=new T1(1,I_fromInt(_uk.a));continue;}else{return new T1(1,I_sub(_uf.a,_uk.a));}}}},_ul=function(_um,_un,_uo){while(1){if(!E(_ub)){if(!B(_to(B(_tx(_un,_ua)),_tw))){if(!B(_to(_un,_u7))){var _up=B(_m1(_um,_um)),_uq=B(_tS(B(_uc(_un,_u7)),_ua)),_ur=B(_m1(_um,_uo));_um=_up;_un=_uq;_uo=_ur;continue;}else{return new F(function(){return _m1(_um,_uo);});}}else{var _up=B(_m1(_um,_um)),_uq=B(_tS(_un,_ua));_um=_up;_un=_uq;continue;}}else{return E(_tn);}}},_us=function(_ut,_uu){while(1){if(!E(_ub)){if(!B(_to(B(_tx(_uu,_ua)),_tw))){if(!B(_to(_uu,_u7))){return new F(function(){return _ul(B(_m1(_ut,_ut)),B(_tS(B(_uc(_uu,_u7)),_ua)),_ut);});}else{return E(_ut);}}else{var _uv=B(_m1(_ut,_ut)),_uw=B(_tS(_uu,_ua));_ut=_uv;_uu=_uw;continue;}}else{return E(_tn);}}},_ux=function(_uy,_uz){var _uA=E(_uy);if(!_uA._){var _uB=_uA.a,_uC=E(_uz);return (_uC._==0)?_uB<_uC.a:I_compareInt(_uC.a,_uB)>0;}else{var _uD=_uA.a,_uE=E(_uz);return (_uE._==0)?I_compareInt(_uD,_uE.a)<0:I_compare(_uD,_uE.a)<0;}},_uF=function(_uG,_uH){if(!B(_ux(_uH,_tw))){if(!B(_to(_uH,_tw))){return new F(function(){return _us(_uG,_uH);});}else{return E(_u7);}}else{return E(_u9);}},_uI=new T1(0,1),_uJ=new T1(0,0),_uK=new T1(0, -1),_uL=function(_uM){var _uN=E(_uM);if(!_uN._){var _uO=_uN.a;return (_uO>=0)?(E(_uO)==0)?E(_uJ):E(_oo):E(_uK);}else{var _uP=I_compareInt(_uN.a,0);return (_uP<=0)?(E(_uP)==0)?E(_uJ):E(_uK):E(_oo);}},_uQ=function(_uR,_uS,_uT){while(1){var _uU=E(_uT);if(!_uU._){if(!B(_ux(_uR,_me))){return new T2(0,B(_m1(_uS,B(_uF(_ov,_uR)))),_u7);}else{var _uV=B(_uF(_ov,B(_or(_uR))));return new F(function(){return _u3(B(_m1(_uS,B(_uL(_uV)))),B(_tN(_uV)));});}}else{var _uW=B(_uc(_uR,_uI)),_uX=B(_lS(B(_m1(_uS,_ov)),B(_lD(E(_uU.a)))));_uR=_uW;_uS=_uX;_uT=_uU.b;continue;}}},_uY=function(_uZ,_v0){var _v1=E(_uZ);if(!_v1._){var _v2=_v1.a,_v3=E(_v0);return (_v3._==0)?_v2>=_v3.a:I_compareInt(_v3.a,_v2)<=0;}else{var _v4=_v1.a,_v5=E(_v0);return (_v5._==0)?I_compareInt(_v4,_v5.a)>=0:I_compare(_v4,_v5.a)>=0;}},_v6=function(_v7){var _v8=E(_v7);if(!_v8._){var _v9=_v8.b;return new F(function(){return _u3(B(_m1(B(_mf(new T(function(){return B(_lD(E(_v8.a)));}),new T(function(){return B(_lF(_v9,0));},1),B(_lK(_lO,_v9)))),_uI)),_uI);});}else{var _va=_v8.a,_vb=_v8.c,_vc=E(_v8.b);if(!_vc._){var _vd=E(_vb);if(!_vd._){return new F(function(){return _u3(B(_m1(B(_mw(_ov,_va)),_uI)),_uI);});}else{var _ve=_vd.a;if(!B(_uY(_ve,_me))){var _vf=B(_uF(_ov,B(_or(_ve))));return new F(function(){return _u3(B(_m1(B(_mw(_ov,_va)),B(_uL(_vf)))),B(_tN(_vf)));});}else{return new F(function(){return _u3(B(_m1(B(_m1(B(_mw(_ov,_va)),B(_uF(_ov,_ve)))),_uI)),_uI);});}}}else{var _vg=_vc.a,_vh=E(_vb);if(!_vh._){return new F(function(){return _uQ(_me,B(_mw(_ov,_va)),_vg);});}else{return new F(function(){return _uQ(_vh.a,B(_mw(_ov,_va)),_vg);});}}}},_vi=function(_vj,_vk){var _vl=E(_vj);if(!_vl._){var _vm=_vl.a,_vn=E(_vk);return (_vn._==0)?_vm>_vn.a:I_compareInt(_vn.a,_vm)<0;}else{var _vo=_vl.a,_vp=E(_vk);return (_vp._==0)?I_compareInt(_vo,_vp.a)>0:I_compare(_vo,_vp.a)>0;}},_vq=0,_vr=function(_vs,_vt){return E(_vs)==E(_vt);},_vu=function(_vv){return new F(function(){return _vr(_vq,_vv);});},_vw=new T2(0,E(_me),E(_u7)),_vx=new T1(1,_vw),_vy=new T1(0, -2147483648),_vz=new T1(0,2147483647),_vA=function(_vB,_vC,_vD){var _vE=E(_vD);if(!_vE._){return new T1(1,new T(function(){var _vF=B(_v6(_vE));return new T2(0,E(_vF.a),E(_vF.b));}));}else{var _vG=E(_vE.c);if(!_vG._){return new T1(1,new T(function(){var _vH=B(_v6(_vE));return new T2(0,E(_vH.a),E(_vH.b));}));}else{var _vI=_vG.a;if(!B(_vi(_vI,_vz))){if(!B(_ux(_vI,_vy))){var _vJ=function(_vK){var _vL=_vK+B(_ha(_vI))|0;return (_vL<=(E(_vC)+3|0))?(_vL>=(E(_vB)-3|0))?new T1(1,new T(function(){var _vM=B(_v6(_vE));return new T2(0,E(_vM.a),E(_vM.b));})):E(_vx):__Z;},_vN=B(_rp(_vu,_vE.a));if(!_vN._){var _vO=E(_vE.b);if(!_vO._){return E(_vx);}else{var _vP=B(_4f(_vu,_vO.a));if(!E(_vP.b)._){return E(_vx);}else{return new F(function(){return _vJ( -B(_lF(_vP.a,0)));});}}}else{return new F(function(){return _vJ(B(_lF(_vN,0)));});}}else{return __Z;}}else{return __Z;}}}},_vQ=new T1(0,1),_vR=function(_vS,_vT){var _vU=E(_vS);if(!_vU._){var _vV=_vU.a,_vW=E(_vT);if(!_vW._){var _vX=_vW.a;return (_vV!=_vX)?(_vV>_vX)?2:0:1;}else{var _vY=I_compareInt(_vW.a,_vV);return (_vY<=0)?(_vY>=0)?1:2:0;}}else{var _vZ=_vU.a,_w0=E(_vT);if(!_w0._){var _w1=I_compareInt(_vZ,_w0.a);return (_w1>=0)?(_w1<=0)?1:2:0;}else{var _w2=I_compare(_vZ,_w0.a);return (_w2>=0)?(_w2<=0)?1:2:0;}}},_w3=function(_w4,_w5){var _w6=E(_w4);return (_w6._==0)?_w6.a*Math.pow(2,_w5):I_toNumber(_w6.a)*Math.pow(2,_w5);},_w7=function(_w8,_w9){while(1){var _wa=E(_w8);if(!_wa._){var _wb=E(_wa.a);if(_wb==( -2147483648)){_w8=new T1(1,I_fromInt( -2147483648));continue;}else{var _wc=E(_w9);if(!_wc._){var _wd=_wc.a;return new T2(0,new T1(0,quot(_wb,_wd)),new T1(0,_wb%_wd));}else{_w8=new T1(1,I_fromInt(_wb));_w9=_wc;continue;}}}else{var _we=E(_w9);if(!_we._){_w8=_wa;_w9=new T1(1,I_fromInt(_we.a));continue;}else{var _wf=I_quotRem(_wa.a,_we.a);return new T2(0,new T1(1,_wf.a),new T1(1,_wf.b));}}}},_wg=new T1(0,0),_wh=function(_wi,_wj){while(1){var _wk=E(_wi);if(!_wk._){_wi=new T1(1,I_fromInt(_wk.a));continue;}else{return new T1(1,I_shiftLeft(_wk.a,_wj));}}},_wl=function(_wm,_wn,_wo){if(!B(_to(_wo,_wg))){var _wp=B(_w7(_wn,_wo)),_wq=_wp.a;switch(B(_vR(B(_wh(_wp.b,1)),_wo))){case 0:return new F(function(){return _w3(_wq,_wm);});break;case 1:if(!(B(_ha(_wq))&1)){return new F(function(){return _w3(_wq,_wm);});}else{return new F(function(){return _w3(B(_lS(_wq,_vQ)),_wm);});}break;default:return new F(function(){return _w3(B(_lS(_wq,_vQ)),_wm);});}}else{return E(_tn);}},_wr=function(_ws){var _wt=function(_wu,_wv){while(1){if(!B(_ux(_wu,_ws))){if(!B(_vi(_wu,_ws))){if(!B(_to(_wu,_ws))){return new F(function(){return _4B("GHC\\Integer\\Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_wv);}}else{return _wv-1|0;}}else{var _ww=B(_wh(_wu,1)),_wx=_wv+1|0;_wu=_ww;_wv=_wx;continue;}}};return new F(function(){return _wt(_oo,0);});},_wy=function(_wz){var _wA=E(_wz);if(!_wA._){var _wB=_wA.a>>>0;if(!_wB){return  -1;}else{var _wC=function(_wD,_wE){while(1){if(_wD>=_wB){if(_wD<=_wB){if(_wD!=_wB){return new F(function(){return _4B("GHC\\Integer\\Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_wE);}}else{return _wE-1|0;}}else{var _wF=imul(_wD,2)>>>0,_wG=_wE+1|0;_wD=_wF;_wE=_wG;continue;}}};return new F(function(){return _wC(1,0);});}}else{return new F(function(){return _wr(_wA);});}},_wH=function(_wI){var _wJ=E(_wI);if(!_wJ._){var _wK=_wJ.a>>>0;if(!_wK){return new T2(0, -1,0);}else{var _wL=function(_wM,_wN){while(1){if(_wM>=_wK){if(_wM<=_wK){if(_wM!=_wK){return new F(function(){return _4B("GHC\\Integer\\Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_wN);}}else{return _wN-1|0;}}else{var _wO=imul(_wM,2)>>>0,_wP=_wN+1|0;_wM=_wO;_wN=_wP;continue;}}};return new T2(0,B(_wL(1,0)),(_wK&_wK-1>>>0)>>>0&4294967295);}}else{var _wQ=_wJ.a;return new T2(0,B(_wy(_wJ)),I_compareInt(I_and(_wQ,I_sub(_wQ,I_fromInt(1))),0));}},_wR=function(_wS,_wT){while(1){var _wU=E(_wS);if(!_wU._){var _wV=_wU.a,_wW=E(_wT);if(!_wW._){return new T1(0,(_wV>>>0&_wW.a>>>0)>>>0&4294967295);}else{_wS=new T1(1,I_fromInt(_wV));_wT=_wW;continue;}}else{var _wX=E(_wT);if(!_wX._){_wS=_wU;_wT=new T1(1,I_fromInt(_wX.a));continue;}else{return new T1(1,I_and(_wU.a,_wX.a));}}}},_wY=new T1(0,2),_wZ=function(_x0,_x1){var _x2=E(_x0);if(!_x2._){var _x3=(_x2.a>>>0&(2<<_x1>>>0)-1>>>0)>>>0,_x4=1<<_x1>>>0;return (_x4<=_x3)?(_x4>=_x3)?1:2:0;}else{var _x5=B(_wR(_x2,B(_uc(B(_wh(_wY,_x1)),_oo)))),_x6=B(_wh(_oo,_x1));return (!B(_vi(_x6,_x5)))?(!B(_ux(_x6,_x5)))?1:2:0;}},_x7=function(_x8,_x9){while(1){var _xa=E(_x8);if(!_xa._){_x8=new T1(1,I_fromInt(_xa.a));continue;}else{return new T1(1,I_shiftRight(_xa.a,_x9));}}},_xb=function(_xc,_xd,_xe,_xf){var _xg=B(_wH(_xf)),_xh=_xg.a;if(!E(_xg.b)){var _xi=B(_wy(_xe));if(_xi<((_xh+_xc|0)-1|0)){var _xj=_xh+(_xc-_xd|0)|0;if(_xj>0){if(_xj>_xi){if(_xj<=(_xi+1|0)){if(!E(B(_wH(_xe)).b)){return 0;}else{return new F(function(){return _w3(_vQ,_xc-_xd|0);});}}else{return 0;}}else{var _xk=B(_x7(_xe,_xj));switch(B(_wZ(_xe,_xj-1|0))){case 0:return new F(function(){return _w3(_xk,_xc-_xd|0);});break;case 1:if(!(B(_ha(_xk))&1)){return new F(function(){return _w3(_xk,_xc-_xd|0);});}else{return new F(function(){return _w3(B(_lS(_xk,_vQ)),_xc-_xd|0);});}break;default:return new F(function(){return _w3(B(_lS(_xk,_vQ)),_xc-_xd|0);});}}}else{return new F(function(){return _w3(_xe,(_xc-_xd|0)-_xj|0);});}}else{if(_xi>=_xd){var _xl=B(_x7(_xe,(_xi+1|0)-_xd|0));switch(B(_wZ(_xe,_xi-_xd|0))){case 0:return new F(function(){return _w3(_xl,((_xi-_xh|0)+1|0)-_xd|0);});break;case 2:return new F(function(){return _w3(B(_lS(_xl,_vQ)),((_xi-_xh|0)+1|0)-_xd|0);});break;default:if(!(B(_ha(_xl))&1)){return new F(function(){return _w3(_xl,((_xi-_xh|0)+1|0)-_xd|0);});}else{return new F(function(){return _w3(B(_lS(_xl,_vQ)),((_xi-_xh|0)+1|0)-_xd|0);});}}}else{return new F(function(){return _w3(_xe, -_xh);});}}}else{var _xm=B(_wy(_xe))-_xh|0,_xn=function(_xo){var _xp=function(_xq,_xr){if(!B(_hd(B(_wh(_xr,_xd)),_xq))){return new F(function(){return _wl(_xo-_xd|0,_xq,_xr);});}else{return new F(function(){return _wl((_xo-_xd|0)+1|0,_xq,B(_wh(_xr,1)));});}};if(_xo>=_xd){if(_xo!=_xd){return new F(function(){return _xp(_xe,new T(function(){return B(_wh(_xf,_xo-_xd|0));}));});}else{return new F(function(){return _xp(_xe,_xf);});}}else{return new F(function(){return _xp(new T(function(){return B(_wh(_xe,_xd-_xo|0));}),_xf);});}};if(_xc>_xm){return new F(function(){return _xn(_xc);});}else{return new F(function(){return _xn(_xm);});}}},_xs=new T(function(){return 0/0;}),_xt=new T(function(){return  -1/0;}),_xu=new T(function(){return 1/0;}),_xv=0,_xw=function(_xx,_xy){if(!B(_to(_xy,_wg))){if(!B(_to(_xx,_wg))){if(!B(_ux(_xx,_wg))){return new F(function(){return _xb( -1021,53,_xx,_xy);});}else{return  -B(_xb( -1021,53,B(_or(_xx)),_xy));}}else{return E(_xv);}}else{return (!B(_to(_xx,_wg)))?(!B(_ux(_xx,_wg)))?E(_xu):E(_xt):E(_xs);}},_xz=function(_xA){var _xB=E(_xA);switch(_xB._){case 3:var _xC=_xB.a;return (!B(_ei(_xC,_sF)))?(!B(_ei(_xC,_sE)))?E(_qS):E(_sL):E(_sH);case 5:var _xD=B(_vA(_sP,_sO,_xB.a));if(!_xD._){return E(_sH);}else{var _xE=new T(function(){var _xF=E(_xD.a);return B(_xw(_xF.a,_xF.b));});return function(_xG,_xH){return new F(function(){return A1(_xH,_xE);});};}break;default:return E(_qS);}},_xI=new T(function(){return B(A3(_sj,_xz,_pX,_r2));}),_xJ=new T(function(){return B(err(_rL));}),_xK=new T(function(){return B(err(_rM));}),_xL=function(_xM){var _xN=E(_xM);if(!_xN._){return __Z;}else{var _xO=E(_xN.b);if(!_xO._){return __Z;}else{var _xP=E(_xO.b);if(!_xP._){return E(_si);}else{var _xQ=E(_xP.b);return (_xQ._==0)?E(_si):new T2(1,new T4(0,new T(function(){var _xR=B(_rN(B(_du(_r7,_xN.a))));if(!_xR._){return E(_xK);}else{if(!E(_xR.b)._){return E(_xR.a);}else{return E(_xJ);}}}),new T(function(){var _xS=B(_rN(B(_du(_r7,_xO.a))));if(!_xS._){return E(_xK);}else{if(!E(_xS.b)._){return E(_xS.a);}else{return E(_xJ);}}}),new T(function(){var _xT=B(_rN(B(_du(_xI,_xP.a))));if(!_xT._){return E(_sf);}else{if(!E(_xT.b)._){return E(_xT.a);}else{return E(_se);}}}),new T(function(){var _xU=B(_rN(B(_du(_xI,_xQ.a))));if(!_xU._){return E(_sf);}else{if(!E(_xU.b)._){return E(_xU.a);}else{return E(_se);}}})),new T(function(){return B(_xL(_xQ.b));}));}}}},_xV=new T(function(){return B(_xL(_sd));}),_xW=function(_xX,_xY){var _xZ=E(_xX);if(!_xZ){return __Z;}else{var _y0=new T(function(){var _y1=new T(function(){var _y2=E(_xY);return {_:0,a:new T(function(){return E(_y2.a)+1|0;}),b:_y2.b,c:new T(function(){return E(_y2.c)+2+20;}),d:_y2.d,e:_y2.e,f:_y2.f,g:_y2.g,h:_y2.h};});return B(_xW(_xZ-1|0,_y1));});return new T2(1,_xY,_y0);}},_y3=function(_y4,_y5,_y6,_y7,_y8,_y9,_ya,_yb,_yc,_yd){var _ye=E(_y5);return (_ye==0)?__Z:new T2(1,new T(function(){return B(_xW(E(_y4),{_:0,a:_y6,b:_y7,c:_y8,d:_y9,e:_ya,f:_yb,g:_yc,h:_yd}));}),new T(function(){return B(_y3(_y4,_ye-1|0,_y6,_y7+1|0,_y8,_y9+2+20,_ya,_yb,_yc,_yd));}));},_yf=function(_yg,_yh){return E(_yg)+E(_yh);},_yi=function(_yj,_yk){var _yl=E(_yk);if(!_yl._){return __Z;}else{var _ym=_yl.a,_yn=new T(function(){var _yo=new T(function(){return E(E(_ym).c);}),_yp=new T(function(){return E(E(_ym).d);}),_yq=function(_yr,_ys){while(1){var _yt=B((function(_yu,_yv){var _yw=E(_yu);if(!_yw._){return E(_yv);}else{var _yx=new T(function(){var _yy=E(_yw.a),_yz=E(_ym),_yA=E(_yz.a);if(_yA!=E(_yy.a)){return E(_yv);}else{var _yB=E(_yz.b);if(_yB!=E(_yy.b)){return E(_yv);}else{return {_:0,a:_yA,b:_yB,c:new T(function(){return B(_yf(_yo,_yy.c));}),d:new T(function(){return B(_yf(_yp,_yy.d));}),e:_yz.e,f:_yz.f,g:_yz.g,h:_yz.h};}}},1);_yr=_yw.b;_ys=_yx;return __continue;}})(_yr,_ys));if(_yt!=__continue){return _yt;}}};return B(_yq(_yj,_ym));});return new T2(1,_yn,new T(function(){return B(_yi(_yj,_yl.b));}));}},_yC=function(_yD,_yE){var _yF=E(_yE);return (_yF._==0)?__Z:new T2(1,new T(function(){return B(_yi(_yD,_yF.a));}),new T(function(){return B(_yC(_yD,_yF.b));}));},_yG=new T(function(){return B(_yC(_xV,B(_y3(_rU,E(_s7),_sb,0,_d0,0,_d0,_d0,_d0,_d0))));}),_yH=new T(function(){return B(_9z(_yG,_sa));}),_yI=new T(function(){return B(_7U(_yH));}),_yJ=new T(function(){return B(_6W(_yI));}),_yK=new T(function(){return B(_9r(_yG));}),_yL=function(_yM,_yN,_yO,_yP,_yQ,_yR){var _yS=E(_yM);if(!_yS){return __Z;}else{var _yT=new T(function(){return B(_yL(_yS-1|0,_yN,new T(function(){return E(_yO)+20+2;}),_yP,new T(function(){return E(_yO)+40+2;}),_yR));});return new T2(1,new T5(0,_yN,_yO,_yP,_yQ,_yR),_yT);}},_yU=function(_yV,_yW,_yX,_yY,_yZ,_z0,_z1){var _z2=E(_yW);if(!_z2){return __Z;}else{var _z3=E(_yV);return (_z3==0)?__Z:new T2(1,new T(function(){return B(_yL(_z2,_yX,_yY,_yZ,_z0,_z1));}),new T(function(){return B(_yU(_z3-1|0,_z2,_yX+20+2,_yY,_yX+20+2,_z0,_z1));}));}},_z4=function(_z5,_z6,_z7,_z8,_z9,_za){var _zb=E(_z6);if(!_zb){return __Z;}else{var _zc=E(_z5);return (_zc==0)?__Z:new T2(1,new T(function(){return B(_yL(_zb,_z7,_z8,_d0,_z9,_za));}),new T(function(){return B(_yU(_zc-1|0,_zb,_z7+20+2,_z8,_z7+20+2,_z9,_za));}));}},_zd=new T(function(){return B(_z4(_rU,E(_s7)-1|0,0,_s9,_cZ,_cY));}),_ze=new T(function(){return B(_9z(_yK,_zd));}),_zf=new T(function(){return B(_8k(_ze));}),_zg=new T(function(){return B(_6W(_zf));}),_zh=new T(function(){return B(unCStr("Pattern match failure in do expression at jsEther.hs:235:3-10"));}),_zi=new T6(0,_2a,_2b,_u,_zh,_2a,_2a),_zj=new T(function(){return B(_1D(_zi));}),_zk=new T(function(){return B(unCStr("eCanvas"));}),_zl=function(_){var _zm=B(A3(_cS,_2s,_zk,_)),_zn=E(_zm);if(!_zn._){return new F(function(){return die(_zj);});}else{var _zo=E(_zn.a);return new F(function(){return _9E(_zo.a,_zo.b,_yG,_yJ,_zg,_);});}},_zp=function(_){return new F(function(){return _zl(_);});};
var hasteMain = function() {B(A(_zp, [0]));};window.onload = hasteMain;