"use strict";
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined') window = global;

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
  var x = new Long(2904464383, 3929545892, true);
  var y = new Long(3027541338, 3270546716, true);
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
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
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
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': new Int16Array(buffer)
        , 'i32': new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': new Uint16Array(buffer)
        , 'w32': new Uint32Array(buffer)
        , 'f32': new Float32Array(buffer)
        , 'f64': new Float64Array(buffer)
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

var _0=0,_1=0,_2=1,_3=2,_4="deltaZ",_5="deltaY",_6="deltaX",_7=function(_8,_9){var _a=E(_8);return (_a._==0)?E(_9):new T2(1,_a.a,new T(function(){return B(_7(_a.b,_9));}));},_b=function(_c,_d){var _e=jsShowI(_c);return new F(function(){return _7(fromJSStr(_e),_d);});},_f=41,_g=40,_h=function(_i,_j,_k){if(_j>=0){return new F(function(){return _b(_j,_k);});}else{if(_i<=6){return new F(function(){return _b(_j,_k);});}else{return new T2(1,_g,new T(function(){var _l=jsShowI(_j);return B(_7(fromJSStr(_l),new T2(1,_f,_k)));}));}}},_m=new T(function(){return B(unCStr(")"));}),_n=new T(function(){return B(_h(0,2,_m));}),_o=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_n));}),_p=function(_q){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_h(0,_q,_o));}))));});},_r=function(_s,_){return new T(function(){var _t=Number(E(_s)),_u=jsTrunc(_t);if(_u<0){return B(_p(_u));}else{if(_u>2){return B(_p(_u));}else{return _u;}}});},_v=0,_w=new T3(0,_v,_v,_v),_x="button",_y=new T(function(){return eval("jsGetMouseCoords");}),_z=__Z,_A=function(_B,_){var _C=E(_B);if(!_C._){return _z;}else{var _D=B(_A(_C.b,_));return new T2(1,new T(function(){var _E=Number(E(_C.a));return jsTrunc(_E);}),_D);}},_F=function(_G,_){var _H=__arr2lst(0,_G);return new F(function(){return _A(_H,_);});},_I=function(_J,_){return new F(function(){return _F(E(_J),_);});},_K=function(_L,_){return new T(function(){var _M=Number(E(_L));return jsTrunc(_M);});},_N=new T2(0,_K,_I),_O=function(_P,_){var _Q=E(_P);if(!_Q._){return _z;}else{var _R=B(_O(_Q.b,_));return new T2(1,_Q.a,_R);}},_S=new T(function(){return B(unCStr("base"));}),_T=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_U=new T(function(){return B(unCStr("IOException"));}),_V=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_S,_T,_U),_W=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_V,_z,_z),_X=function(_Y){return E(_W);},_Z=function(_10){return E(E(_10).a);},_11=function(_12,_13,_14){var _15=B(A1(_12,_)),_16=B(A1(_13,_)),_17=hs_eqWord64(_15.a,_16.a);if(!_17){return __Z;}else{var _18=hs_eqWord64(_15.b,_16.b);return (!_18)?__Z:new T1(1,_14);}},_19=function(_1a){var _1b=E(_1a);return new F(function(){return _11(B(_Z(_1b.a)),_X,_1b.b);});},_1c=new T(function(){return B(unCStr(": "));}),_1d=new T(function(){return B(unCStr(")"));}),_1e=new T(function(){return B(unCStr(" ("));}),_1f=new T(function(){return B(unCStr("interrupted"));}),_1g=new T(function(){return B(unCStr("system error"));}),_1h=new T(function(){return B(unCStr("unsatisified constraints"));}),_1i=new T(function(){return B(unCStr("user error"));}),_1j=new T(function(){return B(unCStr("permission denied"));}),_1k=new T(function(){return B(unCStr("illegal operation"));}),_1l=new T(function(){return B(unCStr("end of file"));}),_1m=new T(function(){return B(unCStr("resource exhausted"));}),_1n=new T(function(){return B(unCStr("resource busy"));}),_1o=new T(function(){return B(unCStr("does not exist"));}),_1p=new T(function(){return B(unCStr("already exists"));}),_1q=new T(function(){return B(unCStr("resource vanished"));}),_1r=new T(function(){return B(unCStr("timeout"));}),_1s=new T(function(){return B(unCStr("unsupported operation"));}),_1t=new T(function(){return B(unCStr("hardware fault"));}),_1u=new T(function(){return B(unCStr("inappropriate type"));}),_1v=new T(function(){return B(unCStr("invalid argument"));}),_1w=new T(function(){return B(unCStr("failed"));}),_1x=new T(function(){return B(unCStr("protocol error"));}),_1y=function(_1z,_1A){switch(E(_1z)){case 0:return new F(function(){return _7(_1p,_1A);});break;case 1:return new F(function(){return _7(_1o,_1A);});break;case 2:return new F(function(){return _7(_1n,_1A);});break;case 3:return new F(function(){return _7(_1m,_1A);});break;case 4:return new F(function(){return _7(_1l,_1A);});break;case 5:return new F(function(){return _7(_1k,_1A);});break;case 6:return new F(function(){return _7(_1j,_1A);});break;case 7:return new F(function(){return _7(_1i,_1A);});break;case 8:return new F(function(){return _7(_1h,_1A);});break;case 9:return new F(function(){return _7(_1g,_1A);});break;case 10:return new F(function(){return _7(_1x,_1A);});break;case 11:return new F(function(){return _7(_1w,_1A);});break;case 12:return new F(function(){return _7(_1v,_1A);});break;case 13:return new F(function(){return _7(_1u,_1A);});break;case 14:return new F(function(){return _7(_1t,_1A);});break;case 15:return new F(function(){return _7(_1s,_1A);});break;case 16:return new F(function(){return _7(_1r,_1A);});break;case 17:return new F(function(){return _7(_1q,_1A);});break;default:return new F(function(){return _7(_1f,_1A);});}},_1B=new T(function(){return B(unCStr("}"));}),_1C=new T(function(){return B(unCStr("{handle: "));}),_1D=function(_1E,_1F,_1G,_1H,_1I,_1J){var _1K=new T(function(){var _1L=new T(function(){var _1M=new T(function(){var _1N=E(_1H);if(!_1N._){return E(_1J);}else{var _1O=new T(function(){return B(_7(_1N,new T(function(){return B(_7(_1d,_1J));},1)));},1);return B(_7(_1e,_1O));}},1);return B(_1y(_1F,_1M));}),_1P=E(_1G);if(!_1P._){return E(_1L);}else{return B(_7(_1P,new T(function(){return B(_7(_1c,_1L));},1)));}}),_1Q=E(_1I);if(!_1Q._){var _1R=E(_1E);if(!_1R._){return E(_1K);}else{var _1S=E(_1R.a);if(!_1S._){var _1T=new T(function(){var _1U=new T(function(){return B(_7(_1B,new T(function(){return B(_7(_1c,_1K));},1)));},1);return B(_7(_1S.a,_1U));},1);return new F(function(){return _7(_1C,_1T);});}else{var _1V=new T(function(){var _1W=new T(function(){return B(_7(_1B,new T(function(){return B(_7(_1c,_1K));},1)));},1);return B(_7(_1S.a,_1W));},1);return new F(function(){return _7(_1C,_1V);});}}}else{return new F(function(){return _7(_1Q.a,new T(function(){return B(_7(_1c,_1K));},1));});}},_1X=function(_1Y){var _1Z=E(_1Y);return new F(function(){return _1D(_1Z.a,_1Z.b,_1Z.c,_1Z.d,_1Z.f,_z);});},_20=function(_21,_22,_23){var _24=E(_22);return new F(function(){return _1D(_24.a,_24.b,_24.c,_24.d,_24.f,_23);});},_25=function(_26,_27){var _28=E(_26);return new F(function(){return _1D(_28.a,_28.b,_28.c,_28.d,_28.f,_27);});},_29=44,_2a=93,_2b=91,_2c=function(_2d,_2e,_2f){var _2g=E(_2e);if(!_2g._){return new F(function(){return unAppCStr("[]",_2f);});}else{var _2h=new T(function(){var _2i=new T(function(){var _2j=function(_2k){var _2l=E(_2k);if(!_2l._){return E(new T2(1,_2a,_2f));}else{var _2m=new T(function(){return B(A2(_2d,_2l.a,new T(function(){return B(_2j(_2l.b));})));});return new T2(1,_29,_2m);}};return B(_2j(_2g.b));});return B(A2(_2d,_2g.a,_2i));});return new T2(1,_2b,_2h);}},_2n=function(_2o,_2p){return new F(function(){return _2c(_25,_2o,_2p);});},_2q=new T3(0,_20,_1X,_2n),_2r=new T(function(){return new T5(0,_X,_2q,_2s,_19,_1X);}),_2s=function(_2t){return new T2(0,_2r,_2t);},_2u=__Z,_2v=7,_2w=new T(function(){return B(unCStr("Pattern match failure in do expression at src\\Haste\\Prim\\Any.hs:272:5-9"));}),_2x=new T6(0,_2u,_2v,_z,_2w,_2u,_2u),_2y=new T(function(){return B(_2s(_2x));}),_2z=function(_){return new F(function(){return die(_2y);});},_2A=function(_2B){return E(E(_2B).a);},_2C=function(_2D,_2E,_2F,_){var _2G=__arr2lst(0,_2F),_2H=B(_O(_2G,_)),_2I=E(_2H);if(!_2I._){return new F(function(){return _2z(_);});}else{var _2J=E(_2I.b);if(!_2J._){return new F(function(){return _2z(_);});}else{if(!E(_2J.b)._){var _2K=B(A3(_2A,_2D,_2I.a,_)),_2L=B(A3(_2A,_2E,_2J.a,_));return new T2(0,_2K,_2L);}else{return new F(function(){return _2z(_);});}}}},_2M=function(_){return new F(function(){return __jsNull();});},_2N=function(_2O){var _2P=B(A1(_2O,_));return E(_2P);},_2Q=new T(function(){return B(_2N(_2M));}),_2R=new T(function(){return E(_2Q);}),_2S=function(_2T,_2U,_){if(E(_2T)==7){var _2V=__app1(E(_y),_2U),_2W=B(_2C(_N,_N,_2V,_)),_2X=__get(_2U,E(_6)),_2Y=__get(_2U,E(_5)),_2Z=__get(_2U,E(_4));return new T(function(){return new T3(0,E(_2W),E(_2u),E(new T3(0,_2X,_2Y,_2Z)));});}else{var _30=__app1(E(_y),_2U),_31=B(_2C(_N,_N,_30,_)),_32=__get(_2U,E(_x)),_33=__eq(_32,E(_2R));if(!E(_33)){var _34=B(_r(_32,_));return new T(function(){return new T3(0,E(_31),E(new T1(1,_34)),E(_w));});}else{return new T(function(){return new T3(0,E(_31),E(_2u),E(_w));});}}},_35=function(_36,_37,_){return new F(function(){return _2S(_36,E(_37),_);});},_38="mouseout",_39="mouseover",_3a="mousemove",_3b="mouseup",_3c="mousedown",_3d="dblclick",_3e="click",_3f="wheel",_3g=function(_3h){switch(E(_3h)){case 0:return E(_3e);case 1:return E(_3d);case 2:return E(_3c);case 3:return E(_3b);case 4:return E(_3a);case 5:return E(_39);case 6:return E(_38);default:return E(_3f);}},_3i=new T2(0,_3g,_35),_3j=function(_3k,_){return new T1(1,_3k);},_3l=function(_3m){return E(_3m);},_3n=new T2(0,_3l,_3j),_3o=function(_3p,_3q,_){var _3r=B(A1(_3p,_)),_3s=B(A1(_3q,_));return _3r;},_3t=function(_3u,_3v,_){var _3w=B(A1(_3u,_)),_3x=B(A1(_3v,_));return new T(function(){return B(A1(_3w,_3x));});},_3y=function(_3z,_3A,_){var _3B=B(A1(_3A,_));return _3z;},_3C=function(_3D,_3E,_){var _3F=B(A1(_3E,_));return new T(function(){return B(A1(_3D,_3F));});},_3G=new T2(0,_3C,_3y),_3H=function(_3I,_){return _3I;},_3J=function(_3K,_3L,_){var _3M=B(A1(_3K,_));return new F(function(){return A1(_3L,_);});},_3N=new T5(0,_3G,_3H,_3t,_3J,_3o),_3O=new T(function(){return E(_2r);}),_3P=function(_3Q){return E(E(_3Q).c);},_3R=function(_3S){return new T6(0,_2u,_2v,_z,_3S,_2u,_2u);},_3T=function(_3U,_){var _3V=new T(function(){return B(A2(_3P,_3O,new T(function(){return B(A1(_3R,_3U));})));});return new F(function(){return die(_3V);});},_3W=function(_3X,_){return new F(function(){return _3T(_3X,_);});},_3Y=function(_3Z){return new F(function(){return A1(_3W,_3Z);});},_40=function(_41,_42,_){var _43=B(A1(_41,_));return new F(function(){return A2(_42,_43,_);});},_44=new T5(0,_3N,_40,_3J,_3H,_3Y),_45=new T2(0,_44,_3l),_46=new T2(0,_45,_3H),_47=function(_48,_49,_4a,_4b,_4c){return new T5(0,_48,_49,_4a,_4b,_4c);},_4d=function(_4e,_4f){if(_4e<=_4f){var _4g=function(_4h){return new T2(1,_4h,new T(function(){if(_4h!=_4f){return B(_4g(_4h+1|0));}else{return __Z;}}));};return new F(function(){return _4g(_4e);});}else{return __Z;}},_4i=new T(function(){return B(_4d(0,2147483647));}),_4j=function(_4k,_4l){var _4m=E(_4l);return (_4m._==0)?__Z:new T2(1,new T(function(){return B(A1(_4k,_4m.a));}),new T(function(){return B(_4j(_4k,_4m.b));}));},_4n=function(_4o,_4p,_4q,_4r){switch(E(_4r)){case 0:return E(_4o);case 1:return E(_4p);default:return E(_4q);}},_4s=function(_4t,_4u,_4v,_4w){var _4x=new T(function(){var _4y=function(_4z){var _4A=function(_4B){return new T3(0,new T(function(){return B(_4n(_4u,_4B,_4z,_4t));}),new T(function(){return B(_4n(_4u,_4B,_4z,_4v));}),new T(function(){return B(_4n(_4u,_4B,_4z,_4w));}));};return new F(function(){return _4j(_4A,_4i);});};return B(_4j(_4y,_4i));});return function(_4C){return new F(function(){return _47(new T2(0,_4t,_4u),_4v,_4w,_4x,_4C);});};},_4D=function(_4E,_4F,_4G,_4H){while(1){var _4I=E(_4H);if(!_4I._){var _4J=_4I.d,_4K=_4I.e,_4L=E(_4I.b),_4M=E(_4L.a);if(_4E>=_4M){if(_4E!=_4M){_4H=_4K;continue;}else{var _4N=E(_4L.b);if(_4F>=_4N){if(_4F!=_4N){_4H=_4K;continue;}else{var _4O=E(_4L.c);if(_4G>=_4O){if(_4G!=_4O){_4H=_4K;continue;}else{return new T1(1,_4I.c);}}else{_4H=_4J;continue;}}}else{_4H=_4J;continue;}}}else{_4H=_4J;continue;}}else{return __Z;}}},_4P=function(_4Q,_4R,_4S,_4T){while(1){var _4U=E(_4T);if(!_4U._){var _4V=_4U.d,_4W=_4U.e,_4X=E(_4U.b),_4Y=E(_4X.a);if(_4Q>=_4Y){if(_4Q!=_4Y){_4T=_4W;continue;}else{var _4Z=E(_4X.b);if(_4R>=_4Z){if(_4R!=_4Z){_4T=_4W;continue;}else{var _50=E(_4S),_51=E(_4X.c);if(_50>=_51){if(_50!=_51){return new F(function(){return _4D(_4Q,_4R,_50,_4W);});}else{return new T1(1,_4U.c);}}else{return new F(function(){return _4D(_4Q,_4R,_50,_4V);});}}}else{_4T=_4V;continue;}}}else{_4T=_4V;continue;}}else{return __Z;}}},_52=function(_53,_54,_55,_56){while(1){var _57=E(_56);if(!_57._){var _58=_57.d,_59=_57.e,_5a=E(_57.b),_5b=E(_5a.a);if(_53>=_5b){if(_53!=_5b){_56=_59;continue;}else{var _5c=E(_54),_5d=E(_5a.b);if(_5c>=_5d){if(_5c!=_5d){return new F(function(){return _4P(_53,_5c,_55,_59);});}else{var _5e=E(_55),_5f=E(_5a.c);if(_5e>=_5f){if(_5e!=_5f){return new F(function(){return _4D(_53,_5c,_5e,_59);});}else{return new T1(1,_57.c);}}else{return new F(function(){return _4D(_53,_5c,_5e,_58);});}}}else{return new F(function(){return _4P(_53,_5c,_55,_58);});}}}else{_56=_58;continue;}}else{return __Z;}}},_5g=function(_5h,_5i,_5j,_5k){var _5l=E(_5k);if(!_5l._){var _5m=_5l.d,_5n=_5l.e,_5o=E(_5l.b),_5p=E(_5h),_5q=E(_5o.a);if(_5p>=_5q){if(_5p!=_5q){return new F(function(){return _52(_5p,_5i,_5j,_5n);});}else{var _5r=E(_5i),_5s=E(_5o.b);if(_5r>=_5s){if(_5r!=_5s){return new F(function(){return _4P(_5p,_5r,_5j,_5n);});}else{var _5t=E(_5j),_5u=E(_5o.c);if(_5t>=_5u){if(_5t!=_5u){return new F(function(){return _4D(_5p,_5r,_5t,_5n);});}else{return new T1(1,_5l.c);}}else{return new F(function(){return _4D(_5p,_5r,_5t,_5m);});}}}else{return new F(function(){return _4P(_5p,_5r,_5j,_5m);});}}}else{return new F(function(){return _52(_5p,_5i,_5j,_5m);});}}else{return __Z;}},_5v=function(_5w){return E(E(_5w).d);},_5x=function(_5y){return E(E(_5y).b);},_5z=function(_5A){return E(E(_5A).a);},_5B=function(_5C,_5D){return new T4(0,new T(function(){return B(_5z(_5D));}),new T(function(){return B(_5x(_5D));}),new T(function(){var _5E=E(_5D),_5F=_5E.b,_5G=E(_5C),_5H=B(_5g(_5G.a,_5G.b,_5G.c,_5E.d));if(!_5H._){return __Z;}else{if(!E(E(_5H.a).a)){if(!E(_5F)){return new T1(1,_5G);}else{return __Z;}}else{if(!E(_5F)){return __Z;}else{return new T1(1,_5G);}}}}),new T(function(){return B(_5v(_5D));}));},_5I=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_5J=new T(function(){return B(err(_5I));}),_5K=function(_){return _0;},_5L=function(_5M,_5N){return E(_5M)==E(_5N);},_5O=function(_5P,_5Q){return E(_5P)!=E(_5Q);},_5R=new T2(0,_5L,_5O),_5S=function(_5T,_5U){var _5V=E(_5T),_5W=E(_5U);return (_5V>_5W)?E(_5V):E(_5W);},_5X=function(_5Y,_5Z){var _60=E(_5Y),_61=E(_5Z);return (_60>_61)?E(_61):E(_60);},_62=function(_63,_64){return (_63>=_64)?(_63!=_64)?2:1:0;},_65=function(_66,_67){return new F(function(){return _62(E(_66),E(_67));});},_68=function(_69,_6a){return E(_69)>=E(_6a);},_6b=function(_6c,_6d){return E(_6c)>E(_6d);},_6e=function(_6f,_6g){return E(_6f)<=E(_6g);},_6h=function(_6i,_6j){return E(_6i)<E(_6j);},_6k={_:0,a:_5R,b:_65,c:_6h,d:_6e,e:_6b,f:_68,g:_5S,h:_5X},_6l=function(_6m){return E(E(_6m).a);},_6n=function(_6o){return E(E(_6o).a);},_6p=function(_6q){return E(E(_6q).a);},_6r=new T(function(){return B(unCStr("!!: negative index"));}),_6s=new T(function(){return B(unCStr("Prelude."));}),_6t=new T(function(){return B(_7(_6s,_6r));}),_6u=new T(function(){return B(err(_6t));}),_6v=new T(function(){return B(unCStr("!!: index too large"));}),_6w=new T(function(){return B(_7(_6s,_6v));}),_6x=new T(function(){return B(err(_6w));}),_6y=function(_6z,_6A){while(1){var _6B=E(_6z);if(!_6B._){return E(_6x);}else{var _6C=E(_6A);if(!_6C){return E(_6B.a);}else{_6z=_6B.b;_6A=_6C-1|0;continue;}}}},_6D=function(_6E,_6F){if(_6F>=0){return new F(function(){return _6y(_6E,_6F);});}else{return E(_6u);}},_6G=function(_6H,_6I){while(1){var _6J=E(_6H);if(!_6J._){return E(_6I);}else{var _6K=_6I+1|0;_6H=_6J.b;_6I=_6K;continue;}}},_6L=109,_6M=100,_6N=99,_6O=108,_6P=120,_6Q=118,_6R=105,_6S=function(_6T){if(_6T<1000){if(_6T<900){if(_6T<500){if(_6T<400){if(_6T<100){if(_6T<90){if(_6T<50){if(_6T<40){if(_6T<10){if(_6T<9){if(_6T<5){if(_6T<4){return (_6T<1)?__Z:new T2(1,_6R,new T(function(){return B(_6S(_6T-1|0));}));}else{return new F(function(){return unAppCStr("iv",new T(function(){return B(_6S(_6T-4|0));}));});}}else{return new T2(1,_6Q,new T(function(){return B(_6S(_6T-5|0));}));}}else{return new F(function(){return unAppCStr("ix",new T(function(){return B(_6S(_6T-9|0));}));});}}else{return new T2(1,_6P,new T(function(){return B(_6S(_6T-10|0));}));}}else{return new F(function(){return unAppCStr("xl",new T(function(){return B(_6S(_6T-40|0));}));});}}else{return new T2(1,_6O,new T(function(){return B(_6S(_6T-50|0));}));}}else{return new F(function(){return unAppCStr("xc",new T(function(){return B(_6S(_6T-90|0));}));});}}else{return new T2(1,_6N,new T(function(){return B(_6S(_6T-100|0));}));}}else{return new F(function(){return unAppCStr("cd",new T(function(){return B(_6S(_6T-400|0));}));});}}else{return new T2(1,_6M,new T(function(){return B(_6S(_6T-500|0));}));}}else{return new F(function(){return unAppCStr("cm",new T(function(){return B(_6S(_6T-900|0));}));});}}else{return new T2(1,_6L,new T(function(){return B(_6S(_6T-1000|0));}));}},_6U=new T(function(){return B(unCStr("+"));}),_6V=new T(function(){return B(unCStr("+ - "));}),_6W=new T(function(){return B(_7(_6V,_6U));}),_6X=function(_6Y){var _6Z=E(_6Y);if(_6Z==1){return E(_6W);}else{return new F(function(){return _7(_6V,new T(function(){return B(_6X(_6Z-1|0));},1));});}},_70=function(_71,_72){return new T2(1,_71,_72);},_73=function(_74){return E(E(_74).c);},_75=function(_76){return E(E(_76).c);},_77=function(_78){return E(E(_78).b);},_79=function(_7a){return new T1(2,_7a);},_7b=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_7c=35,_7d=87,_7e=new T(function(){return B(unCStr("   "));}),_7f=42,_7g=32,_7h=75,_7i=81,_7j=78,_7k=82,_7l=80,_7m=66,_7n=function(_7o){var _7p=E(_7o);if(!_7p._){return E(_7e);}else{var _7q=E(_7p.a);return new T2(1,new T(function(){if(!E(_7q.a)){return E(_7d);}else{return E(_7m);}}),new T2(1,new T(function(){switch(E(_7q.b)._){case 0:return E(_7l);break;case 1:return E(_7k);break;case 2:return E(_7j);break;case 3:return E(_7m);break;case 4:return E(_7i);break;default:return E(_7h);}}),new T2(1,new T(function(){if(!E(_7q.d)._){return E(_7g);}else{if(!E(_7q.c)){return E(_7f);}else{return E(_7c);}}}),_z)));}},_7r=function(_7s){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_h(9,_7s,_z));}))));});},_7t=function(_7u){return E(E(_7u).a);},_7v=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_7w=function(_7x){return E(E(_7x).b);},_7y=new T(function(){return B(unCStr("selected"));}),_7z=3,_7A=function(_7B){return E(E(_7B).g);},_7C=new T(function(){return B(unCStr(": empty list"));}),_7D=function(_7E){return new F(function(){return err(B(_7(_6s,new T(function(){return B(_7(_7E,_7C));},1))));});},_7F=new T(function(){return B(unCStr("maximum"));}),_7G=new T(function(){return B(_7D(_7F));}),_7H=function(_7I,_7J){var _7K=E(_7J);if(!_7K._){return E(_7G);}else{var _7L=new T(function(){return B(_7A(_7I));}),_7M=function(_7N,_7O){while(1){var _7P=E(_7N);if(!_7P._){return E(_7O);}else{var _7Q=B(A2(_7L,E(_7O),_7P.a));_7N=_7P.b;_7O=_7Q;continue;}}};return new F(function(){return _7M(_7K.b,_7K.a);});}},_7R=new T(function(){return B(_7H(_6k,_z));}),_7S=8,_7T=new T(function(){return B(unCStr("span"));}),_7U=new T(function(){return toJSStr(E(_7T));}),_7V=new T(function(){return B(unCStr("|"));}),_7W=new T(function(){return toJSStr(E(_7V));}),_7X=new T(function(){return B(unCStr("id"));}),_7Y=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_7Z=function(_80,_81){var _82=function(_){return new F(function(){return __app1(E(_7Y),E(_81));});};return new F(function(){return A2(_7w,_80,_82);});},_83=new T(function(){return B(unCStr("br"));}),_84=new T(function(){return toJSStr(E(_83));}),_85=function(_86){return new F(function(){return A3(_7t,B(_6l(B(_6n(B(_6p(_86)))))),_79,new T(function(){return B(_7Z(_86,_84));}));});},_87=new T(function(){return eval("(function(s){return document.createTextNode(s);})");}),_88=function(_89,_8a){var _8b=function(_){return new F(function(){return __app1(E(_87),E(_8a));});};return new F(function(){return A2(_7w,_89,_8b);});},_8c=function(_8d){return E(E(_8d).d);},_8e=32,_8f=new T2(1,_8e,_z),_8g=function(_8h){var _8i=E(_8h);return (_8i==1)?E(_8f):new T2(1,_8e,new T(function(){return B(_8g(_8i-1|0));}));},_8j=function(_8k,_8l){var _8m=new T(function(){return B(_88(_8k,new T(function(){var _8n=E(_8l);if(0>=_8n){return toJSStr(_z);}else{return toJSStr(B(_8g(_8n)));}},1)));});return new F(function(){return A3(_7t,B(_6l(B(_6n(B(_6p(_8k)))))),_79,_8m);});},_8o=new T(function(){return B(unCStr("n"));}),_8p=function(_8q,_8r,_8s,_8t,_8u,_8v){var _8w=function(_8x){var _8y=new T(function(){switch(E(_8s)){case 0:return E(E(_8v).a)+1|0;break;case 1:return E(_7S);break;default:return E(_7S);}}),_8z=new T(function(){var _8A=E(_8y);if(0>=_8A){return toJSStr(E(_6U));}else{return toJSStr(B(_6X(_8A)));}}),_8B=new T(function(){var _8C=function(_8D){switch(E(_8t)){case 0:var _8E=E(_8D);if(!_8E){return new F(function(){return _6G(_8o,0);});}else{return new F(function(){return _6G(B(_6S(_8E)),0);});}break;case 1:return 1;default:return 1;}};switch(E(_8t)){case 0:var _8F=E(E(_8v).a);if(0<=_8F){var _8G=function(_8H){return new T2(1,new T(function(){return B(_8C(_8H));}),new T(function(){if(_8H!=_8F){return B(_8G(_8H+1|0));}else{return __Z;}}));},_8I=E(B(_7H(_6k,B(_8G(0)))));if(_8I==2147483647){return E(_5J);}else{return _8I+1|0;}}else{var _8J=E(_7R);if(_8J==2147483647){return E(_5J);}else{return _8J+1|0;}}break;case 1:var _8K=function(_8L){return new T2(1,new T(function(){return B(_8C(_8L));}),new T(function(){var _8M=E(_8L);if(_8M==7){return __Z;}else{return B(_8K(_8M+1|0));}}));},_8N=E(B(_7H(_6k,B(_8K(0)))));if(_8N==2147483647){return E(_5J);}else{return _8N+1|0;}break;default:var _8O=function(_8P){return new T2(1,new T(function(){return B(_8C(_8P));}),new T(function(){var _8Q=E(_8P);if(_8Q==7){return __Z;}else{return B(_8O(_8Q+1|0));}}));},_8R=E(B(_7H(_6k,B(_8O(0)))));if(_8R==2147483647){return E(_5J);}else{return _8R+1|0;}}}),_8S=function(_8T){var _8U=new T(function(){return B(A3(_7t,B(_6l(B(_6n(B(_6p(_8T)))))),_79,new T(function(){return B(_88(_8T,_8z));})));});return new T2(1,new T(function(){return B(_8j(_8T,_8B));}),new T2(1,_8U,new T2(1,new T(function(){return B(_85(_8T));}),_z)));},_8V=B(_6p(_8q)),_8W=new T(function(){var _8X=function(_8Y){if(0<=_8Y){var _8Z=new T(function(){return B(_7Z(_8q,_7U));}),_90=new T(function(){return B(_8c(_8V));}),_91=new T(function(){return B(_8j(_8q,_7z));}),_92=function(_93){var _94=new T(function(){var _95=new T(function(){var _96=new T(function(){switch(E(_8s)){case 0:var _97=E(_93);if(!_97){return toJSStr(E(_8o));}else{return toJSStr(B(_6S(_97)));}break;case 1:return toJSStr(new T2(1,new T(function(){var _98=97+_93|0;if(_98>>>0>1114111){return B(_7r(_98));}else{return _98;}}),_z));break;default:return toJSStr(new T2(1,new T(function(){var _99=49+_93|0;if(_99>>>0>1114111){return B(_7r(_99));}else{return _99;}}),_z));}},1);return B(_88(_8q,_96));}),_9a=function(_9b){var _9c=new T(function(){var _9d=function(_9e){var _9f=function(_){var _9g=__app2(E(_7b),E(_9e),E(_9b));return new F(function(){return _5K(_);});};return new F(function(){return A2(_7w,_8q,_9f);});};return B(A3(_77,_8V,_95,_9d));});return new F(function(){return A3(_75,_8V,_9c,new T(function(){return B(A1(_90,new T1(1,_9b)));}));});};return B(A3(_77,_8V,_8Z,_9a));});return new T2(1,_94,new T2(1,_91,new T(function(){if(_93!=_8Y){return B(_92(_93+1|0));}else{return __Z;}})));};return new F(function(){return _92(0);});}else{return __Z;}};switch(E(_8s)){case 0:return B(_8X(E(E(_8v).a)));break;case 1:return B(_8X(7));break;default:return B(_8X(7));}}),_9h=new T(function(){return B(_8j(_8q,new T(function(){return E(_8B)+2|0;},1)));}),_9i=B(_7(new T2(1,_9h,_8W),new T2(1,new T(function(){return B(_85(_8q));}),new T(function(){return B(_8S(_8q));})))),_9j=new T(function(){return B(_6n(_8V));}),_9k=new T(function(){return B(_6l(_9j));}),_9l=new T(function(){return B(A2(_8c,_8V,_z));}),_9m=function(_9n){var _9o=E(_9n);if(!_9o._){return E(_9l);}else{return new F(function(){return A3(_73,_9j,new T(function(){return B(A3(_7t,_9k,_70,_9o.a));}),new T(function(){return B(_9m(_9o.b));}));});}};if(0<=_8x){var _9p=new T(function(){return B(A3(_7t,B(_6l(B(_6n(B(_6p(_8q)))))),_79,new T(function(){return B(_88(_8q,_7W));})));}),_9q=new T(function(){return B(_8c(_8V));}),_9r=new T(function(){return B(_7Z(_8q,_7U));}),_9s=new T(function(){return B(A2(_8c,_8V,_0));}),_9t=function(_9u,_9v){var _9w=new T(function(){var _9x=new T(function(){return B(_88(_8q,new T(function(){var _9y=E(_9u);return toJSStr(B(_7n(B(_5g(_9y.a,_9y.b,_9y.c,E(_8v).d)))));},1)));}),_9z=new T(function(){var _9A=E(E(_8v).c);if(!_9A._){return false;}else{var _9B=E(_9u),_9C=E(_9A.a);if(E(_9B.a)!=E(_9C.a)){return false;}else{if(E(_9B.b)!=E(_9C.b)){return false;}else{return E(_9B.c)==E(_9C.c);}}}}),_9D=function(_9E){var _9F=new T(function(){var _9G=new T(function(){if(!E(_9z)){return E(_9s);}else{var _9H=function(_){var _9I=__app3(E(_7v),E(_9E),toJSStr(E(_7X)),toJSStr(E(_7y)));return new F(function(){return _5K(_);});};return B(A2(_7w,_8q,_9H));}});return B(A3(_75,_8V,_9G,new T(function(){return B(A1(_9q,new T2(0,_9u,_9E)));})));}),_9J=new T(function(){var _9K=function(_9L){var _9M=function(_){var _9N=__app2(E(_7b),E(_9L),E(_9E));return new F(function(){return _5K(_);});};return new F(function(){return A2(_7w,_8q,_9M);});};return B(A3(_77,_8V,_9x,_9K));});return new F(function(){return A3(_75,_8V,_9J,_9F);});};return B(A3(_77,_8V,_9r,_9D));});return new T2(1,_9p,new T2(1,_9w,_9v));},_9O=new T2(1,_9p,new T2(1,new T(function(){return B(_85(_8q));}),_z)),_9P=function(_9Q,_9R){var _9S=E(_9Q);if(!_9S._){return E(_9O);}else{var _9T=_9S.a,_9U=E(_9R);if(_9U==1){return new F(function(){return _9t(_9T,_9O);});}else{return new F(function(){return _9t(_9T,new T(function(){return B(_9P(_9S.b,_9U-1|0));}));});}}},_9V=new T(function(){return B(_8S(_8q));}),_9W=function(_9X,_9Y){while(1){var _9Z=B((function(_a0,_a1){var _a2=new T(function(){var _a3=new T(function(){return B(_8j(_8q,new T(function(){var _a4=E(_8B);switch(E(_8t)){case 0:var _a5=E(_a0);if(!_a5){return _a4-B(_6G(_8o,0))|0;}else{return _a4-B(_6G(B(_6S(_a5)),0))|0;}break;case 1:return _a4-1|0;break;default:return _a4-1|0;}},1)));}),_a6=new T(function(){var _a7=new T(function(){var _a8=new T(function(){switch(E(_8t)){case 0:var _a9=E(_a0);if(!_a9){return toJSStr(E(_8o));}else{return toJSStr(B(_6S(_a9)));}break;case 1:return toJSStr(new T2(1,new T(function(){var _aa=97+_a0|0;if(_aa>>>0>1114111){return B(_7r(_aa));}else{return _aa;}}),_z));break;default:return toJSStr(new T2(1,new T(function(){var _ab=49+_a0|0;if(_ab>>>0>1114111){return B(_7r(_ab));}else{return _ab;}}),_z));}},1);return B(_88(_8q,_a8));}),_ac=function(_ad){var _ae=new T(function(){var _af=function(_ag){var _ah=function(_){var _ai=__app2(E(_7b),E(_ag),E(_ad));return new F(function(){return _5K(_);});};return new F(function(){return A2(_7w,_8q,_ah);});};return B(A3(_77,_8V,_a7,_af));});return new F(function(){return A3(_75,_8V,_ae,new T(function(){return B(A1(_9q,new T1(1,_ad)));}));});};return B(A3(_77,_8V,_9r,_ac));});return B(_7(new T2(1,_a6,new T2(1,_a3,new T(function(){var _aj=E(_8y);if(0>=_aj){return E(_9O);}else{return B(_9P(B(_6D(_8u,_a0)),_aj));}}))),_9V));},1),_ak=B(_7(_a1,_a2));if(_a0!=_8x){var _al=_a0+1|0;_9X=_al;_9Y=_ak;return __continue;}else{return E(_ak);}})(_9X,_9Y));if(_9Z!=__continue){return _9Z;}}};return new F(function(){return _9m(B(_9W(0,_9i)));});}else{return new F(function(){return _9m(_9i);});}};switch(E(_8t)){case 0:return new F(function(){return _8w(E(E(_8v).a));});break;case 1:return new F(function(){return _8w(7);});break;default:return new F(function(){return _8w(7);});}},_am=0,_an=0,_ao=new T(function(){return B(unCStr("foldl1"));}),_ap=new T(function(){return B(_7D(_ao));}),_aq=function(_ar){var _as=E(_ar);switch(_as._){case 0:return E(_as.b);case 1:return E(_as.a);default:return E(_as.a);}},_at=function(_au,_av,_){while(1){var _aw=B((function(_ax,_ay,_){var _az=E(_ax);if(!_az._){return new F(function(){return A1(_ay,_);});}else{_au=_az.b;_av=function(_){return new F(function(){return _3J(_ay,_az.a,_);});};return __continue;}})(_au,_av,_));if(_aw!=__continue){return _aw;}}},_aA=new T(function(){return B(unCStr("Pattern match failure in do expression at Web.hs:26:9-21"));}),_aB=new T6(0,_2u,_2v,_z,_aA,_2u,_2u),_aC=new T(function(){return B(_2s(_aB));}),_aD=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_aE=function(_aF,_aG){var _aH=function(_){var _aI=__app1(E(_aD),E(_aG)),_aJ=__eq(_aI,E(_2R));return (E(_aJ)==0)?new T1(1,_aI):_2u;};return new F(function(){return A2(_7w,_aF,_aH);});},_aK="board",_aL=new T(function(){return B(_aE(_45,_aK));}),_aM=function(_aN,_aO,_aP,_aQ){while(1){var _aR=E(_aQ);if(!_aR._){var _aS=_aR.d,_aT=_aR.e,_aU=E(_aR.b),_aV=E(_aU.a);if(_aN>=_aV){if(_aN!=_aV){_aQ=_aT;continue;}else{var _aW=E(_aU.b);if(_aO>=_aW){if(_aO!=_aW){_aQ=_aT;continue;}else{var _aX=E(_aU.c);if(_aP>=_aX){if(_aP!=_aX){_aQ=_aT;continue;}else{return new T1(1,_aR.c);}}else{_aQ=_aS;continue;}}}else{_aQ=_aS;continue;}}}else{_aQ=_aS;continue;}}else{return __Z;}}},_aY=function(_aZ,_b0,_b1,_b2){while(1){var _b3=E(_b2);if(!_b3._){var _b4=_b3.d,_b5=_b3.e,_b6=E(_b3.b),_b7=E(_b6.a);if(_aZ>=_b7){if(_aZ!=_b7){_b2=_b5;continue;}else{var _b8=E(_b6.b);if(_b0>=_b8){if(_b0!=_b8){_b2=_b5;continue;}else{var _b9=E(_b1),_ba=E(_b6.c);if(_b9>=_ba){if(_b9!=_ba){return new F(function(){return _aM(_aZ,_b0,_b9,_b5);});}else{return new T1(1,_b3.c);}}else{return new F(function(){return _aM(_aZ,_b0,_b9,_b4);});}}}else{_b2=_b4;continue;}}}else{_b2=_b4;continue;}}else{return __Z;}}},_bb=function(_bc,_bd,_be,_bf){while(1){var _bg=E(_bf);if(!_bg._){var _bh=_bg.d,_bi=_bg.e,_bj=E(_bg.b),_bk=E(_bj.a);if(_bc>=_bk){if(_bc!=_bk){_bf=_bi;continue;}else{var _bl=E(_bd),_bm=E(_bj.b);if(_bl>=_bm){if(_bl!=_bm){return new F(function(){return _aY(_bc,_bl,_be,_bi);});}else{var _bn=E(_be),_bo=E(_bj.c);if(_bn>=_bo){if(_bn!=_bo){return new F(function(){return _aM(_bc,_bl,_bn,_bi);});}else{return new T1(1,_bg.c);}}else{return new F(function(){return _aM(_bc,_bl,_bn,_bh);});}}}else{return new F(function(){return _aY(_bc,_bl,_be,_bh);});}}}else{_bf=_bh;continue;}}else{return __Z;}}},_bp=function(_bq,_br,_bs,_bt){var _bu=E(_bt);if(!_bu._){var _bv=_bu.d,_bw=_bu.e,_bx=E(_bu.b),_by=E(_bq),_bz=E(_bx.a);if(_by>=_bz){if(_by!=_bz){return new F(function(){return _bb(_by,_br,_bs,_bw);});}else{var _bA=E(_br),_bB=E(_bx.b);if(_bA>=_bB){if(_bA!=_bB){return new F(function(){return _aY(_by,_bA,_bs,_bw);});}else{var _bC=E(_bs),_bD=E(_bx.c);if(_bC>=_bD){if(_bC!=_bD){return new F(function(){return _aM(_by,_bA,_bC,_bw);});}else{return new T1(1,_bu.c);}}else{return new F(function(){return _aM(_by,_bA,_bC,_bv);});}}}else{return new F(function(){return _aY(_by,_bA,_bs,_bv);});}}}else{return new F(function(){return _bb(_by,_br,_bs,_bv);});}}else{return __Z;}},_bE=function(_bF){return false;},_bG=new T0(1),_bH=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_bI=function(_bJ){return new F(function(){return err(_bH);});},_bK=new T(function(){return B(_bI(_));}),_bL=function(_bM,_bN,_bO,_bP){var _bQ=E(_bP);if(!_bQ._){var _bR=_bQ.a,_bS=E(_bO);if(!_bS._){var _bT=_bS.a,_bU=_bS.b,_bV=_bS.c;if(_bT<=(imul(3,_bR)|0)){return new T5(0,(1+_bT|0)+_bR|0,E(_bM),_bN,E(_bS),E(_bQ));}else{var _bW=E(_bS.d);if(!_bW._){var _bX=_bW.a,_bY=E(_bS.e);if(!_bY._){var _bZ=_bY.a,_c0=_bY.b,_c1=_bY.c,_c2=_bY.d;if(_bZ>=(imul(2,_bX)|0)){var _c3=function(_c4){var _c5=E(_bY.e);return (_c5._==0)?new T5(0,(1+_bT|0)+_bR|0,E(_c0),_c1,E(new T5(0,(1+_bX|0)+_c4|0,E(_bU),_bV,E(_bW),E(_c2))),E(new T5(0,(1+_bR|0)+_c5.a|0,E(_bM),_bN,E(_c5),E(_bQ)))):new T5(0,(1+_bT|0)+_bR|0,E(_c0),_c1,E(new T5(0,(1+_bX|0)+_c4|0,E(_bU),_bV,E(_bW),E(_c2))),E(new T5(0,1+_bR|0,E(_bM),_bN,E(_bG),E(_bQ))));},_c6=E(_c2);if(!_c6._){return new F(function(){return _c3(_c6.a);});}else{return new F(function(){return _c3(0);});}}else{return new T5(0,(1+_bT|0)+_bR|0,E(_bU),_bV,E(_bW),E(new T5(0,(1+_bR|0)+_bZ|0,E(_bM),_bN,E(_bY),E(_bQ))));}}else{return E(_bK);}}else{return E(_bK);}}}else{return new T5(0,1+_bR|0,E(_bM),_bN,E(_bG),E(_bQ));}}else{var _c7=E(_bO);if(!_c7._){var _c8=_c7.a,_c9=_c7.b,_ca=_c7.c,_cb=_c7.e,_cc=E(_c7.d);if(!_cc._){var _cd=_cc.a,_ce=E(_cb);if(!_ce._){var _cf=_ce.a,_cg=_ce.b,_ch=_ce.c,_ci=_ce.d;if(_cf>=(imul(2,_cd)|0)){var _cj=function(_ck){var _cl=E(_ce.e);return (_cl._==0)?new T5(0,1+_c8|0,E(_cg),_ch,E(new T5(0,(1+_cd|0)+_ck|0,E(_c9),_ca,E(_cc),E(_ci))),E(new T5(0,1+_cl.a|0,E(_bM),_bN,E(_cl),E(_bG)))):new T5(0,1+_c8|0,E(_cg),_ch,E(new T5(0,(1+_cd|0)+_ck|0,E(_c9),_ca,E(_cc),E(_ci))),E(new T5(0,1,E(_bM),_bN,E(_bG),E(_bG))));},_cm=E(_ci);if(!_cm._){return new F(function(){return _cj(_cm.a);});}else{return new F(function(){return _cj(0);});}}else{return new T5(0,1+_c8|0,E(_c9),_ca,E(_cc),E(new T5(0,1+_cf|0,E(_bM),_bN,E(_ce),E(_bG))));}}else{return new T5(0,3,E(_c9),_ca,E(_cc),E(new T5(0,1,E(_bM),_bN,E(_bG),E(_bG))));}}else{var _cn=E(_cb);return (_cn._==0)?new T5(0,3,E(_cn.b),_cn.c,E(new T5(0,1,E(_c9),_ca,E(_bG),E(_bG))),E(new T5(0,1,E(_bM),_bN,E(_bG),E(_bG)))):new T5(0,2,E(_bM),_bN,E(_c7),E(_bG));}}else{return new T5(0,1,E(_bM),_bN,E(_bG),E(_bG));}}},_co=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_cp=function(_cq){return new F(function(){return err(_co);});},_cr=new T(function(){return B(_cp(_));}),_cs=function(_ct,_cu,_cv,_cw){var _cx=E(_cv);if(!_cx._){var _cy=_cx.a,_cz=E(_cw);if(!_cz._){var _cA=_cz.a,_cB=_cz.b,_cC=_cz.c;if(_cA<=(imul(3,_cy)|0)){return new T5(0,(1+_cy|0)+_cA|0,E(_ct),_cu,E(_cx),E(_cz));}else{var _cD=E(_cz.d);if(!_cD._){var _cE=_cD.a,_cF=_cD.b,_cG=_cD.c,_cH=_cD.d,_cI=E(_cz.e);if(!_cI._){var _cJ=_cI.a;if(_cE>=(imul(2,_cJ)|0)){var _cK=function(_cL){var _cM=E(_ct),_cN=E(_cD.e);return (_cN._==0)?new T5(0,(1+_cy|0)+_cA|0,E(_cF),_cG,E(new T5(0,(1+_cy|0)+_cL|0,E(_cM),_cu,E(_cx),E(_cH))),E(new T5(0,(1+_cJ|0)+_cN.a|0,E(_cB),_cC,E(_cN),E(_cI)))):new T5(0,(1+_cy|0)+_cA|0,E(_cF),_cG,E(new T5(0,(1+_cy|0)+_cL|0,E(_cM),_cu,E(_cx),E(_cH))),E(new T5(0,1+_cJ|0,E(_cB),_cC,E(_bG),E(_cI))));},_cO=E(_cH);if(!_cO._){return new F(function(){return _cK(_cO.a);});}else{return new F(function(){return _cK(0);});}}else{return new T5(0,(1+_cy|0)+_cA|0,E(_cB),_cC,E(new T5(0,(1+_cy|0)+_cE|0,E(_ct),_cu,E(_cx),E(_cD))),E(_cI));}}else{return E(_cr);}}else{return E(_cr);}}}else{return new T5(0,1+_cy|0,E(_ct),_cu,E(_cx),E(_bG));}}else{var _cP=E(_cw);if(!_cP._){var _cQ=_cP.a,_cR=_cP.b,_cS=_cP.c,_cT=_cP.e,_cU=E(_cP.d);if(!_cU._){var _cV=_cU.a,_cW=_cU.b,_cX=_cU.c,_cY=_cU.d,_cZ=E(_cT);if(!_cZ._){var _d0=_cZ.a;if(_cV>=(imul(2,_d0)|0)){var _d1=function(_d2){var _d3=E(_ct),_d4=E(_cU.e);return (_d4._==0)?new T5(0,1+_cQ|0,E(_cW),_cX,E(new T5(0,1+_d2|0,E(_d3),_cu,E(_bG),E(_cY))),E(new T5(0,(1+_d0|0)+_d4.a|0,E(_cR),_cS,E(_d4),E(_cZ)))):new T5(0,1+_cQ|0,E(_cW),_cX,E(new T5(0,1+_d2|0,E(_d3),_cu,E(_bG),E(_cY))),E(new T5(0,1+_d0|0,E(_cR),_cS,E(_bG),E(_cZ))));},_d5=E(_cY);if(!_d5._){return new F(function(){return _d1(_d5.a);});}else{return new F(function(){return _d1(0);});}}else{return new T5(0,1+_cQ|0,E(_cR),_cS,E(new T5(0,1+_cV|0,E(_ct),_cu,E(_bG),E(_cU))),E(_cZ));}}else{return new T5(0,3,E(_cW),_cX,E(new T5(0,1,E(_ct),_cu,E(_bG),E(_bG))),E(new T5(0,1,E(_cR),_cS,E(_bG),E(_bG))));}}else{var _d6=E(_cT);return (_d6._==0)?new T5(0,3,E(_cR),_cS,E(new T5(0,1,E(_ct),_cu,E(_bG),E(_bG))),E(_d6)):new T5(0,2,E(_ct),_cu,E(_bG),E(_cP));}}else{return new T5(0,1,E(_ct),_cu,E(_bG),E(_bG));}}},_d7=function(_d8,_d9,_da,_db,_dc){var _dd=E(_dc);if(!_dd._){var _de=new T(function(){var _df=B(_d7(_dd.a,_dd.b,_dd.c,_dd.d,_dd.e));return new T2(0,_df.a,_df.b);});return new T2(0,new T(function(){return E(E(_de).a);}),new T(function(){return B(_bL(_d9,_da,_db,E(_de).b));}));}else{return new T2(0,new T2(0,_d9,_da),_db);}},_dg=function(_dh,_di,_dj,_dk,_dl){var _dm=E(_dk);if(!_dm._){var _dn=new T(function(){var _do=B(_dg(_dm.a,_dm.b,_dm.c,_dm.d,_dm.e));return new T2(0,_do.a,_do.b);});return new T2(0,new T(function(){return E(E(_dn).a);}),new T(function(){return B(_cs(_di,_dj,E(_dn).b,_dl));}));}else{return new T2(0,new T2(0,_di,_dj),_dl);}},_dp=function(_dq,_dr){var _ds=E(_dq);if(!_ds._){var _dt=_ds.a,_du=E(_dr);if(!_du._){var _dv=_du.a;if(_dt<=_dv){var _dw=B(_dg(_dv,_du.b,_du.c,_du.d,_du.e)),_dx=E(_dw.a);return new F(function(){return _bL(_dx.a,_dx.b,_ds,_dw.b);});}else{var _dy=B(_d7(_dt,_ds.b,_ds.c,_ds.d,_ds.e)),_dz=E(_dy.a);return new F(function(){return _cs(_dz.a,_dz.b,_dy.b,_du);});}}else{return E(_ds);}}else{return E(_dr);}},_dA=function(_dB,_dC,_dD,_dE){var _dF=E(_dE);if(!_dF._){var _dG=_dF.c,_dH=_dF.d,_dI=_dF.e,_dJ=E(_dF.b),_dK=E(_dJ.a);if(_dB>=_dK){if(_dB!=_dK){return new F(function(){return _bL(_dJ,_dG,_dH,B(_dA(_dB,_dC,_dD,_dI)));});}else{var _dL=E(_dJ.b);if(_dC>=_dL){if(_dC!=_dL){return new F(function(){return _bL(_dJ,_dG,_dH,B(_dA(_dB,_dC,_dD,_dI)));});}else{var _dM=E(_dJ.c);if(_dD>=_dM){if(_dD!=_dM){return new F(function(){return _bL(_dJ,_dG,_dH,B(_dA(_dB,_dC,_dD,_dI)));});}else{return new F(function(){return _dp(_dH,_dI);});}}else{return new F(function(){return _cs(_dJ,_dG,B(_dA(_dB,_dC,_dD,_dH)),_dI);});}}}else{return new F(function(){return _cs(_dJ,_dG,B(_dA(_dB,_dC,_dD,_dH)),_dI);});}}}else{return new F(function(){return _cs(_dJ,_dG,B(_dA(_dB,_dC,_dD,_dH)),_dI);});}}else{return new T0(1);}},_dN=function(_dO,_dP,_dQ,_dR){var _dS=E(_dR);if(!_dS._){var _dT=_dS.c,_dU=_dS.d,_dV=_dS.e,_dW=E(_dS.b),_dX=E(_dW.a);if(_dO>=_dX){if(_dO!=_dX){return new F(function(){return _bL(_dW,_dT,_dU,B(_dN(_dO,_dP,_dQ,_dV)));});}else{var _dY=E(_dW.b);if(_dP>=_dY){if(_dP!=_dY){return new F(function(){return _bL(_dW,_dT,_dU,B(_dN(_dO,_dP,_dQ,_dV)));});}else{var _dZ=E(_dQ),_e0=E(_dW.c);if(_dZ>=_e0){if(_dZ!=_e0){return new F(function(){return _bL(_dW,_dT,_dU,B(_dA(_dO,_dP,_dZ,_dV)));});}else{return new F(function(){return _dp(_dU,_dV);});}}else{return new F(function(){return _cs(_dW,_dT,B(_dA(_dO,_dP,_dZ,_dU)),_dV);});}}}else{return new F(function(){return _cs(_dW,_dT,B(_dN(_dO,_dP,_dQ,_dU)),_dV);});}}}else{return new F(function(){return _cs(_dW,_dT,B(_dN(_dO,_dP,_dQ,_dU)),_dV);});}}else{return new T0(1);}},_e1=function(_e2,_e3,_e4,_e5){var _e6=E(_e5);if(!_e6._){var _e7=_e6.c,_e8=_e6.d,_e9=_e6.e,_ea=E(_e6.b),_eb=E(_ea.a);if(_e2>=_eb){if(_e2!=_eb){return new F(function(){return _bL(_ea,_e7,_e8,B(_e1(_e2,_e3,_e4,_e9)));});}else{var _ec=E(_e3),_ed=E(_ea.b);if(_ec>=_ed){if(_ec!=_ed){return new F(function(){return _bL(_ea,_e7,_e8,B(_dN(_e2,_ec,_e4,_e9)));});}else{var _ee=E(_e4),_ef=E(_ea.c);if(_ee>=_ef){if(_ee!=_ef){return new F(function(){return _bL(_ea,_e7,_e8,B(_dA(_e2,_ec,_ee,_e9)));});}else{return new F(function(){return _dp(_e8,_e9);});}}else{return new F(function(){return _cs(_ea,_e7,B(_dA(_e2,_ec,_ee,_e8)),_e9);});}}}else{return new F(function(){return _cs(_ea,_e7,B(_dN(_e2,_ec,_e4,_e8)),_e9);});}}}else{return new F(function(){return _cs(_ea,_e7,B(_e1(_e2,_e3,_e4,_e8)),_e9);});}}else{return new T0(1);}},_eg=function(_eh,_ei,_ej,_ek){var _el=E(_ek);if(!_el._){var _em=_el.c,_en=_el.d,_eo=_el.e,_ep=E(_el.b),_eq=E(_eh),_er=E(_ep.a);if(_eq>=_er){if(_eq!=_er){return new F(function(){return _bL(_ep,_em,_en,B(_e1(_eq,_ei,_ej,_eo)));});}else{var _es=E(_ei),_et=E(_ep.b);if(_es>=_et){if(_es!=_et){return new F(function(){return _bL(_ep,_em,_en,B(_dN(_eq,_es,_ej,_eo)));});}else{var _eu=E(_ej),_ev=E(_ep.c);if(_eu>=_ev){if(_eu!=_ev){return new F(function(){return _bL(_ep,_em,_en,B(_dA(_eq,_es,_eu,_eo)));});}else{return new F(function(){return _dp(_en,_eo);});}}else{return new F(function(){return _cs(_ep,_em,B(_dA(_eq,_es,_eu,_en)),_eo);});}}}else{return new F(function(){return _cs(_ep,_em,B(_dN(_eq,_es,_ej,_en)),_eo);});}}}else{return new F(function(){return _cs(_ep,_em,B(_e1(_eq,_ei,_ej,_en)),_eo);});}}else{return new T0(1);}},_ew=function(_ex,_ey,_ez){while(1){var _eA=E(_ey);if(!_eA._){return E(_ez);}else{var _eB=E(_eA.a),_eC=_eB.a,_eD=_eB.b,_eE=_eB.c,_eF=B(_bp(_eC,_eD,_eE,_ez));if(!_eF._){return new F(function(){return _eg(_eC,_eD,_eE,_ez);});}else{var _eG=B(A1(_ex,_eF.a)),_eH=B(_eg(_eC,_eD,_eE,_ez));_ey=_eG;_ez=_eH;continue;}}}},_eI=function(_eJ,_eK,_eL,_eM,_eN){var _eO=B(_bp(_eK,_eL,_eM,_eN));if(!_eO._){return new F(function(){return _eg(_eK,_eL,_eM,_eN);});}else{return new F(function(){return _ew(_eJ,B(A1(_eJ,_eO.a)),B(_eg(_eK,_eL,_eM,_eN)));});}},_eP=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_eQ=new T(function(){return B(err(_eP));}),_eR=function(_eS){var _eT=E(_eS);return (_eT._==0)?E(_eQ):E(_eT.a);},_eU=function(_eV,_eW,_eX,_eY){while(1){var _eZ=B((function(_f0,_f1,_f2,_f3){var _f4=E(_f2);if(!_f4._){return E(_f3);}else{var _f5=_f4.a,_f6=new T(function(){var _f7=E(_f5);return B(_bp(_f7.a,_f7.b,_f7.c,_f3));});if(!B(A1(_f1,new T(function(){return B(_eR(_f6));})))){var _f8=E(_f6);if(!_f8._){var _f9=E(_f5);return new F(function(){return _eg(_f9.a,_f9.b,_f9.c,_f3);});}else{var _fa=E(_f5),_fb=_f0,_fc=_f1,_fd=B(A1(_f0,_f8.a)),_fe=B(_eg(_fa.a,_fa.b,_fa.c,_f3));_eV=_fb;_eW=_fc;_eX=_fd;_eY=_fe;return __continue;}}else{return E(_f3);}}})(_eV,_eW,_eX,_eY));if(_eZ!=__continue){return _eZ;}}},_ff=function(_fg){return E(E(_fg).c);},_fh=function(_fi){return E(E(_fi).d);},_fj=function(_fk){return E(E(_fk).e);},_fl=function(_fm,_fn,_fo,_fp){var _fq=B(_bp(_fm,_fn,_fo,_fp));if(!_fq._){return new F(function(){return _eI(_fh,_fm,_fn,_fo,_fp);});}else{return new F(function(){return _eI(_fh,_fm,_fn,_fo,B(_eU(_fj,new T(function(){var _fr=B(_bp(_fm,_fn,_fo,_fp));if(!_fr._){return E(_bE);}else{if(!E(E(_fr.a).c)){return E(_bE);}else{return E(_ff);}}}),E(_fq.a).e,_fp)));});}},_fs=function(_ft,_fu,_fv,_fw,_fx){var _fy=E(_fx);if(!_fy._){var _fz=_fy.c,_fA=_fy.d,_fB=_fy.e,_fC=E(_fy.b),_fD=E(_fC.a);if(_ft>=_fD){if(_ft!=_fD){return new F(function(){return _cs(_fC,_fz,_fA,B(_fs(_ft,_fu,_fv,_fw,_fB)));});}else{var _fE=E(_fC.b);if(_fu>=_fE){if(_fu!=_fE){return new F(function(){return _cs(_fC,_fz,_fA,B(_fs(_ft,_fu,_fv,_fw,_fB)));});}else{var _fF=E(_fC.c);if(_fv>=_fF){if(_fv!=_fF){return new F(function(){return _cs(_fC,_fz,_fA,B(_fs(_ft,_fu,_fv,_fw,_fB)));});}else{return new T5(0,_fy.a,E(new T3(0,_ft,_fu,_fv)),_fw,E(_fA),E(_fB));}}else{return new F(function(){return _bL(_fC,_fz,B(_fs(_ft,_fu,_fv,_fw,_fA)),_fB);});}}}else{return new F(function(){return _bL(_fC,_fz,B(_fs(_ft,_fu,_fv,_fw,_fA)),_fB);});}}}else{return new F(function(){return _bL(_fC,_fz,B(_fs(_ft,_fu,_fv,_fw,_fA)),_fB);});}}else{return new T5(0,1,E(new T3(0,_ft,_fu,_fv)),_fw,E(_bG),E(_bG));}},_fG=function(_fH,_fI,_fJ,_fK,_fL){var _fM=E(_fL);if(!_fM._){var _fN=_fM.c,_fO=_fM.d,_fP=_fM.e,_fQ=E(_fM.b),_fR=E(_fQ.a);if(_fH>=_fR){if(_fH!=_fR){return new F(function(){return _cs(_fQ,_fN,_fO,B(_fG(_fH,_fI,_fJ,_fK,_fP)));});}else{var _fS=E(_fQ.b);if(_fI>=_fS){if(_fI!=_fS){return new F(function(){return _cs(_fQ,_fN,_fO,B(_fG(_fH,_fI,_fJ,_fK,_fP)));});}else{var _fT=E(_fJ),_fU=E(_fQ.c);if(_fT>=_fU){if(_fT!=_fU){return new F(function(){return _cs(_fQ,_fN,_fO,B(_fs(_fH,_fI,_fT,_fK,_fP)));});}else{return new T5(0,_fM.a,E(new T3(0,_fH,_fI,_fT)),_fK,E(_fO),E(_fP));}}else{return new F(function(){return _bL(_fQ,_fN,B(_fs(_fH,_fI,_fT,_fK,_fO)),_fP);});}}}else{return new F(function(){return _bL(_fQ,_fN,B(_fG(_fH,_fI,_fJ,_fK,_fO)),_fP);});}}}else{return new F(function(){return _bL(_fQ,_fN,B(_fG(_fH,_fI,_fJ,_fK,_fO)),_fP);});}}else{return new T5(0,1,E(new T3(0,_fH,_fI,_fJ)),_fK,E(_bG),E(_bG));}},_fV=function(_fW,_fX,_fY,_fZ,_g0){var _g1=E(_g0);if(!_g1._){var _g2=_g1.c,_g3=_g1.d,_g4=_g1.e,_g5=E(_g1.b),_g6=E(_g5.a);if(_fW>=_g6){if(_fW!=_g6){return new F(function(){return _cs(_g5,_g2,_g3,B(_fV(_fW,_fX,_fY,_fZ,_g4)));});}else{var _g7=E(_fX),_g8=E(_g5.b);if(_g7>=_g8){if(_g7!=_g8){return new F(function(){return _cs(_g5,_g2,_g3,B(_fG(_fW,_g7,_fY,_fZ,_g4)));});}else{var _g9=E(_fY),_ga=E(_g5.c);if(_g9>=_ga){if(_g9!=_ga){return new F(function(){return _cs(_g5,_g2,_g3,B(_fs(_fW,_g7,_g9,_fZ,_g4)));});}else{return new T5(0,_g1.a,E(new T3(0,_fW,_g7,_g9)),_fZ,E(_g3),E(_g4));}}else{return new F(function(){return _bL(_g5,_g2,B(_fs(_fW,_g7,_g9,_fZ,_g3)),_g4);});}}}else{return new F(function(){return _bL(_g5,_g2,B(_fG(_fW,_g7,_fY,_fZ,_g3)),_g4);});}}}else{return new F(function(){return _bL(_g5,_g2,B(_fV(_fW,_fX,_fY,_fZ,_g3)),_g4);});}}else{return new T5(0,1,E(new T3(0,_fW,_fX,_fY)),_fZ,E(_bG),E(_bG));}},_gb=function(_gc,_gd,_ge,_gf,_gg){var _gh=E(_gg);if(!_gh._){var _gi=_gh.c,_gj=_gh.d,_gk=_gh.e,_gl=E(_gh.b),_gm=E(_gc),_gn=E(_gl.a);if(_gm>=_gn){if(_gm!=_gn){return new F(function(){return _cs(_gl,_gi,_gj,B(_fV(_gm,_gd,_ge,_gf,_gk)));});}else{var _go=E(_gd),_gp=E(_gl.b);if(_go>=_gp){if(_go!=_gp){return new F(function(){return _cs(_gl,_gi,_gj,B(_fG(_gm,_go,_ge,_gf,_gk)));});}else{var _gq=E(_ge),_gr=E(_gl.c);if(_gq>=_gr){if(_gq!=_gr){return new F(function(){return _cs(_gl,_gi,_gj,B(_fs(_gm,_go,_gq,_gf,_gk)));});}else{return new T5(0,_gh.a,E(new T3(0,_gm,_go,_gq)),_gf,E(_gj),E(_gk));}}else{return new F(function(){return _bL(_gl,_gi,B(_fs(_gm,_go,_gq,_gf,_gj)),_gk);});}}}else{return new F(function(){return _bL(_gl,_gi,B(_fG(_gm,_go,_ge,_gf,_gj)),_gk);});}}}else{return new F(function(){return _bL(_gl,_gi,B(_fV(_gm,_gd,_ge,_gf,_gj)),_gk);});}}else{return new T5(0,1,E(new T3(0,_gc,_gd,_ge)),_gf,E(_bG),E(_bG));}},_gs=function(_gt,_gu,_gv,_gw){while(1){var _gx=E(_gw);if(!_gx._){var _gy=_gx.d,_gz=_gx.e,_gA=E(_gx.b),_gB=E(_gA.a);if(_gt>=_gB){if(_gt!=_gB){_gw=_gz;continue;}else{var _gC=E(_gA.b);if(_gu>=_gC){if(_gu!=_gC){_gw=_gz;continue;}else{var _gD=E(_gA.c);if(_gv>=_gD){if(_gv!=_gD){_gw=_gz;continue;}else{return new T1(1,_gx.c);}}else{_gw=_gy;continue;}}}else{_gw=_gy;continue;}}}else{_gw=_gy;continue;}}else{return __Z;}}},_gE=function(_gF,_gG,_gH,_gI){while(1){var _gJ=E(_gI);if(!_gJ._){var _gK=_gJ.d,_gL=_gJ.e,_gM=E(_gJ.b),_gN=E(_gM.a);if(_gF>=_gN){if(_gF!=_gN){_gI=_gL;continue;}else{var _gO=E(_gM.b);if(_gG>=_gO){if(_gG!=_gO){_gI=_gL;continue;}else{var _gP=E(_gH),_gQ=E(_gM.c);if(_gP>=_gQ){if(_gP!=_gQ){return new F(function(){return _gs(_gF,_gG,_gP,_gL);});}else{return new T1(1,_gJ.c);}}else{return new F(function(){return _gs(_gF,_gG,_gP,_gK);});}}}else{_gI=_gK;continue;}}}else{_gI=_gK;continue;}}else{return __Z;}}},_gR=function(_gS,_gT,_gU,_gV){while(1){var _gW=E(_gV);if(!_gW._){var _gX=_gW.d,_gY=_gW.e,_gZ=E(_gW.b),_h0=E(_gZ.a);if(_gS>=_h0){if(_gS!=_h0){_gV=_gY;continue;}else{var _h1=E(_gT),_h2=E(_gZ.b);if(_h1>=_h2){if(_h1!=_h2){return new F(function(){return _gE(_gS,_h1,_gU,_gY);});}else{var _h3=E(_gU),_h4=E(_gZ.c);if(_h3>=_h4){if(_h3!=_h4){return new F(function(){return _gs(_gS,_h1,_h3,_gY);});}else{return new T1(1,_gW.c);}}else{return new F(function(){return _gs(_gS,_h1,_h3,_gX);});}}}else{return new F(function(){return _gE(_gS,_h1,_gU,_gX);});}}}else{_gV=_gX;continue;}}else{return __Z;}}},_h5=function(_h6,_h7,_h8,_h9){var _ha=E(_h9);if(!_ha._){var _hb=_ha.d,_hc=_ha.e,_hd=E(_ha.b),_he=E(_h6),_hf=E(_hd.a);if(_he>=_hf){if(_he!=_hf){return new F(function(){return _gR(_he,_h7,_h8,_hc);});}else{var _hg=E(_h7),_hh=E(_hd.b);if(_hg>=_hh){if(_hg!=_hh){return new F(function(){return _gE(_he,_hg,_h8,_hc);});}else{var _hi=E(_h8),_hj=E(_hd.c);if(_hi>=_hj){if(_hi!=_hj){return new F(function(){return _gs(_he,_hg,_hi,_hc);});}else{return new T1(1,_ha.c);}}else{return new F(function(){return _gs(_he,_hg,_hi,_hb);});}}}else{return new F(function(){return _gE(_he,_hg,_h8,_hb);});}}}else{return new F(function(){return _gR(_he,_h7,_h8,_hb);});}}else{return __Z;}},_hk=function(_hl){while(1){var _hm=E(_hl);if(!_hm._){return __Z;}else{_hl=_hm.b;continue;}}},_hn=function(_ho,_hp){while(1){var _hq=E(_ho);if(!_hq._){return new T1(1,_hp);}else{var _hr=_hq.b;if(E(_hq.a)!=_hp){return new F(function(){return _hk(_hr);});}else{_ho=_hr;continue;}}}},_hs=new T(function(){return B(unCStr("head"));}),_ht=new T(function(){return B(_7D(_hs));}),_hu=function(_hv){while(1){var _hw=B((function(_hx){var _hy=E(_hx);if(!_hy._){return __Z;}else{var _hz=_hy.b,_hA=E(_hy.a),_hB=E(_hA);if(!_hB){_hv=_hz;return __continue;}else{return new T2(1,new T(function(){if(_hB<0){return  -_hB;}else{return E(_hA);}}),new T(function(){return B(_hu(_hz));}));}}})(_hv));if(_hw!=__continue){return _hw;}}},_hC=function(_hD){return E(E(_hD).c);},_hE=new T2(1,_hC,_z),_hF=function(_hG){return E(E(_hG).b);},_hH=new T2(1,_hF,_hE),_hI=function(_hJ){return E(E(_hJ).a);},_hK=new T2(1,_hI,_hH),_hL=0,_hM=new T1(1,_hL),_hN=-1,_hO=new T1(1,_hN),_hP=1,_hQ=new T1(1,_hP),_hR=function(_hS,_hT,_hU,_hV,_hW){var _hX=B(_4j(function(_hY){return B(A1(_hY,_hW))-B(A1(_hY,_hV))|0;},_hK)),_hZ=B(_hu(_hX)),_i0=E(_hZ);if(!_i0._){var _i1=new T1(1,_ht);}else{var _i1=B(_hn(_i0.b,E(_i0.a)));}var _i2=function(_i3){var _i4=function(_i5){var _i6=E(_hV),_i7=E(_hW),_i8=function(_i9){var _ia=function(_ib){var _ic=B(_6D(_hX,_ib));return (_ic<=0)?(_ic>=0)?E(_hM):E(_hO):E(_hQ);},_id=B(_ia(0));if(!_id._){return __Z;}else{var _ie=B(_ia(1));if(!_ie._){return __Z;}else{var _if=B(_ia(2));if(!_if._){return __Z;}else{var _ig=E(_i1);return (_ig._==0)?__Z:new T1(1,new T5(0,_id.a,_ie.a,_if.a,_ig.a,_i6));}}}};if(E(_i6.a)!=E(_i7.a)){return new F(function(){return _i8(_);});}else{if(E(_i6.b)!=E(_i7.b)){return new F(function(){return _i8(_);});}else{if(E(_i6.c)!=E(_i7.c)){return new F(function(){return _i8(_);});}else{return new T1(1,new T5(0,_hL,_hL,_hL,_hL,_i6));}}}};if(!E(_hS)){if(!E(_hT)){return __Z;}else{if(B(_6G(_hZ,0))==2){return new F(function(){return _i4(_);});}else{return __Z;}}}else{var _ih=B(_6G(_hZ,0));if(_ih==1){return new F(function(){return _i4(_);});}else{if(!E(_hT)){return __Z;}else{if(E(_ih)==2){return new F(function(){return _i4(_);});}else{return __Z;}}}}},_ii=E(_i1);if(!_ii._){return new F(function(){return _i2(_);});}else{var _ij=E(_hU);if(!_ij._){return new F(function(){return _i2(_);});}else{if(E(_ii.a)<=E(_ij.a)){return new F(function(){return _i2(_);});}else{return __Z;}}}},_ik=false,_il=true,_im=function(_in,_io,_ip,_iq,_ir,_is,_it){var _iu=E(_iq);if(!_iu){return __Z;}else{var _iv=new T(function(){return E(_ip)+E(_it)|0;}),_iw=new T(function(){return E(_io)+E(_is)|0;}),_ix=new T(function(){return E(_in)+E(_ir)|0;});return new T2(1,new T3(0,_ix,_iw,_iv),new T(function(){return B(_im(_in,_io,_ip,_iu-1|0,_ix,_iw,_iv));}));}},_iy=function(_iz,_iA,_iB,_iC,_iD){var _iE=E(_iC);if(!_iE){return __Z;}else{var _iF=new T(function(){return E(_iB)+E(E(_iD).c)|0;}),_iG=new T(function(){return E(_iA)+E(E(_iD).b)|0;}),_iH=new T(function(){return E(_iz)+E(E(_iD).a)|0;});return new T2(1,new T3(0,_iH,_iG,_iF),new T(function(){return B(_im(_iz,_iA,_iB,_iE-1|0,_iH,_iG,_iF));}));}},_iI=function(_iJ){var _iK=E(_iJ);return new F(function(){return _iy(_iK.a,_iK.b,_iK.c,E(_iK.d),_iK.e);});},_iL=function(_iM,_iN,_iO,_iP,_iQ){while(1){var _iR=B((function(_iS,_iT,_iU,_iV,_iW){var _iX=E(_iV);if(!_iX._){return E(_iW);}else{var _iY=_iX.b,_iZ=E(_iX.a),_j0=new T(function(){if(!B(_6G(_iY,0))){return __Z;}else{return new T1(1,new T(function(){var _j1=E(_iY);if(!_j1._){return E(_ht);}else{return E(_j1.a);}}));}}),_j2=_iS,_j3=_iT,_j4=B(_gb(_iZ.a,_iZ.b,_iZ.c,new T5(0,_iS,_iT,_ik,_j0,_iU),_iW));_iM=_j2;_iN=_j3;_iO=new T1(1,_iZ);_iP=_iY;_iQ=_j4;return __continue;}})(_iM,_iN,_iO,_iP,_iQ));if(_iR!=__continue){return _iR;}}},_j5=function(_j6,_j7,_j8,_j9,_ja,_jb,_jc){var _jd=B(_hR(_j6,_j7,_j8,_ja,_jb));if(!_jd._){return __Z;}else{var _je=B(_iI(_jd.a)),_jf=function(_jg,_jh){while(1){var _ji=B((function(_jj,_jk){var _jl=E(_jj);if(!_jl._){return E(_jk);}else{_jg=_jl.b;_jh=new T(function(){var _jm=E(_jl.a);if(!B(_h5(_jm.a,_jm.b,_jm.c,_jc))._){return E(_jk);}else{return true;}},1);return __continue;}})(_jg,_jh));if(_ji!=__continue){return _ji;}}};if(!B(_jf(_je,_ik))){var _jn=E(_ja),_jo=_jn.a,_jp=_jn.b,_jq=_jn.c,_jr=B(_h5(_jo,_jp,_jq,_jc));if(!_jr._){return __Z;}else{var _js=_jr.a,_jt=E(_j9);if(!_jt._){return __Z;}else{var _ju=_jt.a,_jv=new T(function(){return B(_gb(_jo,_jp,_jq,new T5(0,new T(function(){return E(E(_js).a);}),new T(function(){return E(E(_js).b);}),_il,new T1(1,new T(function(){var _jw=E(_je);if(!_jw._){return E(_ht);}else{return E(_jw.a);}})),new T(function(){return E(E(_js).e);})),B(_iL(new T(function(){return E(E(_ju).a);}),new T(function(){return E(E(_ju).b);}),new T1(1,_jn),_je,_jc))));});return new T1(1,_jv);}}}else{return __Z;}}},_jx=function(_jy,_jz,_jA,_jB){while(1){var _jC=E(_jB);if(!_jC._){var _jD=_jC.d,_jE=_jC.e,_jF=E(_jC.b),_jG=E(_jF.a);if(_jy>=_jG){if(_jy!=_jG){_jB=_jE;continue;}else{var _jH=E(_jF.b);if(_jz>=_jH){if(_jz!=_jH){_jB=_jE;continue;}else{var _jI=E(_jF.c);if(_jA>=_jI){if(_jA!=_jI){_jB=_jE;continue;}else{return new T1(1,_jC.c);}}else{_jB=_jD;continue;}}}else{_jB=_jD;continue;}}}else{_jB=_jD;continue;}}else{return __Z;}}},_jJ=function(_jK,_jL,_jM,_jN){while(1){var _jO=E(_jN);if(!_jO._){var _jP=_jO.d,_jQ=_jO.e,_jR=E(_jO.b),_jS=E(_jR.a);if(_jK>=_jS){if(_jK!=_jS){_jN=_jQ;continue;}else{var _jT=E(_jR.b);if(_jL>=_jT){if(_jL!=_jT){_jN=_jQ;continue;}else{var _jU=E(_jM),_jV=E(_jR.c);if(_jU>=_jV){if(_jU!=_jV){return new F(function(){return _jx(_jK,_jL,_jU,_jQ);});}else{return new T1(1,_jO.c);}}else{return new F(function(){return _jx(_jK,_jL,_jU,_jP);});}}}else{_jN=_jP;continue;}}}else{_jN=_jP;continue;}}else{return __Z;}}},_jW=function(_jX,_jY,_jZ,_k0){while(1){var _k1=E(_k0);if(!_k1._){var _k2=_k1.d,_k3=_k1.e,_k4=E(_k1.b),_k5=E(_k4.a);if(_jX>=_k5){if(_jX!=_k5){_k0=_k3;continue;}else{var _k6=E(_jY),_k7=E(_k4.b);if(_k6>=_k7){if(_k6!=_k7){return new F(function(){return _jJ(_jX,_k6,_jZ,_k3);});}else{var _k8=E(_jZ),_k9=E(_k4.c);if(_k8>=_k9){if(_k8!=_k9){return new F(function(){return _jx(_jX,_k6,_k8,_k3);});}else{return new T1(1,_k1.c);}}else{return new F(function(){return _jx(_jX,_k6,_k8,_k2);});}}}else{return new F(function(){return _jJ(_jX,_k6,_jZ,_k2);});}}}else{_k0=_k2;continue;}}else{return __Z;}}},_ka=function(_kb,_kc,_kd,_ke){var _kf=E(_ke);if(!_kf._){var _kg=_kf.d,_kh=_kf.e,_ki=E(_kf.b),_kj=E(_kb),_kk=E(_ki.a);if(_kj>=_kk){if(_kj!=_kk){return new F(function(){return _jW(_kj,_kc,_kd,_kh);});}else{var _kl=E(_kc),_km=E(_ki.b);if(_kl>=_km){if(_kl!=_km){return new F(function(){return _jJ(_kj,_kl,_kd,_kh);});}else{var _kn=E(_kd),_ko=E(_ki.c);if(_kn>=_ko){if(_kn!=_ko){return new F(function(){return _jx(_kj,_kl,_kn,_kh);});}else{return new T1(1,_kf.c);}}else{return new F(function(){return _jx(_kj,_kl,_kn,_kg);});}}}else{return new F(function(){return _jJ(_kj,_kl,_kd,_kg);});}}}else{return new F(function(){return _jW(_kj,_kc,_kd,_kg);});}}else{return __Z;}},_kp=function(_kq,_kr){var _ks=E(_kq),_kt=E(_kr);return (E(_ks.a)!=E(_kt.a))?true:(E(_ks.b)!=E(_kt.b))?true:(E(_ks.c)!=E(_kt.c))?true:false;},_ku=function(_kv,_kw,_kx,_ky,_kz,_kA){if(_kv!=_ky){return false;}else{if(E(_kw)!=E(_kz)){return false;}else{return new F(function(){return _5L(_kx,_kA);});}}},_kB=function(_kC,_kD){var _kE=E(_kC),_kF=E(_kD);return new F(function(){return _ku(E(_kE.a),_kE.b,_kE.c,E(_kF.a),_kF.b,_kF.c);});},_kG=new T2(0,_kB,_kp),_kH=function(_kI,_kJ,_kK,_kL,_kM,_kN){if(_kI>=_kL){if(_kI!=_kL){return false;}else{var _kO=E(_kJ),_kP=E(_kM);if(_kO>=_kP){if(_kO!=_kP){return false;}else{return new F(function(){return _6h(_kK,_kN);});}}else{return true;}}}else{return true;}},_kQ=function(_kR,_kS){var _kT=E(_kR),_kU=E(_kS);return new F(function(){return _kH(E(_kT.a),_kT.b,_kT.c,E(_kU.a),_kU.b,_kU.c);});},_kV=function(_kW,_kX,_kY,_kZ,_l0,_l1){if(_kW>=_kZ){if(_kW!=_kZ){return false;}else{var _l2=E(_kX),_l3=E(_l0);if(_l2>=_l3){if(_l2!=_l3){return false;}else{return new F(function(){return _6e(_kY,_l1);});}}else{return true;}}}else{return true;}},_l4=function(_l5,_l6){var _l7=E(_l5),_l8=E(_l6);return new F(function(){return _kV(E(_l7.a),_l7.b,_l7.c,E(_l8.a),_l8.b,_l8.c);});},_l9=function(_la,_lb,_lc,_ld,_le,_lf){if(_la>=_ld){if(_la!=_ld){return true;}else{var _lg=E(_lb),_lh=E(_le);if(_lg>=_lh){if(_lg!=_lh){return true;}else{return new F(function(){return _6b(_lc,_lf);});}}else{return false;}}}else{return false;}},_li=function(_lj,_lk){var _ll=E(_lj),_lm=E(_lk);return new F(function(){return _l9(E(_ll.a),_ll.b,_ll.c,E(_lm.a),_lm.b,_lm.c);});},_ln=function(_lo,_lp,_lq,_lr,_ls,_lt){if(_lo>=_lr){if(_lo!=_lr){return true;}else{var _lu=E(_lp),_lv=E(_ls);if(_lu>=_lv){if(_lu!=_lv){return true;}else{return new F(function(){return _68(_lq,_lt);});}}else{return false;}}}else{return false;}},_lw=function(_lx,_ly){var _lz=E(_lx),_lA=E(_ly);return new F(function(){return _ln(E(_lz.a),_lz.b,_lz.c,E(_lA.a),_lA.b,_lA.c);});},_lB=function(_lC,_lD,_lE,_lF,_lG,_lH){if(_lC>=_lF){if(_lC!=_lF){return 2;}else{var _lI=E(_lD),_lJ=E(_lG);if(_lI>=_lJ){if(_lI!=_lJ){return 2;}else{return new F(function(){return _65(_lE,_lH);});}}else{return 0;}}}else{return 0;}},_lK=function(_lL,_lM){var _lN=E(_lL),_lO=E(_lM);return new F(function(){return _lB(E(_lN.a),_lN.b,_lN.c,E(_lO.a),_lO.b,_lO.c);});},_lP=function(_lQ,_lR){var _lS=E(_lQ),_lT=E(_lS.a),_lU=E(_lR),_lV=E(_lU.a);if(_lT>=_lV){if(_lT!=_lV){return E(_lS);}else{var _lW=E(_lS.b),_lX=E(_lU.b);return (_lW>=_lX)?(_lW!=_lX)?E(_lS):(E(_lS.c)>E(_lU.c))?E(_lS):E(_lU):E(_lU);}}else{return E(_lU);}},_lY=function(_lZ,_m0){var _m1=E(_lZ),_m2=E(_m1.a),_m3=E(_m0),_m4=E(_m3.a);if(_m2>=_m4){if(_m2!=_m4){return E(_m3);}else{var _m5=E(_m1.b),_m6=E(_m3.b);return (_m5>=_m6)?(_m5!=_m6)?E(_m3):(E(_m1.c)>E(_m3.c))?E(_m3):E(_m1):E(_m1);}}else{return E(_m1);}},_m7={_:0,a:_kG,b:_lK,c:_kQ,d:_l4,e:_li,f:_lw,g:_lP,h:_lY},_m8=function(_m9,_ma){return new T5(0,1,E(_m9),_ma,E(_bG),E(_bG));},_mb=function(_mc,_md,_me){var _mf=E(_me);if(!_mf._){return new F(function(){return _cs(_mf.b,_mf.c,_mf.d,B(_mb(_mc,_md,_mf.e)));});}else{return new F(function(){return _m8(_mc,_md);});}},_mg=function(_mh,_mi,_mj){var _mk=E(_mj);if(!_mk._){return new F(function(){return _bL(_mk.b,_mk.c,B(_mg(_mh,_mi,_mk.d)),_mk.e);});}else{return new F(function(){return _m8(_mh,_mi);});}},_ml=function(_mm,_mn,_mo,_mp,_mq,_mr,_ms){return new F(function(){return _bL(_mp,_mq,B(_mg(_mm,_mn,_mr)),_ms);});},_mt=function(_mu,_mv,_mw,_mx,_my,_mz,_mA,_mB){var _mC=E(_mw);if(!_mC._){var _mD=_mC.a,_mE=_mC.b,_mF=_mC.c,_mG=_mC.d,_mH=_mC.e;if((imul(3,_mD)|0)>=_mx){if((imul(3,_mx)|0)>=_mD){return new T5(0,(_mD+_mx|0)+1|0,E(_mu),_mv,E(_mC),E(new T5(0,_mx,E(_my),_mz,E(_mA),E(_mB))));}else{return new F(function(){return _cs(_mE,_mF,_mG,B(_mt(_mu,_mv,_mH,_mx,_my,_mz,_mA,_mB)));});}}else{return new F(function(){return _bL(_my,_mz,B(_mI(_mu,_mv,_mD,_mE,_mF,_mG,_mH,_mA)),_mB);});}}else{return new F(function(){return _ml(_mu,_mv,_mx,_my,_mz,_mA,_mB);});}},_mI=function(_mJ,_mK,_mL,_mM,_mN,_mO,_mP,_mQ){var _mR=E(_mQ);if(!_mR._){var _mS=_mR.a,_mT=_mR.b,_mU=_mR.c,_mV=_mR.d,_mW=_mR.e;if((imul(3,_mL)|0)>=_mS){if((imul(3,_mS)|0)>=_mL){return new T5(0,(_mL+_mS|0)+1|0,E(_mJ),_mK,E(new T5(0,_mL,E(_mM),_mN,E(_mO),E(_mP))),E(_mR));}else{return new F(function(){return _cs(_mM,_mN,_mO,B(_mt(_mJ,_mK,_mP,_mS,_mT,_mU,_mV,_mW)));});}}else{return new F(function(){return _bL(_mT,_mU,B(_mI(_mJ,_mK,_mL,_mM,_mN,_mO,_mP,_mV)),_mW);});}}else{return new F(function(){return _mb(_mJ,_mK,new T5(0,_mL,E(_mM),_mN,E(_mO),E(_mP)));});}},_mX=function(_mY,_mZ,_n0,_n1){var _n2=E(_n0);if(!_n2._){var _n3=_n2.a,_n4=_n2.b,_n5=_n2.c,_n6=_n2.d,_n7=_n2.e,_n8=E(_n1);if(!_n8._){var _n9=_n8.a,_na=_n8.b,_nb=_n8.c,_nc=_n8.d,_nd=_n8.e;if((imul(3,_n3)|0)>=_n9){if((imul(3,_n9)|0)>=_n3){return new T5(0,(_n3+_n9|0)+1|0,E(_mY),_mZ,E(_n2),E(_n8));}else{return new F(function(){return _cs(_n4,_n5,_n6,B(_mt(_mY,_mZ,_n7,_n9,_na,_nb,_nc,_nd)));});}}else{return new F(function(){return _bL(_na,_nb,B(_mI(_mY,_mZ,_n3,_n4,_n5,_n6,_n7,_nc)),_nd);});}}else{return new F(function(){return _mb(_mY,_mZ,_n2);});}}else{return new F(function(){return _mg(_mY,_mZ,_n1);});}},_ne=function(_nf,_ng,_nh,_ni,_nj,_nk){var _nl=E(_nf);if(_nl==1){var _nm=E(_nk);if(!_nm._){return new T3(0,new T5(0,1,E(new T3(0,_ng,_nh,_ni)),_nj,E(_bG),E(_bG)),_z,_z);}else{var _nn=E(E(_nm.a).a),_no=E(_nn.a);if(_ng>=_no){if(_ng!=_no){return new T3(0,new T5(0,1,E(new T3(0,_ng,_nh,_ni)),_nj,E(_bG),E(_bG)),_z,_nm);}else{var _np=E(_nn.b);return (_nh>=_np)?(_nh!=_np)?new T3(0,new T5(0,1,E(new T3(0,_ng,_nh,_ni)),_nj,E(_bG),E(_bG)),_z,_nm):(_ni<E(_nn.c))?new T3(0,new T5(0,1,E(new T3(0,_ng,_nh,_ni)),_nj,E(_bG),E(_bG)),_nm,_z):new T3(0,new T5(0,1,E(new T3(0,_ng,_nh,_ni)),_nj,E(_bG),E(_bG)),_z,_nm):new T3(0,new T5(0,1,E(new T3(0,_ng,_nh,_ni)),_nj,E(_bG),E(_bG)),_nm,_z);}}else{return new T3(0,new T5(0,1,E(new T3(0,_ng,_nh,_ni)),_nj,E(_bG),E(_bG)),_nm,_z);}}}else{var _nq=B(_ne(_nl>>1,_ng,_nh,_ni,_nj,_nk)),_nr=_nq.a,_ns=_nq.c,_nt=E(_nq.b);if(!_nt._){return new T3(0,_nr,_z,_ns);}else{var _nu=E(_nt.a),_nv=_nu.a,_nw=_nu.b,_nx=E(_nt.b);if(!_nx._){return new T3(0,new T(function(){return B(_mb(_nv,_nw,_nr));}),_z,_ns);}else{var _ny=_nx.b,_nz=E(_nx.a),_nA=_nz.b,_nB=E(_nv),_nC=E(_nB.a),_nD=E(_nz.a),_nE=_nD.b,_nF=_nD.c,_nG=E(_nD.a);if(_nC>=_nG){if(_nC!=_nG){return new T3(0,_nr,_z,_nt);}else{var _nH=E(_nB.b),_nI=E(_nE);if(_nH>=_nI){if(_nH!=_nI){return new T3(0,_nr,_z,_nt);}else{var _nJ=E(_nF);if(E(_nB.c)<_nJ){var _nK=B(_ne(_nl>>1,_nG,_nI,_nJ,_nA,_ny));return new T3(0,new T(function(){return B(_mX(_nB,_nw,_nr,_nK.a));}),_nK.b,_nK.c);}else{return new T3(0,_nr,_z,_nt);}}}else{var _nL=B(_nM(_nl>>1,_nG,_nI,_nF,_nA,_ny));return new T3(0,new T(function(){return B(_mX(_nB,_nw,_nr,_nL.a));}),_nL.b,_nL.c);}}}else{var _nN=B(_nO(_nl>>1,_nG,_nE,_nF,_nA,_ny));return new T3(0,new T(function(){return B(_mX(_nB,_nw,_nr,_nN.a));}),_nN.b,_nN.c);}}}}},_nM=function(_nP,_nQ,_nR,_nS,_nT,_nU){var _nV=E(_nP);if(_nV==1){var _nW=E(_nU);if(!_nW._){return new T3(0,new T5(0,1,E(new T3(0,_nQ,_nR,_nS)),_nT,E(_bG),E(_bG)),_z,_z);}else{var _nX=E(E(_nW.a).a),_nY=E(_nX.a);if(_nQ>=_nY){if(_nQ!=_nY){return new T3(0,new T5(0,1,E(new T3(0,_nQ,_nR,_nS)),_nT,E(_bG),E(_bG)),_z,_nW);}else{var _nZ=E(_nX.b);if(_nR>=_nZ){if(_nR!=_nZ){return new T3(0,new T5(0,1,E(new T3(0,_nQ,_nR,_nS)),_nT,E(_bG),E(_bG)),_z,_nW);}else{var _o0=E(_nS);return (_o0<E(_nX.c))?new T3(0,new T5(0,1,E(new T3(0,_nQ,_nR,_o0)),_nT,E(_bG),E(_bG)),_nW,_z):new T3(0,new T5(0,1,E(new T3(0,_nQ,_nR,_o0)),_nT,E(_bG),E(_bG)),_z,_nW);}}else{return new T3(0,new T5(0,1,E(new T3(0,_nQ,_nR,_nS)),_nT,E(_bG),E(_bG)),_nW,_z);}}}else{return new T3(0,new T5(0,1,E(new T3(0,_nQ,_nR,_nS)),_nT,E(_bG),E(_bG)),_nW,_z);}}}else{var _o1=B(_nM(_nV>>1,_nQ,_nR,_nS,_nT,_nU)),_o2=_o1.a,_o3=_o1.c,_o4=E(_o1.b);if(!_o4._){return new T3(0,_o2,_z,_o3);}else{var _o5=E(_o4.a),_o6=_o5.a,_o7=_o5.b,_o8=E(_o4.b);if(!_o8._){return new T3(0,new T(function(){return B(_mb(_o6,_o7,_o2));}),_z,_o3);}else{var _o9=_o8.b,_oa=E(_o8.a),_ob=_oa.b,_oc=E(_o6),_od=E(_oc.a),_oe=E(_oa.a),_of=_oe.b,_og=_oe.c,_oh=E(_oe.a);if(_od>=_oh){if(_od!=_oh){return new T3(0,_o2,_z,_o4);}else{var _oi=E(_oc.b),_oj=E(_of);if(_oi>=_oj){if(_oi!=_oj){return new T3(0,_o2,_z,_o4);}else{var _ok=E(_og);if(E(_oc.c)<_ok){var _ol=B(_ne(_nV>>1,_oh,_oj,_ok,_ob,_o9));return new T3(0,new T(function(){return B(_mX(_oc,_o7,_o2,_ol.a));}),_ol.b,_ol.c);}else{return new T3(0,_o2,_z,_o4);}}}else{var _om=B(_nM(_nV>>1,_oh,_oj,_og,_ob,_o9));return new T3(0,new T(function(){return B(_mX(_oc,_o7,_o2,_om.a));}),_om.b,_om.c);}}}else{var _on=B(_nO(_nV>>1,_oh,_of,_og,_ob,_o9));return new T3(0,new T(function(){return B(_mX(_oc,_o7,_o2,_on.a));}),_on.b,_on.c);}}}}},_nO=function(_oo,_op,_oq,_or,_os,_ot){var _ou=E(_oo);if(_ou==1){var _ov=E(_ot);if(!_ov._){return new T3(0,new T5(0,1,E(new T3(0,_op,_oq,_or)),_os,E(_bG),E(_bG)),_z,_z);}else{var _ow=E(E(_ov.a).a),_ox=E(_ow.a);if(_op>=_ox){if(_op!=_ox){return new T3(0,new T5(0,1,E(new T3(0,_op,_oq,_or)),_os,E(_bG),E(_bG)),_z,_ov);}else{var _oy=E(_oq),_oz=E(_ow.b);if(_oy>=_oz){if(_oy!=_oz){return new T3(0,new T5(0,1,E(new T3(0,_op,_oy,_or)),_os,E(_bG),E(_bG)),_z,_ov);}else{var _oA=E(_or);return (_oA<E(_ow.c))?new T3(0,new T5(0,1,E(new T3(0,_op,_oy,_oA)),_os,E(_bG),E(_bG)),_ov,_z):new T3(0,new T5(0,1,E(new T3(0,_op,_oy,_oA)),_os,E(_bG),E(_bG)),_z,_ov);}}else{return new T3(0,new T5(0,1,E(new T3(0,_op,_oy,_or)),_os,E(_bG),E(_bG)),_ov,_z);}}}else{return new T3(0,new T5(0,1,E(new T3(0,_op,_oq,_or)),_os,E(_bG),E(_bG)),_ov,_z);}}}else{var _oB=B(_nO(_ou>>1,_op,_oq,_or,_os,_ot)),_oC=_oB.a,_oD=_oB.c,_oE=E(_oB.b);if(!_oE._){return new T3(0,_oC,_z,_oD);}else{var _oF=E(_oE.a),_oG=_oF.a,_oH=_oF.b,_oI=E(_oE.b);if(!_oI._){return new T3(0,new T(function(){return B(_mb(_oG,_oH,_oC));}),_z,_oD);}else{var _oJ=_oI.b,_oK=E(_oI.a),_oL=_oK.b,_oM=E(_oG),_oN=E(_oM.a),_oO=E(_oK.a),_oP=_oO.b,_oQ=_oO.c,_oR=E(_oO.a);if(_oN>=_oR){if(_oN!=_oR){return new T3(0,_oC,_z,_oE);}else{var _oS=E(_oM.b),_oT=E(_oP);if(_oS>=_oT){if(_oS!=_oT){return new T3(0,_oC,_z,_oE);}else{var _oU=E(_oQ);if(E(_oM.c)<_oU){var _oV=B(_ne(_ou>>1,_oR,_oT,_oU,_oL,_oJ));return new T3(0,new T(function(){return B(_mX(_oM,_oH,_oC,_oV.a));}),_oV.b,_oV.c);}else{return new T3(0,_oC,_z,_oE);}}}else{var _oW=B(_nM(_ou>>1,_oR,_oT,_oQ,_oL,_oJ));return new T3(0,new T(function(){return B(_mX(_oM,_oH,_oC,_oW.a));}),_oW.b,_oW.c);}}}else{var _oX=B(_nO(_ou>>1,_oR,_oP,_oQ,_oL,_oJ));return new T3(0,new T(function(){return B(_mX(_oM,_oH,_oC,_oX.a));}),_oX.b,_oX.c);}}}}},_oY=function(_oZ,_p0,_p1,_p2,_p3){var _p4=E(_p3);if(!_p4._){var _p5=_p4.c,_p6=_p4.d,_p7=_p4.e,_p8=E(_p4.b),_p9=E(_p8.a);if(_oZ>=_p9){if(_oZ!=_p9){return new F(function(){return _cs(_p8,_p5,_p6,B(_oY(_oZ,_p0,_p1,_p2,_p7)));});}else{var _pa=E(_p8.b);if(_p0>=_pa){if(_p0!=_pa){return new F(function(){return _cs(_p8,_p5,_p6,B(_oY(_oZ,_p0,_p1,_p2,_p7)));});}else{var _pb=E(_p8.c);if(_p1>=_pb){if(_p1!=_pb){return new F(function(){return _cs(_p8,_p5,_p6,B(_oY(_oZ,_p0,_p1,_p2,_p7)));});}else{return new T5(0,_p4.a,E(new T3(0,_oZ,_p0,_p1)),_p2,E(_p6),E(_p7));}}else{return new F(function(){return _bL(_p8,_p5,B(_oY(_oZ,_p0,_p1,_p2,_p6)),_p7);});}}}else{return new F(function(){return _bL(_p8,_p5,B(_oY(_oZ,_p0,_p1,_p2,_p6)),_p7);});}}}else{return new F(function(){return _bL(_p8,_p5,B(_oY(_oZ,_p0,_p1,_p2,_p6)),_p7);});}}else{return new T5(0,1,E(new T3(0,_oZ,_p0,_p1)),_p2,E(_bG),E(_bG));}},_pc=function(_pd,_pe,_pf,_pg,_ph){var _pi=E(_ph);if(!_pi._){var _pj=_pi.c,_pk=_pi.d,_pl=_pi.e,_pm=E(_pi.b),_pn=E(_pm.a);if(_pd>=_pn){if(_pd!=_pn){return new F(function(){return _cs(_pm,_pj,_pk,B(_pc(_pd,_pe,_pf,_pg,_pl)));});}else{var _po=E(_pm.b);if(_pe>=_po){if(_pe!=_po){return new F(function(){return _cs(_pm,_pj,_pk,B(_pc(_pd,_pe,_pf,_pg,_pl)));});}else{var _pp=E(_pf),_pq=E(_pm.c);if(_pp>=_pq){if(_pp!=_pq){return new F(function(){return _cs(_pm,_pj,_pk,B(_oY(_pd,_pe,_pp,_pg,_pl)));});}else{return new T5(0,_pi.a,E(new T3(0,_pd,_pe,_pp)),_pg,E(_pk),E(_pl));}}else{return new F(function(){return _bL(_pm,_pj,B(_oY(_pd,_pe,_pp,_pg,_pk)),_pl);});}}}else{return new F(function(){return _bL(_pm,_pj,B(_pc(_pd,_pe,_pf,_pg,_pk)),_pl);});}}}else{return new F(function(){return _bL(_pm,_pj,B(_pc(_pd,_pe,_pf,_pg,_pk)),_pl);});}}else{return new T5(0,1,E(new T3(0,_pd,_pe,_pf)),_pg,E(_bG),E(_bG));}},_pr=function(_ps,_pt,_pu,_pv,_pw){var _px=E(_pw);if(!_px._){var _py=_px.c,_pz=_px.d,_pA=_px.e,_pB=E(_px.b),_pC=E(_pB.a);if(_ps>=_pC){if(_ps!=_pC){return new F(function(){return _cs(_pB,_py,_pz,B(_pr(_ps,_pt,_pu,_pv,_pA)));});}else{var _pD=E(_pt),_pE=E(_pB.b);if(_pD>=_pE){if(_pD!=_pE){return new F(function(){return _cs(_pB,_py,_pz,B(_pc(_ps,_pD,_pu,_pv,_pA)));});}else{var _pF=E(_pu),_pG=E(_pB.c);if(_pF>=_pG){if(_pF!=_pG){return new F(function(){return _cs(_pB,_py,_pz,B(_oY(_ps,_pD,_pF,_pv,_pA)));});}else{return new T5(0,_px.a,E(new T3(0,_ps,_pD,_pF)),_pv,E(_pz),E(_pA));}}else{return new F(function(){return _bL(_pB,_py,B(_oY(_ps,_pD,_pF,_pv,_pz)),_pA);});}}}else{return new F(function(){return _bL(_pB,_py,B(_pc(_ps,_pD,_pu,_pv,_pz)),_pA);});}}}else{return new F(function(){return _bL(_pB,_py,B(_pr(_ps,_pt,_pu,_pv,_pz)),_pA);});}}else{return new T5(0,1,E(new T3(0,_ps,_pt,_pu)),_pv,E(_bG),E(_bG));}},_pH=function(_pI,_pJ,_pK,_pL,_pM){var _pN=E(_pM);if(!_pN._){var _pO=_pN.c,_pP=_pN.d,_pQ=_pN.e,_pR=E(_pN.b),_pS=E(_pI),_pT=E(_pR.a);if(_pS>=_pT){if(_pS!=_pT){return new F(function(){return _cs(_pR,_pO,_pP,B(_pr(_pS,_pJ,_pK,_pL,_pQ)));});}else{var _pU=E(_pJ),_pV=E(_pR.b);if(_pU>=_pV){if(_pU!=_pV){return new F(function(){return _cs(_pR,_pO,_pP,B(_pc(_pS,_pU,_pK,_pL,_pQ)));});}else{var _pW=E(_pK),_pX=E(_pR.c);if(_pW>=_pX){if(_pW!=_pX){return new F(function(){return _cs(_pR,_pO,_pP,B(_oY(_pS,_pU,_pW,_pL,_pQ)));});}else{return new T5(0,_pN.a,E(new T3(0,_pS,_pU,_pW)),_pL,E(_pP),E(_pQ));}}else{return new F(function(){return _bL(_pR,_pO,B(_oY(_pS,_pU,_pW,_pL,_pP)),_pQ);});}}}else{return new F(function(){return _bL(_pR,_pO,B(_pc(_pS,_pU,_pK,_pL,_pP)),_pQ);});}}}else{return new F(function(){return _bL(_pR,_pO,B(_pr(_pS,_pJ,_pK,_pL,_pP)),_pQ);});}}else{return new T5(0,1,E(new T3(0,_pI,_pJ,_pK)),_pL,E(_bG),E(_bG));}},_pY=function(_pZ,_q0){while(1){var _q1=E(_q0);if(!_q1._){return E(_pZ);}else{var _q2=E(_q1.a),_q3=E(_q2.a),_q4=B(_pH(_q3.a,_q3.b,_q3.c,_q2.b,_pZ));_pZ=_q4;_q0=_q1.b;continue;}}},_q5=function(_q6,_q7,_q8,_q9,_qa,_qb){return new F(function(){return _pY(B(_pH(_q7,_q8,_q9,_qa,_q6)),_qb);});},_qc=function(_qd,_qe,_qf){var _qg=E(_qe),_qh=E(_qg.a);return new F(function(){return _pY(B(_pH(_qh.a,_qh.b,_qh.c,_qg.b,_qd)),_qf);});},_qi=function(_qj,_qk,_ql){var _qm=E(_ql);if(!_qm._){return E(_qk);}else{var _qn=E(_qm.a),_qo=_qn.a,_qp=_qn.b,_qq=E(_qm.b);if(!_qq._){return new F(function(){return _mb(_qo,_qp,_qk);});}else{var _qr=E(_qq.a),_qs=E(_qo),_qt=_qs.b,_qu=_qs.c,_qv=E(_qs.a),_qw=E(_qr.a),_qx=_qw.b,_qy=_qw.c,_qz=E(_qw.a),_qA=function(_qB){var _qC=B(_nO(_qj,_qz,_qx,_qy,_qr.b,_qq.b)),_qD=_qC.a,_qE=E(_qC.c);if(!_qE._){return new F(function(){return _qi(_qj<<1,B(_mX(_qs,_qp,_qk,_qD)),_qC.b);});}else{return new F(function(){return _qc(B(_mX(_qs,_qp,_qk,_qD)),_qE.a,_qE.b);});}};if(_qv>=_qz){if(_qv!=_qz){return new F(function(){return _q5(_qk,_qv,_qt,_qu,_qp,_qq);});}else{var _qF=E(_qt),_qG=E(_qx);if(_qF>=_qG){if(_qF!=_qG){return new F(function(){return _q5(_qk,_qv,_qF,_qu,_qp,_qq);});}else{var _qH=E(_qu);if(_qH<E(_qy)){return new F(function(){return _qA(_);});}else{return new F(function(){return _q5(_qk,_qv,_qF,_qH,_qp,_qq);});}}}else{return new F(function(){return _qA(_);});}}}else{return new F(function(){return _qA(_);});}}}},_qI=function(_qJ,_qK,_qL,_qM,_qN,_qO,_qP){var _qQ=E(_qP);if(!_qQ._){return new F(function(){return _mb(new T3(0,_qL,_qM,_qN),_qO,_qK);});}else{var _qR=E(_qQ.a),_qS=E(_qR.a),_qT=_qS.b,_qU=_qS.c,_qV=E(_qS.a),_qW=function(_qX){var _qY=B(_nO(_qJ,_qV,_qT,_qU,_qR.b,_qQ.b)),_qZ=_qY.a,_r0=E(_qY.c);if(!_r0._){return new F(function(){return _qi(_qJ<<1,B(_mX(new T3(0,_qL,_qM,_qN),_qO,_qK,_qZ)),_qY.b);});}else{return new F(function(){return _qc(B(_mX(new T3(0,_qL,_qM,_qN),_qO,_qK,_qZ)),_r0.a,_r0.b);});}};if(_qL>=_qV){if(_qL!=_qV){return new F(function(){return _q5(_qK,_qL,_qM,_qN,_qO,_qQ);});}else{var _r1=E(_qT);if(_qM>=_r1){if(_qM!=_r1){return new F(function(){return _q5(_qK,_qL,_qM,_qN,_qO,_qQ);});}else{var _r2=E(_qN);if(_r2<E(_qU)){return new F(function(){return _qW(_);});}else{return new F(function(){return _q5(_qK,_qL,_qM,_r2,_qO,_qQ);});}}}else{return new F(function(){return _qW(_);});}}}else{return new F(function(){return _qW(_);});}}},_r3=function(_r4,_r5,_r6,_r7,_r8,_r9,_ra){var _rb=E(_ra);if(!_rb._){return new F(function(){return _mb(new T3(0,_r6,_r7,_r8),_r9,_r5);});}else{var _rc=E(_rb.a),_rd=E(_rc.a),_re=_rd.b,_rf=_rd.c,_rg=E(_rd.a),_rh=function(_ri){var _rj=B(_nO(_r4,_rg,_re,_rf,_rc.b,_rb.b)),_rk=_rj.a,_rl=E(_rj.c);if(!_rl._){return new F(function(){return _qi(_r4<<1,B(_mX(new T3(0,_r6,_r7,_r8),_r9,_r5,_rk)),_rj.b);});}else{return new F(function(){return _qc(B(_mX(new T3(0,_r6,_r7,_r8),_r9,_r5,_rk)),_rl.a,_rl.b);});}};if(_r6>=_rg){if(_r6!=_rg){return new F(function(){return _q5(_r5,_r6,_r7,_r8,_r9,_rb);});}else{var _rm=E(_r7),_rn=E(_re);if(_rm>=_rn){if(_rm!=_rn){return new F(function(){return _q5(_r5,_r6,_rm,_r8,_r9,_rb);});}else{var _ro=E(_r8);if(_ro<E(_rf)){return new F(function(){return _rh(_);});}else{return new F(function(){return _q5(_r5,_r6,_rm,_ro,_r9,_rb);});}}}else{return new F(function(){return _rh(_);});}}}else{return new F(function(){return _rh(_);});}}},_rp=function(_rq,_rr,_rs,_rt,_ru,_rv,_rw){var _rx=E(_rw);if(!_rx._){return new F(function(){return _mb(new T3(0,_rs,_rt,_ru),_rv,_rr);});}else{var _ry=E(_rx.a),_rz=E(_ry.a),_rA=_rz.b,_rB=_rz.c,_rC=E(_rz.a),_rD=function(_rE){var _rF=B(_nO(_rq,_rC,_rA,_rB,_ry.b,_rx.b)),_rG=_rF.a,_rH=E(_rF.c);if(!_rH._){return new F(function(){return _qi(_rq<<1,B(_mX(new T3(0,_rs,_rt,_ru),_rv,_rr,_rG)),_rF.b);});}else{return new F(function(){return _qc(B(_mX(new T3(0,_rs,_rt,_ru),_rv,_rr,_rG)),_rH.a,_rH.b);});}};if(_rs>=_rC){if(_rs!=_rC){return new F(function(){return _q5(_rr,_rs,_rt,_ru,_rv,_rx);});}else{var _rI=E(_rA);if(_rt>=_rI){if(_rt!=_rI){return new F(function(){return _q5(_rr,_rs,_rt,_ru,_rv,_rx);});}else{if(_ru<E(_rB)){return new F(function(){return _rD(_);});}else{return new F(function(){return _q5(_rr,_rs,_rt,_ru,_rv,_rx);});}}}else{return new F(function(){return _rD(_);});}}}else{return new F(function(){return _rD(_);});}}},_rJ=function(_rK){var _rL=E(_rK);if(!_rL._){return new T0(1);}else{var _rM=E(_rL.a),_rN=_rM.a,_rO=_rM.b,_rP=E(_rL.b);if(!_rP._){return new T5(0,1,E(_rN),_rO,E(_bG),E(_bG));}else{var _rQ=_rP.b,_rR=E(_rP.a),_rS=_rR.b,_rT=E(_rN),_rU=E(_rT.a),_rV=E(_rR.a),_rW=_rV.b,_rX=_rV.c,_rY=E(_rV.a);if(_rU>=_rY){if(_rU!=_rY){return new F(function(){return _q5(new T5(0,1,E(_rT),_rO,E(_bG),E(_bG)),_rY,_rW,_rX,_rS,_rQ);});}else{var _rZ=E(_rT.b),_s0=E(_rW);if(_rZ>=_s0){if(_rZ!=_s0){return new F(function(){return _q5(new T5(0,1,E(_rT),_rO,E(_bG),E(_bG)),_rY,_s0,_rX,_rS,_rQ);});}else{var _s1=E(_rX);if(E(_rT.c)<_s1){return new F(function(){return _rp(1,new T5(0,1,E(_rT),_rO,E(_bG),E(_bG)),_rY,_s0,_s1,_rS,_rQ);});}else{return new F(function(){return _q5(new T5(0,1,E(_rT),_rO,E(_bG),E(_bG)),_rY,_s0,_s1,_rS,_rQ);});}}}else{return new F(function(){return _qI(1,new T5(0,1,E(_rT),_rO,E(_bG),E(_bG)),_rY,_s0,_rX,_rS,_rQ);});}}}else{return new F(function(){return _r3(1,new T5(0,1,E(_rT),_rO,E(_bG),E(_bG)),_rY,_rW,_rX,_rS,_rQ);});}}}},_s2=function(_s3,_s4){var _s5=function(_s6,_s7){while(1){var _s8=B((function(_s9,_sa){var _sb=E(_sa);if(!_sb._){_s6=new T2(1,new T2(0,new T(function(){return B(A1(_s3,_sb.b));}),_sb.c),new T(function(){return B(_s5(_s9,_sb.e));}));_s7=_sb.d;return __continue;}else{return E(_s9);}})(_s6,_s7));if(_s8!=__continue){return _s8;}}};return new F(function(){return _rJ(B(_s5(_z,_s4)));});},_sc=__Z,_sd=function(_se){return new T3(0,new T(function(){return E(E(_se).a)+1|0;}),new T(function(){return B(_hF(_se));}),new T(function(){return B(_hC(_se));}));},_sf=function(_sg,_sh,_si,_sj,_sk,_sl){var _sm=E(_sg);if(!_sm._){var _sn=_sm.a,_so=_sm.b,_sp=_sm.c,_sq=_sm.d,_sr=_sm.e;if((imul(3,_sn)|0)>=_sh){if((imul(3,_sh)|0)>=_sn){return new F(function(){return _dp(_sm,new T5(0,_sh,E(_si),_sj,E(_sk),E(_sl)));});}else{return new F(function(){return _cs(_so,_sp,_sq,B(_sf(_sr,_sh,_si,_sj,_sk,_sl)));});}}else{return new F(function(){return _bL(_si,_sj,B(_ss(_sn,_so,_sp,_sq,_sr,_sk)),_sl);});}}else{return new T5(0,_sh,E(_si),_sj,E(_sk),E(_sl));}},_ss=function(_st,_su,_sv,_sw,_sx,_sy){var _sz=E(_sy);if(!_sz._){var _sA=_sz.a,_sB=_sz.b,_sC=_sz.c,_sD=_sz.d,_sE=_sz.e;if((imul(3,_st)|0)>=_sA){if((imul(3,_sA)|0)>=_st){return new F(function(){return _dp(new T5(0,_st,E(_su),_sv,E(_sw),E(_sx)),_sz);});}else{return new F(function(){return _cs(_su,_sv,_sw,B(_sf(_sx,_sA,_sB,_sC,_sD,_sE)));});}}else{return new F(function(){return _bL(_sB,_sC,B(_ss(_st,_su,_sv,_sw,_sx,_sD)),_sE);});}}else{return new T5(0,_st,E(_su),_sv,E(_sw),E(_sx));}},_sF=function(_sG,_sH){var _sI=E(_sG);if(!_sI._){var _sJ=_sI.a,_sK=_sI.b,_sL=_sI.c,_sM=_sI.d,_sN=_sI.e,_sO=E(_sH);if(!_sO._){var _sP=_sO.a,_sQ=_sO.b,_sR=_sO.c,_sS=_sO.d,_sT=_sO.e;if((imul(3,_sJ)|0)>=_sP){if((imul(3,_sP)|0)>=_sJ){return new F(function(){return _dp(_sI,_sO);});}else{return new F(function(){return _cs(_sK,_sL,_sM,B(_sf(_sN,_sP,_sQ,_sR,_sS,_sT)));});}}else{return new F(function(){return _bL(_sQ,_sR,B(_ss(_sJ,_sK,_sL,_sM,_sN,_sS)),_sT);});}}else{return E(_sI);}}else{return E(_sH);}},_sU=function(_sV,_sW){var _sX=E(_sW);if(!_sX._){var _sY=_sX.b,_sZ=_sX.c,_t0=_sX.d,_t1=_sX.e;if(!B(A2(_sV,_sY,_sZ))){return new F(function(){return _sF(B(_sU(_sV,_t0)),B(_sU(_sV,_t1)));});}else{return new F(function(){return _mX(_sY,_sZ,B(_sU(_sV,_t0)),B(_sU(_sV,_t1)));});}}else{return new T0(1);}},_t2=function(_t3){return E(E(_t3).a);},_t4=function(_t5){return E(E(_t5).b);},_t6=function(_t7,_t8){return new T5(0,new T(function(){return B(_t2(_t8));}),new T(function(){return B(_t4(_t8));}),_il,_2u,new T1(1,_t7));},_t9=function(_ta,_tb){return new T5(0,new T(function(){return B(_t2(_tb));}),new T(function(){return B(_t4(_tb));}),_il,new T1(1,new T(function(){return B(_sd(_ta));})),new T(function(){return B(_fj(_tb));}));},_tc=function(_td,_te){return (E(E(_te).d)._==0)?true:false;},_tf=function(_tg,_th){var _ti=E(_th);if(!_ti._){var _tj=_ti.b;return new T5(0,_ti.a,E(_tj),new T(function(){return B(A2(_tg,_tj,_ti.c));}),E(B(_tf(_tg,_ti.d))),E(B(_tf(_tg,_ti.e))));}else{return new T0(1);}},_tk=function(_tl){return E(E(_tl).b);},_tm=function(_tn,_to,_tp){var _tq=E(_to);if(!_tq._){return E(_tp);}else{var _tr=function(_ts,_tt){while(1){var _tu=E(_tt);if(!_tu._){var _tv=_tu.b,_tw=_tu.e;switch(B(A3(_tk,_tn,_ts,_tv))){case 0:return new F(function(){return _mX(_tv,_tu.c,B(_tr(_ts,_tu.d)),_tw);});break;case 1:return E(_tw);default:_tt=_tw;continue;}}else{return new T0(1);}}};return new F(function(){return _tr(_tq.a,_tp);});}},_tx=function(_ty,_tz,_tA){var _tB=E(_tz);if(!_tB._){return E(_tA);}else{var _tC=function(_tD,_tE){while(1){var _tF=E(_tE);if(!_tF._){var _tG=_tF.b,_tH=_tF.d;switch(B(A3(_tk,_ty,_tG,_tD))){case 0:return new F(function(){return _mX(_tG,_tF.c,_tH,B(_tC(_tD,_tF.e)));});break;case 1:return E(_tH);default:_tE=_tH;continue;}}else{return new T0(1);}}};return new F(function(){return _tC(_tB.a,_tA);});}},_tI=function(_tJ,_tK,_tL,_tM){var _tN=E(_tK),_tO=E(_tM);if(!_tO._){var _tP=_tO.b,_tQ=_tO.c,_tR=_tO.d,_tS=_tO.e;switch(B(A3(_tk,_tJ,_tN,_tP))){case 0:return new F(function(){return _bL(_tP,_tQ,B(_tI(_tJ,_tN,_tL,_tR)),_tS);});break;case 1:return E(_tO);default:return new F(function(){return _cs(_tP,_tQ,_tR,B(_tI(_tJ,_tN,_tL,_tS)));});}}else{return new T5(0,1,E(_tN),_tL,E(_bG),E(_bG));}},_tT=function(_tU,_tV,_tW,_tX){return new F(function(){return _tI(_tU,_tV,_tW,_tX);});},_tY=function(_tZ){return E(E(_tZ).d);},_u0=function(_u1){return E(E(_u1).f);},_u2=function(_u3,_u4,_u5,_u6){var _u7=E(_u4);if(!_u7._){var _u8=E(_u5);if(!_u8._){return E(_u6);}else{var _u9=function(_ua,_ub){while(1){var _uc=E(_ub);if(!_uc._){if(!B(A3(_u0,_u3,_uc.b,_ua))){return E(_uc);}else{_ub=_uc.d;continue;}}else{return new T0(1);}}};return new F(function(){return _u9(_u8.a,_u6);});}}else{var _ud=_u7.a,_ue=E(_u5);if(!_ue._){var _uf=function(_ug,_uh){while(1){var _ui=E(_uh);if(!_ui._){if(!B(A3(_tY,_u3,_ui.b,_ug))){return E(_ui);}else{_uh=_ui.e;continue;}}else{return new T0(1);}}};return new F(function(){return _uf(_ud,_u6);});}else{var _uj=function(_uk,_ul,_um){while(1){var _un=E(_um);if(!_un._){var _uo=_un.b;if(!B(A3(_tY,_u3,_uo,_uk))){if(!B(A3(_u0,_u3,_uo,_ul))){return E(_un);}else{_um=_un.d;continue;}}else{_um=_un.e;continue;}}else{return new T0(1);}}};return new F(function(){return _uj(_ud,_ue.a,_u6);});}}},_up=function(_uq,_ur,_us,_ut,_uu){var _uv=E(_uu);if(!_uv._){var _uw=_uv.b,_ux=_uv.c,_uy=_uv.d,_uz=_uv.e,_uA=E(_ut);if(!_uA._){var _uB=_uA.b,_uC=function(_uD){var _uE=new T1(1,E(_uB));return new F(function(){return _mX(_uB,_uA.c,B(_up(_uq,_ur,_uE,_uA.d,B(_u2(_uq,_ur,_uE,_uv)))),B(_up(_uq,_uE,_us,_uA.e,B(_u2(_uq,_uE,_us,_uv)))));});};if(!E(_uy)._){return new F(function(){return _uC(_);});}else{if(!E(_uz)._){return new F(function(){return _uC(_);});}else{return new F(function(){return _tT(_uq,_uw,_ux,_uA);});}}}else{return new F(function(){return _mX(_uw,_ux,B(_tm(_uq,_ur,_uy)),B(_tx(_uq,_us,_uz)));});}}else{return E(_ut);}},_uF=function(_uG,_uH,_uI,_uJ,_uK,_uL,_uM,_uN,_uO,_uP,_uQ,_uR,_uS){var _uT=function(_uU){var _uV=new T1(1,E(_uK));return new F(function(){return _mX(_uK,_uL,B(_up(_uG,_uH,_uV,_uM,B(_u2(_uG,_uH,_uV,new T5(0,_uO,E(_uP),_uQ,E(_uR),E(_uS)))))),B(_up(_uG,_uV,_uI,_uN,B(_u2(_uG,_uV,_uI,new T5(0,_uO,E(_uP),_uQ,E(_uR),E(_uS)))))));});};if(!E(_uR)._){return new F(function(){return _uT(_);});}else{if(!E(_uS)._){return new F(function(){return _uT(_);});}else{return new F(function(){return _tT(_uG,_uP,_uQ,new T5(0,_uJ,E(_uK),_uL,E(_uM),E(_uN)));});}}},_uW=function(_uX){var _uY=B(_sU(_tc,_uX)),_uZ=function(_v0,_v1,_v2,_v3,_v4,_v5){var _v6=E(_uX);if(!_v6._){return new F(function(){return _uF(_m7,_sc,_sc,_v0,_v1,_v2,_v3,_v4,_v6.a,_v6.b,_v6.c,_v6.d,_v6.e);});}else{return E(_v5);}},_v7=B(_s2(_sd,B(_tf(_t6,_uY))));if(!_v7._){var _v8=_v7.a,_v9=_v7.b,_va=_v7.c,_vb=_v7.d,_vc=_v7.e,_vd=B(_tf(_t9,_uY));if(!_vd._){var _ve=B(_uF(_m7,_sc,_sc,_v8,_v9,_va,_vb,_vc,_vd.a,_vd.b,_vd.c,_vd.d,_vd.e));if(!_ve._){return new F(function(){return _uZ(_ve.a,_ve.b,_ve.c,_ve.d,_ve.e,_ve);});}else{return E(_uX);}}else{return new F(function(){return _uZ(_v8,_v9,_va,_vb,_vc,_v7);});}}else{var _vf=B(_tf(_t9,_uY));if(!_vf._){return new F(function(){return _uZ(_vf.a,_vf.b,_vf.c,_vf.d,_vf.e,_vf);});}else{return E(_uX);}}},_vg=function(_vh,_vi){while(1){var _vj=E(_vh);if(!_vj._){return (E(_vi)._==0)?true:false;}else{var _vk=E(_vi);if(!_vk._){return false;}else{if(E(_vj.a)!=E(_vk.a)){return false;}else{_vh=_vj.b;_vi=_vk.b;continue;}}}}},_vl=new T2(1,_hC,_z),_vm=new T2(1,_hF,_vl),_vn=new T2(1,_hI,_vm),_vo=new T2(1,_z,_z),_vp=function(_vq,_vr){var _vs=function(_vt,_vu){var _vv=E(_vt);if(!_vv._){return E(_vu);}else{var _vw=_vv.a,_vx=E(_vu);if(!_vx._){return E(_vv);}else{var _vy=_vx.a;return (B(A2(_vq,_vw,_vy))==2)?new T2(1,_vy,new T(function(){return B(_vs(_vv,_vx.b));})):new T2(1,_vw,new T(function(){return B(_vs(_vv.b,_vx));}));}}},_vz=function(_vA){var _vB=E(_vA);if(!_vB._){return __Z;}else{var _vC=E(_vB.b);return (_vC._==0)?E(_vB):new T2(1,new T(function(){return B(_vs(_vB.a,_vC.a));}),new T(function(){return B(_vz(_vC.b));}));}},_vD=new T(function(){return B(_vE(B(_vz(_z))));}),_vE=function(_vF){while(1){var _vG=E(_vF);if(!_vG._){return E(_vD);}else{if(!E(_vG.b)._){return E(_vG.a);}else{_vF=B(_vz(_vG));continue;}}}},_vH=new T(function(){return B(_vI(_z));}),_vJ=function(_vK,_vL,_vM){while(1){var _vN=B((function(_vO,_vP,_vQ){var _vR=E(_vQ);if(!_vR._){return new T2(1,new T2(1,_vO,_vP),_vH);}else{var _vS=_vR.a;if(B(A2(_vq,_vO,_vS))==2){var _vT=new T2(1,_vO,_vP);_vK=_vS;_vL=_vT;_vM=_vR.b;return __continue;}else{return new T2(1,new T2(1,_vO,_vP),new T(function(){return B(_vI(_vR));}));}}})(_vK,_vL,_vM));if(_vN!=__continue){return _vN;}}},_vU=function(_vV,_vW,_vX){while(1){var _vY=B((function(_vZ,_w0,_w1){var _w2=E(_w1);if(!_w2._){return new T2(1,new T(function(){return B(A1(_w0,new T2(1,_vZ,_z)));}),_vH);}else{var _w3=_w2.a,_w4=_w2.b;switch(B(A2(_vq,_vZ,_w3))){case 0:_vV=_w3;_vW=function(_w5){return new F(function(){return A1(_w0,new T2(1,_vZ,_w5));});};_vX=_w4;return __continue;case 1:_vV=_w3;_vW=function(_w6){return new F(function(){return A1(_w0,new T2(1,_vZ,_w6));});};_vX=_w4;return __continue;default:return new T2(1,new T(function(){return B(A1(_w0,new T2(1,_vZ,_z)));}),new T(function(){return B(_vI(_w2));}));}}})(_vV,_vW,_vX));if(_vY!=__continue){return _vY;}}},_vI=function(_w7){var _w8=E(_w7);if(!_w8._){return E(_vo);}else{var _w9=_w8.a,_wa=E(_w8.b);if(!_wa._){return new T2(1,_w8,_z);}else{var _wb=_wa.a,_wc=_wa.b;if(B(A2(_vq,_w9,_wb))==2){return new F(function(){return _vJ(_wb,new T2(1,_w9,_z),_wc);});}else{return new F(function(){return _vU(_wb,function(_wd){return new T2(1,_w9,_wd);},_wc);});}}}};return new F(function(){return _vE(B(_vI(_vr)));});},_we=function(_wf,_wg,_wh,_wi,_wj){if(!B(_vg(B(_vp(_65,B(_4j(function(_wk){var _wl=B(A1(_wk,_wi))-B(A1(_wk,_wh))|0;return (_wl<0)? -_wl:_wl;},_vn)))),_wf))){return __Z;}else{var _wm=E(_wg);if(!_wm._){return __Z;}else{var _wn=_wm.a,_wo=new T(function(){var _wp=E(_wh),_wq=E(_wi),_wr=new T(function(){return E(E(_wn).a);}),_ws=new T(function(){return E(E(_wn).b);});return B(_gb(_wp.a,_wp.b,_wp.c,new T5(0,_wr,_ws,_il,new T1(1,_wq),new T(function(){return E(E(_wn).e);})),B(_gb(_wq.a,_wq.b,_wq.c,new T5(0,_wr,_ws,_il,_2u,new T1(1,_wp)),_wj))));});return new T1(1,_wo);}}},_wt=function(_wu){return (E(_wu)==0)?1:0;},_wv=1,_ww=new T1(1,_wv),_wx=2,_wy=new T2(1,_wx,_z),_wz=new T2(1,_wv,_wy),_wA=0,_wB=new T2(1,_wA,_wz),_wC=new T1(0,_il),_wD=function(_wE,_wF,_wG,_wH,_wI){var _wJ=E(_wH);if(!_wJ._){return __Z;}else{var _wK=E(_wE),_wL=_wK.a,_wM=_wK.b,_wN=_wK.c,_wO=B(_ka(_wL,_wM,_wN,_wI));if(!_wO._){var _wP=false;}else{var _wP=E(E(_wO.a).c);}var _wQ=function(_wR){var _wS=E(_wJ.a),_wT=B(_ka(_wS.a,_wS.b,_wS.c,_wI));if(!_wT._){return __Z;}else{var _wU=E(_wT.a),_wV=function(_wW){return new T1(1,new T4(0,new T(function(){return E(_wF)+1|0;}),new T(function(){return B(_wt(_wG));}),_2u,new T(function(){return B(_uW(_wW));})));},_wX=E(_wU.b);switch(_wX._){case 0:var _wY=B(_j5(new T(function(){if(!E(_wP)){return true;}else{return false;}},1),_wP,new T1(1,new T(function(){if(!E(_wX.a)){if(!E(_wP)){return E(_wx);}else{return E(_wv);}}else{return E(_wv);}})),new T1(1,new T5(0,_wU.a,_wC,_ik,_2u,_2u)),_wS,_wK,new T(function(){return B(_fl(_wL,_wM,_wN,_wI));})));if(!_wY._){return __Z;}else{return new F(function(){return _wV(_wY.a);});}break;case 1:var _wZ=B(_j5(_il,_ik,_2u,_wT,_wS,_wK,new T(function(){return B(_fl(_wL,_wM,_wN,_wI));})));if(!_wZ._){return __Z;}else{return new F(function(){return _wV(_wZ.a);});}break;case 2:var _x0=B(_we(_wB,_wT,_wS,_wK,new T(function(){return B(_fl(_wL,_wM,_wN,_wI));},1)));if(!_x0._){return __Z;}else{return new F(function(){return _wV(_x0.a);});}break;case 3:var _x1=B(_j5(_ik,_il,_2u,_wT,_wS,_wK,new T(function(){return B(_fl(_wL,_wM,_wN,_wI));})));if(!_x1._){return __Z;}else{return new F(function(){return _wV(_x1.a);});}break;case 4:var _x2=B(_j5(_il,_il,_2u,_wT,_wS,_wK,new T(function(){return B(_fl(_wL,_wM,_wN,_wI));})));if(!_x2._){return __Z;}else{return new F(function(){return _wV(_x2.a);});}break;default:var _x3=B(_j5(_il,_il,_ww,_wT,_wS,_wK,new T(function(){return B(_fl(_wL,_wM,_wN,_wI));})));if(!_x3._){return __Z;}else{return new F(function(){return _wV(_x3.a);});}}}};if(!E(_wP)){return new F(function(){return _wQ(_);});}else{var _x4=B(_5g(_wL,_wM,_wN,_wI));if(!_x4._){return new F(function(){return _wQ(_);});}else{if(!E(E(_x4.a).a)){if(!E(_wG)){return __Z;}else{return new F(function(){return _wQ(_);});}}else{if(!E(_wG)){return new F(function(){return _wQ(_);});}else{return __Z;}}}}}},_x5=function(_x6){return E(E(_x6).a);},_x7=function(_x8){return E(E(_x8).a);},_x9=function(_xa){return E(E(_xa).b);},_xb=function(_xc){return E(E(_xc).a);},_xd=function(_){return new F(function(){return nMV(_2u);});},_xe=new T(function(){return B(_2N(_xd));}),_xf=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_xg=function(_xh){return E(E(_xh).b);},_xi=function(_xj,_xk,_xl,_xm,_xn,_xo){var _xp=B(_x5(_xj)),_xq=B(_6p(_xp)),_xr=new T(function(){return B(_7w(_xp));}),_xs=new T(function(){return B(_8c(_xq));}),_xt=new T(function(){return B(A2(_x7,_xk,_xm));}),_xu=new T(function(){return B(A2(_xb,_xl,_xn));}),_xv=function(_xw){return new F(function(){return A1(_xs,new T3(0,_xu,_xt,_xw));});},_xx=function(_xy){var _xz=new T(function(){var _xA=new T(function(){var _xB=__createJSFunc(2,function(_xC,_){var _xD=B(A2(E(_xy),_xC,_));return _2R;}),_xE=_xB;return function(_){return new F(function(){return __app3(E(_xf),E(_xt),E(_xu),_xE);});};});return B(A1(_xr,_xA));});return new F(function(){return A3(_77,_xq,_xz,_xv);});},_xF=new T(function(){var _xG=new T(function(){return B(_7w(_xp));}),_xH=function(_xI){var _xJ=new T(function(){return B(A1(_xG,function(_){var _=wMV(E(_xe),new T1(1,_xI));return new F(function(){return A(_x9,[_xl,_xn,_xI,_]);});}));});return new F(function(){return A3(_77,_xq,_xJ,_xo);});};return B(A2(_xg,_xj,_xH));});return new F(function(){return A3(_77,_xq,_xF,_xx);});},_xK=new T(function(){return eval("(function(e,ch){while(e.firstChild) {e.removeChild(e.firstChild);}for(var i in ch) {e.appendChild(ch[i]);}})");}),_xL=function(_xM){return E(_xM);},_xN=function(_xO,_xP,_xQ,_xR,_xS){var _xT=new T(function(){var _xU=__lst2arr(B(_4j(_xL,B(_4j(new T(function(){return B(_x7(_xP));}),_xS))))),_xV=_xU;return function(_){var _xW=__app2(E(_xK),B(A2(_x7,_xO,_xR)),_xV);return new F(function(){return _5K(_);});};});return new F(function(){return A2(_7w,_xQ,_xT);});},_xX=function(_xY,_xZ,_y0,_y1,_y2,_y3,_y4,_){var _y5=B(A1(_aL,_)),_y6=E(_y5);if(!_y6._){return new F(function(){return die(_aC);});}else{var _y7=B(A(_4s,[_xY,_xZ,_y0,_y1,new T4(0,_y2,_y3,_2u,_y4)])),_y8=B(A(_8p,[_45,_y7.a,_y7.b,_y7.c,_y7.d,_y7.e,_])),_y9=function(_ya){while(1){var _yb=B((function(_yc){var _yd=E(_yc);if(!_yd._){return __Z;}else{var _ye=_yd.b,_yf=E(_yd.a);if(!_yf._){var _yg=new T(function(){var _yh=new T(function(){var _yi=B(_5B(_yf.a,new T4(0,_y2,_y3,_2u,_y4)));return new T4(0,_yi.a,_yi.b,_yi.c,_yi.d);});return B(_xi(_46,_3n,_3i,_yf.b,_am,function(_yj,_){return new F(function(){return _yk(_xY,_xZ,_y0,_y1,_yh,_);});}));});return new T2(1,_yg,new T(function(){return B(_y9(_ye));}));}else{_ya=_ye;return __continue;}}})(_ya));if(_yb!=__continue){return _yb;}}},_yl=B(_y9(_y8));if(!_yl._){return E(_ap);}else{var _ym=B(_at(_yl.b,_yl.a,_)),_yn=B(A(_xN,[_3n,_3n,_45,_y6.a,new T(function(){return B(_4j(_aq,_y8));},1),_]));return _0;}}},_yk=function(_yo,_yp,_yq,_yr,_ys,_){var _yt=B(A1(_aL,_)),_yu=E(_yt);if(!_yu._){return new F(function(){return die(_aC);});}else{var _yv=B(A(_4s,[_yo,_yp,_yq,_yr,_ys])),_yw=B(A(_8p,[_45,_yv.a,_yv.b,_yv.c,_yv.d,_yv.e,_])),_yx=new T(function(){return E(E(_ys).a);}),_yy=new T(function(){return E(E(_ys).b);}),_yz=new T(function(){return E(E(_ys).d);}),_yA=function(_yB,_){return new F(function(){return _xX(_yo,_yp,_yq,_yr,_yx,_yy,_yz,_);});},_yC=function(_yD){while(1){var _yE=B((function(_yF){var _yG=E(_yF);if(!_yG._){return __Z;}else{var _yH=_yG.b,_yI=E(_yG.a);if(!_yI._){var _yJ=_yI.a,_yK=_yI.b,_yL=new T(function(){var _yM=E(_ys),_yN=_yM.a,_yO=E(_yM.c);if(!_yO._){var _yP=new T(function(){var _yQ=B(_5B(_yJ,_yM));return new T4(0,_yQ.a,_yQ.b,_yQ.c,_yQ.d);});return B(_xi(_46,_3n,_3i,_yK,_am,function(_yR,_){return new F(function(){return _yk(_yo,_yp,_yq,_yr,_yP,_);});}));}else{var _yS=E(_yO.a),_yT=E(_yJ),_yU=function(_yV){var _yW=new T(function(){return B(_wD(_yT,_yN,_yM.b,_yO,_yM.d));}),_yX=new T(function(){if(!E(_yW)._){return E(_yp);}else{switch(E(_yo)){case 0:var _yY=E(_yp);if(_yY!=E(_yN)){return E(_yY);}else{var _yZ=E(_yY);if(_yZ==2147483647){return E(_5J);}else{return _yZ+1|0;}}break;case 1:return E(_yp);break;default:return E(_yp);}}}),_z0=new T(function(){var _z1=E(_yW);if(!_z1._){return E(_yM);}else{return E(_z1.a);}});return new F(function(){return _xi(_46,_3n,_3i,_yK,_am,function(_z2,_){return new F(function(){return _yk(_yo,_yX,_yq,_yr,_z0,_);});});});};if(E(_yS.a)!=E(_yT.a)){return B(_yU(_));}else{if(E(_yS.b)!=E(_yT.b)){return B(_yU(_));}else{if(E(_yS.c)!=E(_yT.c)){return B(_yU(_));}else{return B(_xi(_46,_3n,_3i,_yK,_am,_yA));}}}}});return new T2(1,_yL,new T(function(){return B(_yC(_yH));}));}else{_yD=_yH;return __continue;}}})(_yD));if(_yE!=__continue){return _yE;}}},_z3=B(_yC(_yw));if(!_z3._){return E(_ap);}else{var _z4=B(_at(_z3.b,_z3.a,_)),_z5=B(A(_xN,[_3n,_3n,_45,_yu.a,new T(function(){return B(_4j(_aq,_yw));},1),_]));return _0;}}},_z6=function(_z7,_z8,_z9,_za,_){var _zb=B(A1(_aL,_)),_zc=E(_zb);if(!_zc._){return new F(function(){return die(_aC);});}else{var _zd=B(A(_4s,[_an,_z7,_z8,_z9,_za])),_ze=B(A(_8p,[_45,_zd.a,_zd.b,_zd.c,_zd.d,_zd.e,_])),_zf=new T(function(){return E(E(_za).a);}),_zg=new T(function(){return E(E(_za).b);}),_zh=new T(function(){return E(E(_za).d);}),_zi=function(_zj,_){return new F(function(){return _xX(_an,_z7,_z8,_z9,_zf,_zg,_zh,_);});},_zk=function(_zl){while(1){var _zm=B((function(_zn){var _zo=E(_zn);if(!_zo._){return __Z;}else{var _zp=_zo.b,_zq=E(_zo.a);if(!_zq._){var _zr=_zq.a,_zs=_zq.b,_zt=new T(function(){var _zu=E(_za),_zv=_zu.a,_zw=E(_zu.c);if(!_zw._){var _zx=new T(function(){var _zy=B(_5B(_zr,_zu));return new T4(0,_zy.a,_zy.b,_zy.c,_zy.d);});return B(_xi(_46,_3n,_3i,_zs,_am,function(_zz,_){return new F(function(){return _z6(_z7,_z8,_z9,_zx,_);});}));}else{var _zA=E(_zw.a),_zB=E(_zr),_zC=function(_zD){var _zE=new T(function(){return B(_wD(_zB,_zv,_zu.b,_zw,_zu.d));}),_zF=new T(function(){if(!E(_zE)._){return _z7;}else{if(_z7!=E(_zv)){return _z7;}else{var _zG=E(_z7);if(_zG==2147483647){return E(_5J);}else{return _zG+1|0;}}}}),_zH=new T(function(){var _zI=E(_zE);if(!_zI._){return E(_zu);}else{return E(_zI.a);}});return new F(function(){return _xi(_46,_3n,_3i,_zs,_am,function(_zJ,_){return new F(function(){return _yk(_an,_zF,_z8,_z9,_zH,_);});});});};if(E(_zA.a)!=E(_zB.a)){return B(_zC(_));}else{if(E(_zA.b)!=E(_zB.b)){return B(_zC(_));}else{if(E(_zA.c)!=E(_zB.c)){return B(_zC(_));}else{return B(_xi(_46,_3n,_3i,_zs,_am,_zi));}}}}});return new T2(1,_zt,new T(function(){return B(_zk(_zp));}));}else{_zl=_zp;return __continue;}}})(_zl));if(_zm!=__continue){return _zm;}}},_zK=B(_zk(_ze));if(!_zK._){return E(_ap);}else{var _zL=B(_at(_zK.b,_zK.a,_)),_zM=B(A(_xN,[_3n,_3n,_45,_zc.a,new T(function(){return B(_4j(_aq,_ze));},1),_]));return _0;}}},_zN=function(_zO,_zP,_zQ,_zR,_zS,_zT,_){var _zU=B(A1(_aL,_)),_zV=E(_zU);if(!_zV._){return new F(function(){return die(_aC);});}else{var _zW=B(A(_4s,[_an,_zO,_zP,_zQ,new T4(0,_zR,_zS,_2u,_zT)])),_zX=B(A(_8p,[_45,_zW.a,_zW.b,_zW.c,_zW.d,_zW.e,_])),_zY=function(_zZ){while(1){var _A0=B((function(_A1){var _A2=E(_A1);if(!_A2._){return __Z;}else{var _A3=_A2.b,_A4=E(_A2.a);if(!_A4._){var _A5=new T(function(){var _A6=new T(function(){var _A7=B(_5B(_A4.a,new T4(0,_zR,_zS,_2u,_zT)));return new T4(0,_A7.a,_A7.b,_A7.c,_A7.d);});return B(_xi(_46,_3n,_3i,_A4.b,_am,function(_A8,_){return new F(function(){return _z6(_zO,_zP,_zQ,_A6,_);});}));});return new T2(1,_A5,new T(function(){return B(_zY(_A3));}));}else{_zZ=_A3;return __continue;}}})(_zZ));if(_A0!=__continue){return _A0;}}},_A9=B(_zY(_zX));if(!_A9._){return E(_ap);}else{var _Aa=B(_at(_A9.b,_A9.a,_)),_Ab=B(A(_xN,[_3n,_3n,_45,_zV.a,new T(function(){return B(_4j(_aq,_zX));},1),_]));return _0;}}},_Ac=new T0(3),_Ad=new T0(2),_Ae=new T0(4),_Af=3,_Ag=2,_Ah=1,_Ai=6,_Aj=0,_Ak=7,_Al=5,_Am=4,_An=new T1(5,_ik),_Ao=new T1(1,_ik),_Ap=function(_Aq,_Ar){return new T2(0,new T2(0,new T3(0,_Aj,_Aj,_Ar),new T5(0,_Aq,_Ao,_il,_2u,_2u)),new T2(1,new T2(0,new T3(0,_Aj,_Ah,_Ar),new T5(0,_Aq,_Ad,_il,_2u,_2u)),new T2(1,new T2(0,new T3(0,_Aj,_Ag,_Ar),new T5(0,_Aq,_Ac,_il,_2u,_2u)),new T2(1,new T2(0,new T3(0,_Aj,_Af,_Ar),new T5(0,_Aq,_Ae,_il,_2u,_2u)),new T2(1,new T2(0,new T3(0,_Aj,_Am,_Ar),new T5(0,_Aq,_An,_il,_2u,_2u)),new T2(1,new T2(0,new T3(0,_Aj,_Al,_Ar),new T5(0,_Aq,_Ac,_il,_2u,_2u)),new T2(1,new T2(0,new T3(0,_Aj,_Ai,_Ar),new T5(0,_Aq,_Ad,_il,_2u,_2u)),new T2(1,new T2(0,new T3(0,_Aj,_Ak,_Ar),new T5(0,_Aq,_Ao,_il,_2u,_2u)),_z))))))));},_As=new T(function(){return B(_4d(0,7));}),_At=new T1(0,_ik),_Au=function(_Av,_Aw){var _Ax=function(_Ay,_Az){var _AA=E(_Ay);if(!_AA._){return __Z;}else{var _AB=E(_Az);return (_AB._==0)?__Z:new T2(1,new T2(0,new T3(0,_Aj,_AA.a,_Aw),_AB.a),new T(function(){return B(_Ax(_AA.b,_AB.b));}));}},_AC=new T(function(){var _AD=new T(function(){return new T2(1,new T5(0,_Av,_At,_il,_2u,_2u),_AD);});return E(_AD);},1);return new F(function(){return _Ax(_As,_AC);});},_AE=new T(function(){return B(_Au(_1,_Ah));}),_AF=1,_AG=new T(function(){return B(_Au(_AF,_Ai));}),_AH=new T(function(){var _AI=B(_Ap(_AF,_Ak));return B(_7(new T2(1,_AI.a,_AI.b),_AG));}),_AJ=new T(function(){return B(_7(_AE,_AH));}),_AK=new T(function(){var _AL=B(_Ap(_1,_Aj));return B(_rJ(B(_7(new T2(1,_AL.a,_AL.b),_AJ))));}),_AM=function(_){var _AN=B(_zN(0,_2,_3,0,_1,_AK,_));return _0;},_AO=function(_){return new F(function(){return _AM(_);});};
var hasteMain = function() {B(A(_AO, [0]));};window.onload = hasteMain;