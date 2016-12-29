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

var _0=0,_1=0,_2=1,_3=2,_4="deltaZ",_5="deltaY",_6="deltaX",_7=function(_8,_9){var _a=E(_8);return (_a._==0)?E(_9):new T2(1,_a.a,new T(function(){return B(_7(_a.b,_9));}));},_b=function(_c,_d){var _e=jsShowI(_c);return new F(function(){return _7(fromJSStr(_e),_d);});},_f=41,_g=40,_h=function(_i,_j,_k){if(_j>=0){return new F(function(){return _b(_j,_k);});}else{if(_i<=6){return new F(function(){return _b(_j,_k);});}else{return new T2(1,_g,new T(function(){var _l=jsShowI(_j);return B(_7(fromJSStr(_l),new T2(1,_f,_k)));}));}}},_m=new T(function(){return B(unCStr(")"));}),_n=new T(function(){return B(_h(0,2,_m));}),_o=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_n));}),_p=function(_q){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_h(0,_q,_o));}))));});},_r=function(_s,_){return new T(function(){var _t=Number(E(_s)),_u=jsTrunc(_t);if(_u<0){return B(_p(_u));}else{if(_u>2){return B(_p(_u));}else{return _u;}}});},_v=0,_w=new T3(0,_v,_v,_v),_x="button",_y=new T(function(){return eval("jsGetMouseCoords");}),_z=__Z,_A=function(_B,_){var _C=E(_B);if(!_C._){return _z;}else{var _D=B(_A(_C.b,_));return new T2(1,new T(function(){var _E=Number(E(_C.a));return jsTrunc(_E);}),_D);}},_F=function(_G,_){var _H=__arr2lst(0,_G);return new F(function(){return _A(_H,_);});},_I=function(_J,_){return new F(function(){return _F(E(_J),_);});},_K=function(_L,_){return new T(function(){var _M=Number(E(_L));return jsTrunc(_M);});},_N=new T2(0,_K,_I),_O=function(_P,_){var _Q=E(_P);if(!_Q._){return _z;}else{var _R=B(_O(_Q.b,_));return new T2(1,_Q.a,_R);}},_S=new T(function(){return B(unCStr("base"));}),_T=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_U=new T(function(){return B(unCStr("IOException"));}),_V=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_S,_T,_U),_W=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_V,_z,_z),_X=function(_Y){return E(_W);},_Z=function(_10){return E(E(_10).a);},_11=function(_12,_13,_14){var _15=B(A1(_12,_)),_16=B(A1(_13,_)),_17=hs_eqWord64(_15.a,_16.a);if(!_17){return __Z;}else{var _18=hs_eqWord64(_15.b,_16.b);return (!_18)?__Z:new T1(1,_14);}},_19=function(_1a){var _1b=E(_1a);return new F(function(){return _11(B(_Z(_1b.a)),_X,_1b.b);});},_1c=new T(function(){return B(unCStr(": "));}),_1d=new T(function(){return B(unCStr(")"));}),_1e=new T(function(){return B(unCStr(" ("));}),_1f=new T(function(){return B(unCStr("interrupted"));}),_1g=new T(function(){return B(unCStr("system error"));}),_1h=new T(function(){return B(unCStr("unsatisified constraints"));}),_1i=new T(function(){return B(unCStr("user error"));}),_1j=new T(function(){return B(unCStr("permission denied"));}),_1k=new T(function(){return B(unCStr("illegal operation"));}),_1l=new T(function(){return B(unCStr("end of file"));}),_1m=new T(function(){return B(unCStr("resource exhausted"));}),_1n=new T(function(){return B(unCStr("resource busy"));}),_1o=new T(function(){return B(unCStr("does not exist"));}),_1p=new T(function(){return B(unCStr("already exists"));}),_1q=new T(function(){return B(unCStr("resource vanished"));}),_1r=new T(function(){return B(unCStr("timeout"));}),_1s=new T(function(){return B(unCStr("unsupported operation"));}),_1t=new T(function(){return B(unCStr("hardware fault"));}),_1u=new T(function(){return B(unCStr("inappropriate type"));}),_1v=new T(function(){return B(unCStr("invalid argument"));}),_1w=new T(function(){return B(unCStr("failed"));}),_1x=new T(function(){return B(unCStr("protocol error"));}),_1y=function(_1z,_1A){switch(E(_1z)){case 0:return new F(function(){return _7(_1p,_1A);});break;case 1:return new F(function(){return _7(_1o,_1A);});break;case 2:return new F(function(){return _7(_1n,_1A);});break;case 3:return new F(function(){return _7(_1m,_1A);});break;case 4:return new F(function(){return _7(_1l,_1A);});break;case 5:return new F(function(){return _7(_1k,_1A);});break;case 6:return new F(function(){return _7(_1j,_1A);});break;case 7:return new F(function(){return _7(_1i,_1A);});break;case 8:return new F(function(){return _7(_1h,_1A);});break;case 9:return new F(function(){return _7(_1g,_1A);});break;case 10:return new F(function(){return _7(_1x,_1A);});break;case 11:return new F(function(){return _7(_1w,_1A);});break;case 12:return new F(function(){return _7(_1v,_1A);});break;case 13:return new F(function(){return _7(_1u,_1A);});break;case 14:return new F(function(){return _7(_1t,_1A);});break;case 15:return new F(function(){return _7(_1s,_1A);});break;case 16:return new F(function(){return _7(_1r,_1A);});break;case 17:return new F(function(){return _7(_1q,_1A);});break;default:return new F(function(){return _7(_1f,_1A);});}},_1B=new T(function(){return B(unCStr("}"));}),_1C=new T(function(){return B(unCStr("{handle: "));}),_1D=function(_1E,_1F,_1G,_1H,_1I,_1J){var _1K=new T(function(){var _1L=new T(function(){var _1M=new T(function(){var _1N=E(_1H);if(!_1N._){return E(_1J);}else{var _1O=new T(function(){return B(_7(_1N,new T(function(){return B(_7(_1d,_1J));},1)));},1);return B(_7(_1e,_1O));}},1);return B(_1y(_1F,_1M));}),_1P=E(_1G);if(!_1P._){return E(_1L);}else{return B(_7(_1P,new T(function(){return B(_7(_1c,_1L));},1)));}}),_1Q=E(_1I);if(!_1Q._){var _1R=E(_1E);if(!_1R._){return E(_1K);}else{var _1S=E(_1R.a);if(!_1S._){var _1T=new T(function(){var _1U=new T(function(){return B(_7(_1B,new T(function(){return B(_7(_1c,_1K));},1)));},1);return B(_7(_1S.a,_1U));},1);return new F(function(){return _7(_1C,_1T);});}else{var _1V=new T(function(){var _1W=new T(function(){return B(_7(_1B,new T(function(){return B(_7(_1c,_1K));},1)));},1);return B(_7(_1S.a,_1W));},1);return new F(function(){return _7(_1C,_1V);});}}}else{return new F(function(){return _7(_1Q.a,new T(function(){return B(_7(_1c,_1K));},1));});}},_1X=function(_1Y){var _1Z=E(_1Y);return new F(function(){return _1D(_1Z.a,_1Z.b,_1Z.c,_1Z.d,_1Z.f,_z);});},_20=function(_21,_22,_23){var _24=E(_22);return new F(function(){return _1D(_24.a,_24.b,_24.c,_24.d,_24.f,_23);});},_25=function(_26,_27){var _28=E(_26);return new F(function(){return _1D(_28.a,_28.b,_28.c,_28.d,_28.f,_27);});},_29=44,_2a=93,_2b=91,_2c=function(_2d,_2e,_2f){var _2g=E(_2e);if(!_2g._){return new F(function(){return unAppCStr("[]",_2f);});}else{var _2h=new T(function(){var _2i=new T(function(){var _2j=function(_2k){var _2l=E(_2k);if(!_2l._){return E(new T2(1,_2a,_2f));}else{var _2m=new T(function(){return B(A2(_2d,_2l.a,new T(function(){return B(_2j(_2l.b));})));});return new T2(1,_29,_2m);}};return B(_2j(_2g.b));});return B(A2(_2d,_2g.a,_2i));});return new T2(1,_2b,_2h);}},_2n=function(_2o,_2p){return new F(function(){return _2c(_25,_2o,_2p);});},_2q=new T3(0,_20,_1X,_2n),_2r=new T(function(){return new T5(0,_X,_2q,_2s,_19,_1X);}),_2s=function(_2t){return new T2(0,_2r,_2t);},_2u=__Z,_2v=7,_2w=new T(function(){return B(unCStr("Pattern match failure in do expression at src\\Haste\\Prim\\Any.hs:272:5-9"));}),_2x=new T6(0,_2u,_2v,_z,_2w,_2u,_2u),_2y=new T(function(){return B(_2s(_2x));}),_2z=function(_){return new F(function(){return die(_2y);});},_2A=function(_2B){return E(E(_2B).a);},_2C=function(_2D,_2E,_2F,_){var _2G=__arr2lst(0,_2F),_2H=B(_O(_2G,_)),_2I=E(_2H);if(!_2I._){return new F(function(){return _2z(_);});}else{var _2J=E(_2I.b);if(!_2J._){return new F(function(){return _2z(_);});}else{if(!E(_2J.b)._){var _2K=B(A3(_2A,_2D,_2I.a,_)),_2L=B(A3(_2A,_2E,_2J.a,_));return new T2(0,_2K,_2L);}else{return new F(function(){return _2z(_);});}}}},_2M=function(_){return new F(function(){return __jsNull();});},_2N=function(_2O){var _2P=B(A1(_2O,_));return E(_2P);},_2Q=new T(function(){return B(_2N(_2M));}),_2R=new T(function(){return E(_2Q);}),_2S=function(_2T,_2U,_){if(E(_2T)==7){var _2V=__app1(E(_y),_2U),_2W=B(_2C(_N,_N,_2V,_)),_2X=__get(_2U,E(_6)),_2Y=__get(_2U,E(_5)),_2Z=__get(_2U,E(_4));return new T(function(){return new T3(0,E(_2W),E(_2u),E(new T3(0,_2X,_2Y,_2Z)));});}else{var _30=__app1(E(_y),_2U),_31=B(_2C(_N,_N,_30,_)),_32=__get(_2U,E(_x)),_33=__eq(_32,E(_2R));if(!E(_33)){var _34=B(_r(_32,_));return new T(function(){return new T3(0,E(_31),E(new T1(1,_34)),E(_w));});}else{return new T(function(){return new T3(0,E(_31),E(_2u),E(_w));});}}},_35=function(_36,_37,_){return new F(function(){return _2S(_36,E(_37),_);});},_38="mouseout",_39="mouseover",_3a="mousemove",_3b="mouseup",_3c="mousedown",_3d="dblclick",_3e="click",_3f="wheel",_3g=function(_3h){switch(E(_3h)){case 0:return E(_3e);case 1:return E(_3d);case 2:return E(_3c);case 3:return E(_3b);case 4:return E(_3a);case 5:return E(_39);case 6:return E(_38);default:return E(_3f);}},_3i=new T2(0,_3g,_35),_3j=function(_3k,_){return new T1(1,_3k);},_3l=function(_3m){return E(_3m);},_3n=new T2(0,_3l,_3j),_3o=function(_3p,_3q,_){var _3r=B(A1(_3p,_)),_3s=B(A1(_3q,_));return _3r;},_3t=function(_3u,_3v,_){var _3w=B(A1(_3u,_)),_3x=B(A1(_3v,_));return new T(function(){return B(A1(_3w,_3x));});},_3y=function(_3z,_3A,_){var _3B=B(A1(_3A,_));return _3z;},_3C=function(_3D,_3E,_){var _3F=B(A1(_3E,_));return new T(function(){return B(A1(_3D,_3F));});},_3G=new T2(0,_3C,_3y),_3H=function(_3I,_){return _3I;},_3J=function(_3K,_3L,_){var _3M=B(A1(_3K,_));return new F(function(){return A1(_3L,_);});},_3N=new T5(0,_3G,_3H,_3t,_3J,_3o),_3O=new T(function(){return E(_2r);}),_3P=function(_3Q){return E(E(_3Q).c);},_3R=function(_3S){return new T6(0,_2u,_2v,_z,_3S,_2u,_2u);},_3T=function(_3U,_){var _3V=new T(function(){return B(A2(_3P,_3O,new T(function(){return B(A1(_3R,_3U));})));});return new F(function(){return die(_3V);});},_3W=function(_3X,_){return new F(function(){return _3T(_3X,_);});},_3Y=function(_3Z){return new F(function(){return A1(_3W,_3Z);});},_40=function(_41,_42,_){var _43=B(A1(_41,_));return new F(function(){return A2(_42,_43,_);});},_44=new T5(0,_3N,_40,_3J,_3H,_3Y),_45=new T2(0,_44,_3l),_46=new T2(0,_45,_3H),_47=function(_48,_49,_4a,_4b,_4c){return new T5(0,_48,_49,_4a,_4b,_4c);},_4d=function(_4e,_4f){if(_4e<=_4f){var _4g=function(_4h){return new T2(1,_4h,new T(function(){if(_4h!=_4f){return B(_4g(_4h+1|0));}else{return __Z;}}));};return new F(function(){return _4g(_4e);});}else{return __Z;}},_4i=new T(function(){return B(_4d(0,2147483647));}),_4j=function(_4k,_4l){var _4m=E(_4l);return (_4m._==0)?__Z:new T2(1,new T(function(){return B(A1(_4k,_4m.a));}),new T(function(){return B(_4j(_4k,_4m.b));}));},_4n=function(_4o,_4p,_4q,_4r){switch(E(_4r)){case 0:return E(_4o);case 1:return E(_4p);default:return E(_4q);}},_4s=function(_4t,_4u,_4v,_4w){var _4x=new T(function(){var _4y=function(_4z){var _4A=function(_4B){return new T3(0,new T(function(){return B(_4n(_4u,_4B,_4z,_4t));}),new T(function(){return B(_4n(_4u,_4B,_4z,_4v));}),new T(function(){return B(_4n(_4u,_4B,_4z,_4w));}));};return new F(function(){return _4j(_4A,_4i);});};return B(_4j(_4y,_4i));});return function(_4C){return new F(function(){return _47(new T2(0,_4t,_4u),_4v,_4w,_4x,_4C);});};},_4D=function(_4E,_4F,_4G,_4H){while(1){var _4I=E(_4H);if(!_4I._){var _4J=_4I.d,_4K=_4I.e,_4L=E(_4I.b),_4M=E(_4L.a);if(_4E>=_4M){if(_4E!=_4M){_4H=_4K;continue;}else{var _4N=E(_4L.b);if(_4F>=_4N){if(_4F!=_4N){_4H=_4K;continue;}else{var _4O=E(_4L.c);if(_4G>=_4O){if(_4G!=_4O){_4H=_4K;continue;}else{return new T1(1,_4I.c);}}else{_4H=_4J;continue;}}}else{_4H=_4J;continue;}}}else{_4H=_4J;continue;}}else{return __Z;}}},_4P=function(_4Q,_4R,_4S,_4T){while(1){var _4U=E(_4T);if(!_4U._){var _4V=_4U.d,_4W=_4U.e,_4X=E(_4U.b),_4Y=E(_4X.a);if(_4Q>=_4Y){if(_4Q!=_4Y){_4T=_4W;continue;}else{var _4Z=E(_4X.b);if(_4R>=_4Z){if(_4R!=_4Z){_4T=_4W;continue;}else{var _50=E(_4S),_51=E(_4X.c);if(_50>=_51){if(_50!=_51){return new F(function(){return _4D(_4Q,_4R,_50,_4W);});}else{return new T1(1,_4U.c);}}else{return new F(function(){return _4D(_4Q,_4R,_50,_4V);});}}}else{_4T=_4V;continue;}}}else{_4T=_4V;continue;}}else{return __Z;}}},_52=function(_53,_54,_55,_56){while(1){var _57=E(_56);if(!_57._){var _58=_57.d,_59=_57.e,_5a=E(_57.b),_5b=E(_5a.a);if(_53>=_5b){if(_53!=_5b){_56=_59;continue;}else{var _5c=E(_54),_5d=E(_5a.b);if(_5c>=_5d){if(_5c!=_5d){return new F(function(){return _4P(_53,_5c,_55,_59);});}else{var _5e=E(_55),_5f=E(_5a.c);if(_5e>=_5f){if(_5e!=_5f){return new F(function(){return _4D(_53,_5c,_5e,_59);});}else{return new T1(1,_57.c);}}else{return new F(function(){return _4D(_53,_5c,_5e,_58);});}}}else{return new F(function(){return _4P(_53,_5c,_55,_58);});}}}else{_56=_58;continue;}}else{return __Z;}}},_5g=function(_5h,_5i,_5j,_5k){var _5l=E(_5k);if(!_5l._){var _5m=_5l.d,_5n=_5l.e,_5o=E(_5l.b),_5p=E(_5h),_5q=E(_5o.a);if(_5p>=_5q){if(_5p!=_5q){return new F(function(){return _52(_5p,_5i,_5j,_5n);});}else{var _5r=E(_5i),_5s=E(_5o.b);if(_5r>=_5s){if(_5r!=_5s){return new F(function(){return _4P(_5p,_5r,_5j,_5n);});}else{var _5t=E(_5j),_5u=E(_5o.c);if(_5t>=_5u){if(_5t!=_5u){return new F(function(){return _4D(_5p,_5r,_5t,_5n);});}else{return new T1(1,_5l.c);}}else{return new F(function(){return _4D(_5p,_5r,_5t,_5m);});}}}else{return new F(function(){return _4P(_5p,_5r,_5j,_5m);});}}}else{return new F(function(){return _52(_5p,_5i,_5j,_5m);});}}else{return __Z;}},_5v=function(_5w){return E(E(_5w).d);},_5x=new T(function(){return B(unCStr("base"));}),_5y=new T(function(){return B(unCStr("Control.Exception.Base"));}),_5z=new T(function(){return B(unCStr("RecSelError"));}),_5A=new T5(0,new Long(2975920724,3651309139,true),new Long(465443624,4160253997,true),_5x,_5y,_5z),_5B=new T5(0,new Long(2975920724,3651309139,true),new Long(465443624,4160253997,true),_5A,_z,_z),_5C=function(_5D){return E(_5B);},_5E=function(_5F){var _5G=E(_5F);return new F(function(){return _11(B(_Z(_5G.a)),_5C,_5G.b);});},_5H=function(_5I){return E(E(_5I).a);},_5J=function(_5K){return new T2(0,_5L,_5K);},_5M=function(_5N,_5O){return new F(function(){return _7(E(_5N).a,_5O);});},_5P=function(_5Q,_5R){return new F(function(){return _2c(_5M,_5Q,_5R);});},_5S=function(_5T,_5U,_5V){return new F(function(){return _7(E(_5U).a,_5V);});},_5W=new T3(0,_5S,_5H,_5P),_5L=new T(function(){return new T5(0,_5C,_5W,_5J,_5E,_5H);}),_5X=function(_5Y,_5Z){return new F(function(){return die(new T(function(){return B(A2(_3P,_5Z,_5Y));}));});},_60=function(_61,_62){return new F(function(){return _5X(_61,_62);});},_63=function(_64){var _65=new T(function(){return B(unAppCStr("No match in record selector ",new T(function(){return B(unCStr(_64));})));});return new F(function(){return _60(new T1(0,_65),_5L);});},_66=new T(function(){return B(_63("colour"));}),_67=function(_68){return E(E(_68).b);},_69=function(_6a){return E(E(_6a).a);},_6b=function(_6c,_6d){return new T4(0,new T(function(){return B(_69(_6d));}),new T(function(){return B(_67(_6d));}),new T(function(){var _6e=E(_6d),_6f=_6e.b,_6g=E(_6c),_6h=B(_5g(_6g.a,_6g.b,_6g.c,_6e.d));if(!_6h._){return __Z;}else{var _6i=E(_6h.a);if(!_6i._){if(!E(_6i.a)){if(!E(_6f)){return new T1(1,_6g);}else{return __Z;}}else{if(!E(_6f)){return __Z;}else{return new T1(1,_6g);}}}else{return E(_66);}}}),new T(function(){return B(_5v(_6d));}));},_6j=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_6k=new T(function(){return B(err(_6j));}),_6l=function(_){return _0;},_6m=function(_6n,_6o){return E(_6n)==E(_6o);},_6p=function(_6q,_6r){return E(_6q)!=E(_6r);},_6s=new T2(0,_6m,_6p),_6t=function(_6u,_6v){var _6w=E(_6u),_6x=E(_6v);return (_6w>_6x)?E(_6w):E(_6x);},_6y=function(_6z,_6A){var _6B=E(_6z),_6C=E(_6A);return (_6B>_6C)?E(_6C):E(_6B);},_6D=function(_6E,_6F){return (_6E>=_6F)?(_6E!=_6F)?2:1:0;},_6G=function(_6H,_6I){return new F(function(){return _6D(E(_6H),E(_6I));});},_6J=function(_6K,_6L){return E(_6K)>=E(_6L);},_6M=function(_6N,_6O){return E(_6N)>E(_6O);},_6P=function(_6Q,_6R){return E(_6Q)<=E(_6R);},_6S=function(_6T,_6U){return E(_6T)<E(_6U);},_6V={_:0,a:_6s,b:_6G,c:_6S,d:_6P,e:_6M,f:_6J,g:_6t,h:_6y},_6W=function(_6X){return E(E(_6X).a);},_6Y=function(_6Z){return E(E(_6Z).a);},_70=function(_71){return E(E(_71).a);},_72=new T(function(){return B(unCStr("!!: negative index"));}),_73=new T(function(){return B(unCStr("Prelude."));}),_74=new T(function(){return B(_7(_73,_72));}),_75=new T(function(){return B(err(_74));}),_76=new T(function(){return B(unCStr("!!: index too large"));}),_77=new T(function(){return B(_7(_73,_76));}),_78=new T(function(){return B(err(_77));}),_79=function(_7a,_7b){while(1){var _7c=E(_7a);if(!_7c._){return E(_78);}else{var _7d=E(_7b);if(!_7d){return E(_7c.a);}else{_7a=_7c.b;_7b=_7d-1|0;continue;}}}},_7e=function(_7f,_7g){if(_7g>=0){return new F(function(){return _79(_7f,_7g);});}else{return E(_75);}},_7h=function(_7i,_7j){while(1){var _7k=E(_7i);if(!_7k._){return E(_7j);}else{var _7l=_7j+1|0;_7i=_7k.b;_7j=_7l;continue;}}},_7m=109,_7n=100,_7o=99,_7p=108,_7q=120,_7r=118,_7s=105,_7t=function(_7u){if(_7u<1000){if(_7u<900){if(_7u<500){if(_7u<400){if(_7u<100){if(_7u<90){if(_7u<50){if(_7u<40){if(_7u<10){if(_7u<9){if(_7u<5){if(_7u<4){return (_7u<1)?__Z:new T2(1,_7s,new T(function(){return B(_7t(_7u-1|0));}));}else{return new F(function(){return unAppCStr("iv",new T(function(){return B(_7t(_7u-4|0));}));});}}else{return new T2(1,_7r,new T(function(){return B(_7t(_7u-5|0));}));}}else{return new F(function(){return unAppCStr("ix",new T(function(){return B(_7t(_7u-9|0));}));});}}else{return new T2(1,_7q,new T(function(){return B(_7t(_7u-10|0));}));}}else{return new F(function(){return unAppCStr("xl",new T(function(){return B(_7t(_7u-40|0));}));});}}else{return new T2(1,_7p,new T(function(){return B(_7t(_7u-50|0));}));}}else{return new F(function(){return unAppCStr("xc",new T(function(){return B(_7t(_7u-90|0));}));});}}else{return new T2(1,_7o,new T(function(){return B(_7t(_7u-100|0));}));}}else{return new F(function(){return unAppCStr("cd",new T(function(){return B(_7t(_7u-400|0));}));});}}else{return new T2(1,_7n,new T(function(){return B(_7t(_7u-500|0));}));}}else{return new F(function(){return unAppCStr("cm",new T(function(){return B(_7t(_7u-900|0));}));});}}else{return new T2(1,_7m,new T(function(){return B(_7t(_7u-1000|0));}));}},_7v=new T(function(){return B(unCStr("+"));}),_7w=new T(function(){return B(unCStr("+ - "));}),_7x=new T(function(){return B(_7(_7w,_7v));}),_7y=function(_7z){var _7A=E(_7z);if(_7A==1){return E(_7x);}else{return new F(function(){return _7(_7w,new T(function(){return B(_7y(_7A-1|0));},1));});}},_7B=function(_7C,_7D){return new T2(1,_7C,_7D);},_7E=function(_7F){return E(E(_7F).c);},_7G=function(_7H){return E(E(_7H).c);},_7I=function(_7J){return E(E(_7J).b);},_7K=function(_7L){return new T1(2,_7L);},_7M=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_7N=new T(function(){return B(unCStr("PatternMatchFail"));}),_7O=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5x,_5y,_7N),_7P=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_7O,_z,_z),_7Q=function(_7R){return E(_7P);},_7S=function(_7T){var _7U=E(_7T);return new F(function(){return _11(B(_Z(_7U.a)),_7Q,_7U.b);});},_7V=function(_7W){return E(E(_7W).a);},_7X=function(_5K){return new T2(0,_7Y,_5K);},_7Z=function(_80,_81){return new F(function(){return _7(E(_80).a,_81);});},_82=function(_83,_84){return new F(function(){return _2c(_7Z,_83,_84);});},_85=function(_86,_87,_88){return new F(function(){return _7(E(_87).a,_88);});},_89=new T3(0,_85,_7V,_82),_7Y=new T(function(){return new T5(0,_7Q,_89,_7X,_7S,_7V);}),_8a=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_8b=function(_8c,_8d){var _8e=E(_8d);if(!_8e._){return new T2(0,_z,_z);}else{var _8f=_8e.a;if(!B(A1(_8c,_8f))){return new T2(0,_z,_8e);}else{var _8g=new T(function(){var _8h=B(_8b(_8c,_8e.b));return new T2(0,_8h.a,_8h.b);});return new T2(0,new T2(1,_8f,new T(function(){return E(E(_8g).a);})),new T(function(){return E(E(_8g).b);}));}}},_8i=32,_8j=new T(function(){return B(unCStr("\n"));}),_8k=function(_8l){return (E(_8l)==124)?false:true;},_8m=function(_8n,_8o){var _8p=B(_8b(_8k,B(unCStr(_8n)))),_8q=_8p.a,_8r=function(_8s,_8t){var _8u=new T(function(){var _8v=new T(function(){return B(_7(_8o,new T(function(){return B(_7(_8t,_8j));},1)));});return B(unAppCStr(": ",_8v));},1);return new F(function(){return _7(_8s,_8u);});},_8w=E(_8p.b);if(!_8w._){return new F(function(){return _8r(_8q,_z);});}else{if(E(_8w.a)==124){return new F(function(){return _8r(_8q,new T2(1,_8i,_8w.b));});}else{return new F(function(){return _8r(_8q,_z);});}}},_8x=function(_8y){return new F(function(){return _60(new T1(0,new T(function(){return B(_8m(_8y,_8a));})),_7Y);});},_8z=new T(function(){return B(_8x("Piece.hs:(37,3)-(51,33)|function asciiSymbol"));}),_8A=66,_8B=87,_8C=new T(function(){return B(unCStr("   "));}),_8D=35,_8E=42,_8F=32,_8G=75,_8H=81,_8I=78,_8J=82,_8K=80,_8L=function(_8M){var _8N=E(_8M);if(!_8N._){return E(_8C);}else{var _8O=E(_8N.a);return (_8O._==0)?new T2(1,new T(function(){if(!E(_8O.a)){return E(_8B);}else{return E(_8A);}}),new T2(1,new T(function(){switch(E(_8O.b)._){case 0:return E(_8K);break;case 1:return E(_8J);break;case 2:return E(_8I);break;case 3:return E(_8A);break;case 4:return E(_8H);break;default:return E(_8G);}}),new T2(1,new T(function(){if(!E(_8O.d)._){return E(_8F);}else{if(!E(_8O.c)){return E(_8E);}else{return E(_8D);}}}),_z))):E(_8z);}},_8P=function(_8Q){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_h(9,_8Q,_z));}))));});},_8R=function(_8S){return E(E(_8S).a);},_8T=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_8U=function(_8V){return E(E(_8V).b);},_8W=new T(function(){return B(unCStr("selected"));}),_8X=3,_8Y=function(_8Z){return E(E(_8Z).g);},_90=new T(function(){return B(unCStr(": empty list"));}),_91=function(_92){return new F(function(){return err(B(_7(_73,new T(function(){return B(_7(_92,_90));},1))));});},_93=new T(function(){return B(unCStr("maximum"));}),_94=new T(function(){return B(_91(_93));}),_95=function(_96,_97){var _98=E(_97);if(!_98._){return E(_94);}else{var _99=new T(function(){return B(_8Y(_96));}),_9a=function(_9b,_9c){while(1){var _9d=E(_9b);if(!_9d._){return E(_9c);}else{var _9e=B(A2(_99,E(_9c),_9d.a));_9b=_9d.b;_9c=_9e;continue;}}};return new F(function(){return _9a(_98.b,_98.a);});}},_9f=new T(function(){return B(_95(_6V,_z));}),_9g=8,_9h=new T(function(){return B(unCStr("span"));}),_9i=new T(function(){return toJSStr(E(_9h));}),_9j=new T(function(){return B(unCStr("|"));}),_9k=new T(function(){return toJSStr(E(_9j));}),_9l=new T(function(){return B(unCStr("id"));}),_9m=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_9n=function(_9o,_9p){var _9q=function(_){return new F(function(){return __app1(E(_9m),E(_9p));});};return new F(function(){return A2(_8U,_9o,_9q);});},_9r=new T(function(){return B(unCStr("br"));}),_9s=new T(function(){return toJSStr(E(_9r));}),_9t=function(_9u){return new F(function(){return A3(_8R,B(_6W(B(_6Y(B(_70(_9u)))))),_7K,new T(function(){return B(_9n(_9u,_9s));}));});},_9v=new T(function(){return eval("(function(s){return document.createTextNode(s);})");}),_9w=function(_9x,_9y){var _9z=function(_){return new F(function(){return __app1(E(_9v),E(_9y));});};return new F(function(){return A2(_8U,_9x,_9z);});},_9A=function(_9B){return E(E(_9B).d);},_9C=32,_9D=new T2(1,_9C,_z),_9E=function(_9F){var _9G=E(_9F);return (_9G==1)?E(_9D):new T2(1,_9C,new T(function(){return B(_9E(_9G-1|0));}));},_9H=function(_9I,_9J){var _9K=new T(function(){return B(_9w(_9I,new T(function(){var _9L=E(_9J);if(0>=_9L){return toJSStr(_z);}else{return toJSStr(B(_9E(_9L)));}},1)));});return new F(function(){return A3(_8R,B(_6W(B(_6Y(B(_70(_9I)))))),_7K,_9K);});},_9M=new T(function(){return B(unCStr("n"));}),_9N=function(_9O,_9P,_9Q,_9R,_9S,_9T){var _9U=function(_9V){var _9W=new T(function(){switch(E(_9Q)){case 0:return E(E(_9T).a)+1|0;break;case 1:return E(_9g);break;default:return E(_9g);}}),_9X=new T(function(){var _9Y=E(_9W);if(0>=_9Y){return toJSStr(E(_7v));}else{return toJSStr(B(_7y(_9Y)));}}),_9Z=new T(function(){var _a0=function(_a1){switch(E(_9R)){case 0:var _a2=E(_a1);if(!_a2){return new F(function(){return _7h(_9M,0);});}else{return new F(function(){return _7h(B(_7t(_a2)),0);});}break;case 1:return 1;default:return 1;}};switch(E(_9R)){case 0:var _a3=E(E(_9T).a);if(0<=_a3){var _a4=function(_a5){return new T2(1,new T(function(){return B(_a0(_a5));}),new T(function(){if(_a5!=_a3){return B(_a4(_a5+1|0));}else{return __Z;}}));},_a6=E(B(_95(_6V,B(_a4(0)))));if(_a6==2147483647){return E(_6k);}else{return _a6+1|0;}}else{var _a7=E(_9f);if(_a7==2147483647){return E(_6k);}else{return _a7+1|0;}}break;case 1:var _a8=function(_a9){return new T2(1,new T(function(){return B(_a0(_a9));}),new T(function(){var _aa=E(_a9);if(_aa==7){return __Z;}else{return B(_a8(_aa+1|0));}}));},_ab=E(B(_95(_6V,B(_a8(0)))));if(_ab==2147483647){return E(_6k);}else{return _ab+1|0;}break;default:var _ac=function(_ad){return new T2(1,new T(function(){return B(_a0(_ad));}),new T(function(){var _ae=E(_ad);if(_ae==7){return __Z;}else{return B(_ac(_ae+1|0));}}));},_af=E(B(_95(_6V,B(_ac(0)))));if(_af==2147483647){return E(_6k);}else{return _af+1|0;}}}),_ag=function(_ah){var _ai=new T(function(){return B(A3(_8R,B(_6W(B(_6Y(B(_70(_ah)))))),_7K,new T(function(){return B(_9w(_ah,_9X));})));});return new T2(1,new T(function(){return B(_9H(_ah,_9Z));}),new T2(1,_ai,new T2(1,new T(function(){return B(_9t(_ah));}),_z)));},_aj=B(_70(_9O)),_ak=new T(function(){var _al=function(_am){if(0<=_am){var _an=new T(function(){return B(_9n(_9O,_9i));}),_ao=new T(function(){return B(_9A(_aj));}),_ap=new T(function(){return B(_9H(_9O,_8X));}),_aq=function(_ar){var _as=new T(function(){var _at=new T(function(){var _au=new T(function(){switch(E(_9Q)){case 0:var _av=E(_ar);if(!_av){return toJSStr(E(_9M));}else{return toJSStr(B(_7t(_av)));}break;case 1:return toJSStr(new T2(1,new T(function(){var _aw=97+_ar|0;if(_aw>>>0>1114111){return B(_8P(_aw));}else{return _aw;}}),_z));break;default:return toJSStr(new T2(1,new T(function(){var _ax=49+_ar|0;if(_ax>>>0>1114111){return B(_8P(_ax));}else{return _ax;}}),_z));}},1);return B(_9w(_9O,_au));}),_ay=function(_az){var _aA=new T(function(){var _aB=function(_aC){var _aD=function(_){var _aE=__app2(E(_7M),E(_aC),E(_az));return new F(function(){return _6l(_);});};return new F(function(){return A2(_8U,_9O,_aD);});};return B(A3(_7I,_aj,_at,_aB));});return new F(function(){return A3(_7G,_aj,_aA,new T(function(){return B(A1(_ao,new T1(1,_az)));}));});};return B(A3(_7I,_aj,_an,_ay));});return new T2(1,_as,new T2(1,_ap,new T(function(){if(_ar!=_am){return B(_aq(_ar+1|0));}else{return __Z;}})));};return new F(function(){return _aq(0);});}else{return __Z;}};switch(E(_9Q)){case 0:return B(_al(E(E(_9T).a)));break;case 1:return B(_al(7));break;default:return B(_al(7));}}),_aF=new T(function(){return B(_9H(_9O,new T(function(){return E(_9Z)+2|0;},1)));}),_aG=B(_7(new T2(1,_aF,_ak),new T2(1,new T(function(){return B(_9t(_9O));}),new T(function(){return B(_ag(_9O));})))),_aH=new T(function(){return B(_6Y(_aj));}),_aI=new T(function(){return B(_6W(_aH));}),_aJ=new T(function(){return B(A2(_9A,_aj,_z));}),_aK=function(_aL){var _aM=E(_aL);if(!_aM._){return E(_aJ);}else{return new F(function(){return A3(_7E,_aH,new T(function(){return B(A3(_8R,_aI,_7B,_aM.a));}),new T(function(){return B(_aK(_aM.b));}));});}};if(0<=_9V){var _aN=new T(function(){return B(A3(_8R,B(_6W(B(_6Y(B(_70(_9O)))))),_7K,new T(function(){return B(_9w(_9O,_9k));})));}),_aO=new T(function(){return B(_9A(_aj));}),_aP=new T(function(){return B(_9n(_9O,_9i));}),_aQ=new T(function(){return B(A2(_9A,_aj,_0));}),_aR=function(_aS,_aT){var _aU=new T(function(){var _aV=new T(function(){return B(_9w(_9O,new T(function(){var _aW=E(_aS);return toJSStr(B(_8L(B(_5g(_aW.a,_aW.b,_aW.c,E(_9T).d)))));},1)));}),_aX=new T(function(){var _aY=E(E(_9T).c);if(!_aY._){return false;}else{var _aZ=E(_aS),_b0=E(_aY.a);if(E(_aZ.a)!=E(_b0.a)){return false;}else{if(E(_aZ.b)!=E(_b0.b)){return false;}else{return E(_aZ.c)==E(_b0.c);}}}}),_b1=function(_b2){var _b3=new T(function(){var _b4=new T(function(){if(!E(_aX)){return E(_aQ);}else{var _b5=function(_){var _b6=__app3(E(_8T),E(_b2),toJSStr(E(_9l)),toJSStr(E(_8W)));return new F(function(){return _6l(_);});};return B(A2(_8U,_9O,_b5));}});return B(A3(_7G,_aj,_b4,new T(function(){return B(A1(_aO,new T2(0,_aS,_b2)));})));}),_b7=new T(function(){var _b8=function(_b9){var _ba=function(_){var _bb=__app2(E(_7M),E(_b9),E(_b2));return new F(function(){return _6l(_);});};return new F(function(){return A2(_8U,_9O,_ba);});};return B(A3(_7I,_aj,_aV,_b8));});return new F(function(){return A3(_7G,_aj,_b7,_b3);});};return B(A3(_7I,_aj,_aP,_b1));});return new T2(1,_aN,new T2(1,_aU,_aT));},_bc=new T2(1,_aN,new T2(1,new T(function(){return B(_9t(_9O));}),_z)),_bd=function(_be,_bf){var _bg=E(_be);if(!_bg._){return E(_bc);}else{var _bh=_bg.a,_bi=E(_bf);if(_bi==1){return new F(function(){return _aR(_bh,_bc);});}else{return new F(function(){return _aR(_bh,new T(function(){return B(_bd(_bg.b,_bi-1|0));}));});}}},_bj=new T(function(){return B(_ag(_9O));}),_bk=function(_bl,_bm){while(1){var _bn=B((function(_bo,_bp){var _bq=new T(function(){var _br=new T(function(){return B(_9H(_9O,new T(function(){var _bs=E(_9Z);switch(E(_9R)){case 0:var _bt=E(_bo);if(!_bt){return _bs-B(_7h(_9M,0))|0;}else{return _bs-B(_7h(B(_7t(_bt)),0))|0;}break;case 1:return _bs-1|0;break;default:return _bs-1|0;}},1)));}),_bu=new T(function(){var _bv=new T(function(){var _bw=new T(function(){switch(E(_9R)){case 0:var _bx=E(_bo);if(!_bx){return toJSStr(E(_9M));}else{return toJSStr(B(_7t(_bx)));}break;case 1:return toJSStr(new T2(1,new T(function(){var _by=97+_bo|0;if(_by>>>0>1114111){return B(_8P(_by));}else{return _by;}}),_z));break;default:return toJSStr(new T2(1,new T(function(){var _bz=49+_bo|0;if(_bz>>>0>1114111){return B(_8P(_bz));}else{return _bz;}}),_z));}},1);return B(_9w(_9O,_bw));}),_bA=function(_bB){var _bC=new T(function(){var _bD=function(_bE){var _bF=function(_){var _bG=__app2(E(_7M),E(_bE),E(_bB));return new F(function(){return _6l(_);});};return new F(function(){return A2(_8U,_9O,_bF);});};return B(A3(_7I,_aj,_bv,_bD));});return new F(function(){return A3(_7G,_aj,_bC,new T(function(){return B(A1(_aO,new T1(1,_bB)));}));});};return B(A3(_7I,_aj,_aP,_bA));});return B(_7(new T2(1,_bu,new T2(1,_br,new T(function(){var _bH=E(_9W);if(0>=_bH){return E(_bc);}else{return B(_bd(B(_7e(_9S,_bo)),_bH));}}))),_bj));},1),_bI=B(_7(_bp,_bq));if(_bo!=_9V){var _bJ=_bo+1|0;_bl=_bJ;_bm=_bI;return __continue;}else{return E(_bI);}})(_bl,_bm));if(_bn!=__continue){return _bn;}}};return new F(function(){return _aK(B(_bk(0,_aG)));});}else{return new F(function(){return _aK(_aG);});}};switch(E(_9R)){case 0:return new F(function(){return _9U(E(E(_9T).a));});break;case 1:return new F(function(){return _9U(7);});break;default:return new F(function(){return _9U(7);});}},_bK=0,_bL=0,_bM=new T(function(){return B(unCStr("foldl1"));}),_bN=new T(function(){return B(_91(_bM));}),_bO=function(_bP){var _bQ=E(_bP);switch(_bQ._){case 0:return E(_bQ.b);case 1:return E(_bQ.a);default:return E(_bQ.a);}},_bR=function(_bS,_bT,_){while(1){var _bU=B((function(_bV,_bW,_){var _bX=E(_bV);if(!_bX._){return new F(function(){return A1(_bW,_);});}else{_bS=_bX.b;_bT=function(_){return new F(function(){return _3J(_bW,_bX.a,_);});};return __continue;}})(_bS,_bT,_));if(_bU!=__continue){return _bU;}}},_bY=new T(function(){return B(unCStr("Pattern match failure in do expression at Web.hs:26:9-21"));}),_bZ=new T6(0,_2u,_2v,_z,_bY,_2u,_2u),_c0=new T(function(){return B(_2s(_bZ));}),_c1=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_c2=function(_c3,_c4){var _c5=function(_){var _c6=__app1(E(_c1),E(_c4)),_c7=__eq(_c6,E(_2R));return (E(_c7)==0)?new T1(1,_c6):_2u;};return new F(function(){return A2(_8U,_c3,_c5);});},_c8="board",_c9=new T(function(){return B(_c2(_45,_c8));}),_ca=function(_cb,_cc,_cd,_ce){while(1){var _cf=E(_ce);if(!_cf._){var _cg=_cf.d,_ch=_cf.e,_ci=E(_cf.b),_cj=E(_ci.a);if(_cb>=_cj){if(_cb!=_cj){_ce=_ch;continue;}else{var _ck=E(_ci.b);if(_cc>=_ck){if(_cc!=_ck){_ce=_ch;continue;}else{var _cl=E(_ci.c);if(_cd>=_cl){if(_cd!=_cl){_ce=_ch;continue;}else{return new T1(1,_cf.c);}}else{_ce=_cg;continue;}}}else{_ce=_cg;continue;}}}else{_ce=_cg;continue;}}else{return __Z;}}},_cm=function(_cn,_co,_cp,_cq){while(1){var _cr=E(_cq);if(!_cr._){var _cs=_cr.d,_ct=_cr.e,_cu=E(_cr.b),_cv=E(_cu.a);if(_cn>=_cv){if(_cn!=_cv){_cq=_ct;continue;}else{var _cw=E(_cu.b);if(_co>=_cw){if(_co!=_cw){_cq=_ct;continue;}else{var _cx=E(_cp),_cy=E(_cu.c);if(_cx>=_cy){if(_cx!=_cy){return new F(function(){return _ca(_cn,_co,_cx,_ct);});}else{return new T1(1,_cr.c);}}else{return new F(function(){return _ca(_cn,_co,_cx,_cs);});}}}else{_cq=_cs;continue;}}}else{_cq=_cs;continue;}}else{return __Z;}}},_cz=function(_cA,_cB,_cC,_cD){while(1){var _cE=E(_cD);if(!_cE._){var _cF=_cE.d,_cG=_cE.e,_cH=E(_cE.b),_cI=E(_cH.a);if(_cA>=_cI){if(_cA!=_cI){_cD=_cG;continue;}else{var _cJ=E(_cB),_cK=E(_cH.b);if(_cJ>=_cK){if(_cJ!=_cK){return new F(function(){return _cm(_cA,_cJ,_cC,_cG);});}else{var _cL=E(_cC),_cM=E(_cH.c);if(_cL>=_cM){if(_cL!=_cM){return new F(function(){return _ca(_cA,_cJ,_cL,_cG);});}else{return new T1(1,_cE.c);}}else{return new F(function(){return _ca(_cA,_cJ,_cL,_cF);});}}}else{return new F(function(){return _cm(_cA,_cJ,_cC,_cF);});}}}else{_cD=_cF;continue;}}else{return __Z;}}},_cN=function(_cO,_cP,_cQ,_cR){var _cS=E(_cR);if(!_cS._){var _cT=_cS.d,_cU=_cS.e,_cV=E(_cS.b),_cW=E(_cO),_cX=E(_cV.a);if(_cW>=_cX){if(_cW!=_cX){return new F(function(){return _cz(_cW,_cP,_cQ,_cU);});}else{var _cY=E(_cP),_cZ=E(_cV.b);if(_cY>=_cZ){if(_cY!=_cZ){return new F(function(){return _cm(_cW,_cY,_cQ,_cU);});}else{var _d0=E(_cQ),_d1=E(_cV.c);if(_d0>=_d1){if(_d0!=_d1){return new F(function(){return _ca(_cW,_cY,_d0,_cU);});}else{return new T1(1,_cS.c);}}else{return new F(function(){return _ca(_cW,_cY,_d0,_cT);});}}}else{return new F(function(){return _cm(_cW,_cY,_cQ,_cT);});}}}else{return new F(function(){return _cz(_cW,_cP,_cQ,_cT);});}}else{return __Z;}},_d2=function(_d3,_d4){var _d5=E(_d3),_d6=E(_d4);return (E(_d5.a)!=E(_d6.a))?true:(E(_d5.b)!=E(_d6.b))?true:(E(_d5.c)!=E(_d6.c))?true:false;},_d7=function(_d8,_d9,_da,_db,_dc,_dd){if(_d8!=_db){return false;}else{if(E(_d9)!=E(_dc)){return false;}else{return new F(function(){return _6m(_da,_dd);});}}},_de=function(_df,_dg){var _dh=E(_df),_di=E(_dg);return new F(function(){return _d7(E(_dh.a),_dh.b,_dh.c,E(_di.a),_di.b,_di.c);});},_dj=new T2(0,_de,_d2),_dk=function(_dl,_dm,_dn,_do,_dp,_dq){if(_dl>=_do){if(_dl!=_do){return false;}else{var _dr=E(_dm),_ds=E(_dp);if(_dr>=_ds){if(_dr!=_ds){return false;}else{return new F(function(){return _6S(_dn,_dq);});}}else{return true;}}}else{return true;}},_dt=function(_du,_dv){var _dw=E(_du),_dx=E(_dv);return new F(function(){return _dk(E(_dw.a),_dw.b,_dw.c,E(_dx.a),_dx.b,_dx.c);});},_dy=function(_dz,_dA,_dB,_dC,_dD,_dE){if(_dz>=_dC){if(_dz!=_dC){return false;}else{var _dF=E(_dA),_dG=E(_dD);if(_dF>=_dG){if(_dF!=_dG){return false;}else{return new F(function(){return _6P(_dB,_dE);});}}else{return true;}}}else{return true;}},_dH=function(_dI,_dJ){var _dK=E(_dI),_dL=E(_dJ);return new F(function(){return _dy(E(_dK.a),_dK.b,_dK.c,E(_dL.a),_dL.b,_dL.c);});},_dM=function(_dN,_dO,_dP,_dQ,_dR,_dS){if(_dN>=_dQ){if(_dN!=_dQ){return true;}else{var _dT=E(_dO),_dU=E(_dR);if(_dT>=_dU){if(_dT!=_dU){return true;}else{return new F(function(){return _6M(_dP,_dS);});}}else{return false;}}}else{return false;}},_dV=function(_dW,_dX){var _dY=E(_dW),_dZ=E(_dX);return new F(function(){return _dM(E(_dY.a),_dY.b,_dY.c,E(_dZ.a),_dZ.b,_dZ.c);});},_e0=function(_e1,_e2,_e3,_e4,_e5,_e6){if(_e1>=_e4){if(_e1!=_e4){return true;}else{var _e7=E(_e2),_e8=E(_e5);if(_e7>=_e8){if(_e7!=_e8){return true;}else{return new F(function(){return _6J(_e3,_e6);});}}else{return false;}}}else{return false;}},_e9=function(_ea,_eb){var _ec=E(_ea),_ed=E(_eb);return new F(function(){return _e0(E(_ec.a),_ec.b,_ec.c,E(_ed.a),_ed.b,_ed.c);});},_ee=function(_ef,_eg,_eh,_ei,_ej,_ek){if(_ef>=_ei){if(_ef!=_ei){return 2;}else{var _el=E(_eg),_em=E(_ej);if(_el>=_em){if(_el!=_em){return 2;}else{return new F(function(){return _6G(_eh,_ek);});}}else{return 0;}}}else{return 0;}},_en=function(_eo,_ep){var _eq=E(_eo),_er=E(_ep);return new F(function(){return _ee(E(_eq.a),_eq.b,_eq.c,E(_er.a),_er.b,_er.c);});},_es=function(_et,_eu){var _ev=E(_et),_ew=E(_ev.a),_ex=E(_eu),_ey=E(_ex.a);if(_ew>=_ey){if(_ew!=_ey){return E(_ev);}else{var _ez=E(_ev.b),_eA=E(_ex.b);return (_ez>=_eA)?(_ez!=_eA)?E(_ev):(E(_ev.c)>E(_ex.c))?E(_ev):E(_ex):E(_ex);}}else{return E(_ex);}},_eB=function(_eC,_eD){var _eE=E(_eC),_eF=E(_eE.a),_eG=E(_eD),_eH=E(_eG.a);if(_eF>=_eH){if(_eF!=_eH){return E(_eG);}else{var _eI=E(_eE.b),_eJ=E(_eG.b);return (_eI>=_eJ)?(_eI!=_eJ)?E(_eG):(E(_eE.c)>E(_eG.c))?E(_eG):E(_eE):E(_eE);}}else{return E(_eE);}},_eK={_:0,a:_dj,b:_en,c:_dt,d:_dH,e:_dV,f:_e9,g:_es,h:_eB},_eL=new T0(1),_eM=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_eN=function(_eO){return new F(function(){return err(_eM);});},_eP=new T(function(){return B(_eN(_));}),_eQ=function(_eR,_eS,_eT,_eU){var _eV=E(_eT);if(!_eV._){var _eW=_eV.a,_eX=E(_eU);if(!_eX._){var _eY=_eX.a,_eZ=_eX.b,_f0=_eX.c;if(_eY<=(imul(3,_eW)|0)){return new T5(0,(1+_eW|0)+_eY|0,E(_eR),_eS,E(_eV),E(_eX));}else{var _f1=E(_eX.d);if(!_f1._){var _f2=_f1.a,_f3=_f1.b,_f4=_f1.c,_f5=_f1.d,_f6=E(_eX.e);if(!_f6._){var _f7=_f6.a;if(_f2>=(imul(2,_f7)|0)){var _f8=function(_f9){var _fa=E(_eR),_fb=E(_f1.e);return (_fb._==0)?new T5(0,(1+_eW|0)+_eY|0,E(_f3),_f4,E(new T5(0,(1+_eW|0)+_f9|0,E(_fa),_eS,E(_eV),E(_f5))),E(new T5(0,(1+_f7|0)+_fb.a|0,E(_eZ),_f0,E(_fb),E(_f6)))):new T5(0,(1+_eW|0)+_eY|0,E(_f3),_f4,E(new T5(0,(1+_eW|0)+_f9|0,E(_fa),_eS,E(_eV),E(_f5))),E(new T5(0,1+_f7|0,E(_eZ),_f0,E(_eL),E(_f6))));},_fc=E(_f5);if(!_fc._){return new F(function(){return _f8(_fc.a);});}else{return new F(function(){return _f8(0);});}}else{return new T5(0,(1+_eW|0)+_eY|0,E(_eZ),_f0,E(new T5(0,(1+_eW|0)+_f2|0,E(_eR),_eS,E(_eV),E(_f1))),E(_f6));}}else{return E(_eP);}}else{return E(_eP);}}}else{return new T5(0,1+_eW|0,E(_eR),_eS,E(_eV),E(_eL));}}else{var _fd=E(_eU);if(!_fd._){var _fe=_fd.a,_ff=_fd.b,_fg=_fd.c,_fh=_fd.e,_fi=E(_fd.d);if(!_fi._){var _fj=_fi.a,_fk=_fi.b,_fl=_fi.c,_fm=_fi.d,_fn=E(_fh);if(!_fn._){var _fo=_fn.a;if(_fj>=(imul(2,_fo)|0)){var _fp=function(_fq){var _fr=E(_eR),_fs=E(_fi.e);return (_fs._==0)?new T5(0,1+_fe|0,E(_fk),_fl,E(new T5(0,1+_fq|0,E(_fr),_eS,E(_eL),E(_fm))),E(new T5(0,(1+_fo|0)+_fs.a|0,E(_ff),_fg,E(_fs),E(_fn)))):new T5(0,1+_fe|0,E(_fk),_fl,E(new T5(0,1+_fq|0,E(_fr),_eS,E(_eL),E(_fm))),E(new T5(0,1+_fo|0,E(_ff),_fg,E(_eL),E(_fn))));},_ft=E(_fm);if(!_ft._){return new F(function(){return _fp(_ft.a);});}else{return new F(function(){return _fp(0);});}}else{return new T5(0,1+_fe|0,E(_ff),_fg,E(new T5(0,1+_fj|0,E(_eR),_eS,E(_eL),E(_fi))),E(_fn));}}else{return new T5(0,3,E(_fk),_fl,E(new T5(0,1,E(_eR),_eS,E(_eL),E(_eL))),E(new T5(0,1,E(_ff),_fg,E(_eL),E(_eL))));}}else{var _fu=E(_fh);return (_fu._==0)?new T5(0,3,E(_ff),_fg,E(new T5(0,1,E(_eR),_eS,E(_eL),E(_eL))),E(_fu)):new T5(0,2,E(_eR),_eS,E(_eL),E(_fd));}}else{return new T5(0,1,E(_eR),_eS,E(_eL),E(_eL));}}},_fv=function(_fw,_fx){return new T5(0,1,E(_fw),_fx,E(_eL),E(_eL));},_fy=function(_fz,_fA,_fB){var _fC=E(_fB);if(!_fC._){return new F(function(){return _eQ(_fC.b,_fC.c,_fC.d,B(_fy(_fz,_fA,_fC.e)));});}else{return new F(function(){return _fv(_fz,_fA);});}},_fD=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_fE=function(_fF){return new F(function(){return err(_fD);});},_fG=new T(function(){return B(_fE(_));}),_fH=function(_fI,_fJ,_fK,_fL){var _fM=E(_fL);if(!_fM._){var _fN=_fM.a,_fO=E(_fK);if(!_fO._){var _fP=_fO.a,_fQ=_fO.b,_fR=_fO.c;if(_fP<=(imul(3,_fN)|0)){return new T5(0,(1+_fP|0)+_fN|0,E(_fI),_fJ,E(_fO),E(_fM));}else{var _fS=E(_fO.d);if(!_fS._){var _fT=_fS.a,_fU=E(_fO.e);if(!_fU._){var _fV=_fU.a,_fW=_fU.b,_fX=_fU.c,_fY=_fU.d;if(_fV>=(imul(2,_fT)|0)){var _fZ=function(_g0){var _g1=E(_fU.e);return (_g1._==0)?new T5(0,(1+_fP|0)+_fN|0,E(_fW),_fX,E(new T5(0,(1+_fT|0)+_g0|0,E(_fQ),_fR,E(_fS),E(_fY))),E(new T5(0,(1+_fN|0)+_g1.a|0,E(_fI),_fJ,E(_g1),E(_fM)))):new T5(0,(1+_fP|0)+_fN|0,E(_fW),_fX,E(new T5(0,(1+_fT|0)+_g0|0,E(_fQ),_fR,E(_fS),E(_fY))),E(new T5(0,1+_fN|0,E(_fI),_fJ,E(_eL),E(_fM))));},_g2=E(_fY);if(!_g2._){return new F(function(){return _fZ(_g2.a);});}else{return new F(function(){return _fZ(0);});}}else{return new T5(0,(1+_fP|0)+_fN|0,E(_fQ),_fR,E(_fS),E(new T5(0,(1+_fN|0)+_fV|0,E(_fI),_fJ,E(_fU),E(_fM))));}}else{return E(_fG);}}else{return E(_fG);}}}else{return new T5(0,1+_fN|0,E(_fI),_fJ,E(_eL),E(_fM));}}else{var _g3=E(_fK);if(!_g3._){var _g4=_g3.a,_g5=_g3.b,_g6=_g3.c,_g7=_g3.e,_g8=E(_g3.d);if(!_g8._){var _g9=_g8.a,_ga=E(_g7);if(!_ga._){var _gb=_ga.a,_gc=_ga.b,_gd=_ga.c,_ge=_ga.d;if(_gb>=(imul(2,_g9)|0)){var _gf=function(_gg){var _gh=E(_ga.e);return (_gh._==0)?new T5(0,1+_g4|0,E(_gc),_gd,E(new T5(0,(1+_g9|0)+_gg|0,E(_g5),_g6,E(_g8),E(_ge))),E(new T5(0,1+_gh.a|0,E(_fI),_fJ,E(_gh),E(_eL)))):new T5(0,1+_g4|0,E(_gc),_gd,E(new T5(0,(1+_g9|0)+_gg|0,E(_g5),_g6,E(_g8),E(_ge))),E(new T5(0,1,E(_fI),_fJ,E(_eL),E(_eL))));},_gi=E(_ge);if(!_gi._){return new F(function(){return _gf(_gi.a);});}else{return new F(function(){return _gf(0);});}}else{return new T5(0,1+_g4|0,E(_g5),_g6,E(_g8),E(new T5(0,1+_gb|0,E(_fI),_fJ,E(_ga),E(_eL))));}}else{return new T5(0,3,E(_g5),_g6,E(_g8),E(new T5(0,1,E(_fI),_fJ,E(_eL),E(_eL))));}}else{var _gj=E(_g7);return (_gj._==0)?new T5(0,3,E(_gj.b),_gj.c,E(new T5(0,1,E(_g5),_g6,E(_eL),E(_eL))),E(new T5(0,1,E(_fI),_fJ,E(_eL),E(_eL)))):new T5(0,2,E(_fI),_fJ,E(_g3),E(_eL));}}else{return new T5(0,1,E(_fI),_fJ,E(_eL),E(_eL));}}},_gk=function(_gl,_gm,_gn){var _go=E(_gn);if(!_go._){return new F(function(){return _fH(_go.b,_go.c,B(_gk(_gl,_gm,_go.d)),_go.e);});}else{return new F(function(){return _fv(_gl,_gm);});}},_gp=function(_gq,_gr,_gs,_gt,_gu,_gv,_gw){return new F(function(){return _fH(_gt,_gu,B(_gk(_gq,_gr,_gv)),_gw);});},_gx=function(_gy,_gz,_gA,_gB,_gC,_gD,_gE,_gF){var _gG=E(_gA);if(!_gG._){var _gH=_gG.a,_gI=_gG.b,_gJ=_gG.c,_gK=_gG.d,_gL=_gG.e;if((imul(3,_gH)|0)>=_gB){if((imul(3,_gB)|0)>=_gH){return new T5(0,(_gH+_gB|0)+1|0,E(_gy),_gz,E(_gG),E(new T5(0,_gB,E(_gC),_gD,E(_gE),E(_gF))));}else{return new F(function(){return _eQ(_gI,_gJ,_gK,B(_gx(_gy,_gz,_gL,_gB,_gC,_gD,_gE,_gF)));});}}else{return new F(function(){return _fH(_gC,_gD,B(_gM(_gy,_gz,_gH,_gI,_gJ,_gK,_gL,_gE)),_gF);});}}else{return new F(function(){return _gp(_gy,_gz,_gB,_gC,_gD,_gE,_gF);});}},_gM=function(_gN,_gO,_gP,_gQ,_gR,_gS,_gT,_gU){var _gV=E(_gU);if(!_gV._){var _gW=_gV.a,_gX=_gV.b,_gY=_gV.c,_gZ=_gV.d,_h0=_gV.e;if((imul(3,_gP)|0)>=_gW){if((imul(3,_gW)|0)>=_gP){return new T5(0,(_gP+_gW|0)+1|0,E(_gN),_gO,E(new T5(0,_gP,E(_gQ),_gR,E(_gS),E(_gT))),E(_gV));}else{return new F(function(){return _eQ(_gQ,_gR,_gS,B(_gx(_gN,_gO,_gT,_gW,_gX,_gY,_gZ,_h0)));});}}else{return new F(function(){return _fH(_gX,_gY,B(_gM(_gN,_gO,_gP,_gQ,_gR,_gS,_gT,_gZ)),_h0);});}}else{return new F(function(){return _fy(_gN,_gO,new T5(0,_gP,E(_gQ),_gR,E(_gS),E(_gT)));});}},_h1=function(_h2,_h3,_h4,_h5){var _h6=E(_h4);if(!_h6._){var _h7=_h6.a,_h8=_h6.b,_h9=_h6.c,_ha=_h6.d,_hb=_h6.e,_hc=E(_h5);if(!_hc._){var _hd=_hc.a,_he=_hc.b,_hf=_hc.c,_hg=_hc.d,_hh=_hc.e;if((imul(3,_h7)|0)>=_hd){if((imul(3,_hd)|0)>=_h7){return new T5(0,(_h7+_hd|0)+1|0,E(_h2),_h3,E(_h6),E(_hc));}else{return new F(function(){return _eQ(_h8,_h9,_ha,B(_gx(_h2,_h3,_hb,_hd,_he,_hf,_hg,_hh)));});}}else{return new F(function(){return _fH(_he,_hf,B(_gM(_h2,_h3,_h7,_h8,_h9,_ha,_hb,_hg)),_hh);});}}else{return new F(function(){return _fy(_h2,_h3,_h6);});}}else{return new F(function(){return _gk(_h2,_h3,_h5);});}},_hi=function(_hj,_hk,_hl,_hm,_hn,_ho){var _hp=E(_hj);if(_hp==1){var _hq=E(_ho);if(!_hq._){return new T3(0,new T5(0,1,E(new T3(0,_hk,_hl,_hm)),_hn,E(_eL),E(_eL)),_z,_z);}else{var _hr=E(E(_hq.a).a),_hs=E(_hr.a);if(_hk>=_hs){if(_hk!=_hs){return new T3(0,new T5(0,1,E(new T3(0,_hk,_hl,_hm)),_hn,E(_eL),E(_eL)),_z,_hq);}else{var _ht=E(_hr.b);return (_hl>=_ht)?(_hl!=_ht)?new T3(0,new T5(0,1,E(new T3(0,_hk,_hl,_hm)),_hn,E(_eL),E(_eL)),_z,_hq):(_hm<E(_hr.c))?new T3(0,new T5(0,1,E(new T3(0,_hk,_hl,_hm)),_hn,E(_eL),E(_eL)),_hq,_z):new T3(0,new T5(0,1,E(new T3(0,_hk,_hl,_hm)),_hn,E(_eL),E(_eL)),_z,_hq):new T3(0,new T5(0,1,E(new T3(0,_hk,_hl,_hm)),_hn,E(_eL),E(_eL)),_hq,_z);}}else{return new T3(0,new T5(0,1,E(new T3(0,_hk,_hl,_hm)),_hn,E(_eL),E(_eL)),_hq,_z);}}}else{var _hu=B(_hi(_hp>>1,_hk,_hl,_hm,_hn,_ho)),_hv=_hu.a,_hw=_hu.c,_hx=E(_hu.b);if(!_hx._){return new T3(0,_hv,_z,_hw);}else{var _hy=E(_hx.a),_hz=_hy.a,_hA=_hy.b,_hB=E(_hx.b);if(!_hB._){return new T3(0,new T(function(){return B(_fy(_hz,_hA,_hv));}),_z,_hw);}else{var _hC=_hB.b,_hD=E(_hB.a),_hE=_hD.b,_hF=E(_hz),_hG=E(_hF.a),_hH=E(_hD.a),_hI=_hH.b,_hJ=_hH.c,_hK=E(_hH.a);if(_hG>=_hK){if(_hG!=_hK){return new T3(0,_hv,_z,_hx);}else{var _hL=E(_hF.b),_hM=E(_hI);if(_hL>=_hM){if(_hL!=_hM){return new T3(0,_hv,_z,_hx);}else{var _hN=E(_hJ);if(E(_hF.c)<_hN){var _hO=B(_hi(_hp>>1,_hK,_hM,_hN,_hE,_hC));return new T3(0,new T(function(){return B(_h1(_hF,_hA,_hv,_hO.a));}),_hO.b,_hO.c);}else{return new T3(0,_hv,_z,_hx);}}}else{var _hP=B(_hQ(_hp>>1,_hK,_hM,_hJ,_hE,_hC));return new T3(0,new T(function(){return B(_h1(_hF,_hA,_hv,_hP.a));}),_hP.b,_hP.c);}}}else{var _hR=B(_hS(_hp>>1,_hK,_hI,_hJ,_hE,_hC));return new T3(0,new T(function(){return B(_h1(_hF,_hA,_hv,_hR.a));}),_hR.b,_hR.c);}}}}},_hQ=function(_hT,_hU,_hV,_hW,_hX,_hY){var _hZ=E(_hT);if(_hZ==1){var _i0=E(_hY);if(!_i0._){return new T3(0,new T5(0,1,E(new T3(0,_hU,_hV,_hW)),_hX,E(_eL),E(_eL)),_z,_z);}else{var _i1=E(E(_i0.a).a),_i2=E(_i1.a);if(_hU>=_i2){if(_hU!=_i2){return new T3(0,new T5(0,1,E(new T3(0,_hU,_hV,_hW)),_hX,E(_eL),E(_eL)),_z,_i0);}else{var _i3=E(_i1.b);if(_hV>=_i3){if(_hV!=_i3){return new T3(0,new T5(0,1,E(new T3(0,_hU,_hV,_hW)),_hX,E(_eL),E(_eL)),_z,_i0);}else{var _i4=E(_hW);return (_i4<E(_i1.c))?new T3(0,new T5(0,1,E(new T3(0,_hU,_hV,_i4)),_hX,E(_eL),E(_eL)),_i0,_z):new T3(0,new T5(0,1,E(new T3(0,_hU,_hV,_i4)),_hX,E(_eL),E(_eL)),_z,_i0);}}else{return new T3(0,new T5(0,1,E(new T3(0,_hU,_hV,_hW)),_hX,E(_eL),E(_eL)),_i0,_z);}}}else{return new T3(0,new T5(0,1,E(new T3(0,_hU,_hV,_hW)),_hX,E(_eL),E(_eL)),_i0,_z);}}}else{var _i5=B(_hQ(_hZ>>1,_hU,_hV,_hW,_hX,_hY)),_i6=_i5.a,_i7=_i5.c,_i8=E(_i5.b);if(!_i8._){return new T3(0,_i6,_z,_i7);}else{var _i9=E(_i8.a),_ia=_i9.a,_ib=_i9.b,_ic=E(_i8.b);if(!_ic._){return new T3(0,new T(function(){return B(_fy(_ia,_ib,_i6));}),_z,_i7);}else{var _id=_ic.b,_ie=E(_ic.a),_if=_ie.b,_ig=E(_ia),_ih=E(_ig.a),_ii=E(_ie.a),_ij=_ii.b,_ik=_ii.c,_il=E(_ii.a);if(_ih>=_il){if(_ih!=_il){return new T3(0,_i6,_z,_i8);}else{var _im=E(_ig.b),_in=E(_ij);if(_im>=_in){if(_im!=_in){return new T3(0,_i6,_z,_i8);}else{var _io=E(_ik);if(E(_ig.c)<_io){var _ip=B(_hi(_hZ>>1,_il,_in,_io,_if,_id));return new T3(0,new T(function(){return B(_h1(_ig,_ib,_i6,_ip.a));}),_ip.b,_ip.c);}else{return new T3(0,_i6,_z,_i8);}}}else{var _iq=B(_hQ(_hZ>>1,_il,_in,_ik,_if,_id));return new T3(0,new T(function(){return B(_h1(_ig,_ib,_i6,_iq.a));}),_iq.b,_iq.c);}}}else{var _ir=B(_hS(_hZ>>1,_il,_ij,_ik,_if,_id));return new T3(0,new T(function(){return B(_h1(_ig,_ib,_i6,_ir.a));}),_ir.b,_ir.c);}}}}},_hS=function(_is,_it,_iu,_iv,_iw,_ix){var _iy=E(_is);if(_iy==1){var _iz=E(_ix);if(!_iz._){return new T3(0,new T5(0,1,E(new T3(0,_it,_iu,_iv)),_iw,E(_eL),E(_eL)),_z,_z);}else{var _iA=E(E(_iz.a).a),_iB=E(_iA.a);if(_it>=_iB){if(_it!=_iB){return new T3(0,new T5(0,1,E(new T3(0,_it,_iu,_iv)),_iw,E(_eL),E(_eL)),_z,_iz);}else{var _iC=E(_iu),_iD=E(_iA.b);if(_iC>=_iD){if(_iC!=_iD){return new T3(0,new T5(0,1,E(new T3(0,_it,_iC,_iv)),_iw,E(_eL),E(_eL)),_z,_iz);}else{var _iE=E(_iv);return (_iE<E(_iA.c))?new T3(0,new T5(0,1,E(new T3(0,_it,_iC,_iE)),_iw,E(_eL),E(_eL)),_iz,_z):new T3(0,new T5(0,1,E(new T3(0,_it,_iC,_iE)),_iw,E(_eL),E(_eL)),_z,_iz);}}else{return new T3(0,new T5(0,1,E(new T3(0,_it,_iC,_iv)),_iw,E(_eL),E(_eL)),_iz,_z);}}}else{return new T3(0,new T5(0,1,E(new T3(0,_it,_iu,_iv)),_iw,E(_eL),E(_eL)),_iz,_z);}}}else{var _iF=B(_hS(_iy>>1,_it,_iu,_iv,_iw,_ix)),_iG=_iF.a,_iH=_iF.c,_iI=E(_iF.b);if(!_iI._){return new T3(0,_iG,_z,_iH);}else{var _iJ=E(_iI.a),_iK=_iJ.a,_iL=_iJ.b,_iM=E(_iI.b);if(!_iM._){return new T3(0,new T(function(){return B(_fy(_iK,_iL,_iG));}),_z,_iH);}else{var _iN=_iM.b,_iO=E(_iM.a),_iP=_iO.b,_iQ=E(_iK),_iR=E(_iQ.a),_iS=E(_iO.a),_iT=_iS.b,_iU=_iS.c,_iV=E(_iS.a);if(_iR>=_iV){if(_iR!=_iV){return new T3(0,_iG,_z,_iI);}else{var _iW=E(_iQ.b),_iX=E(_iT);if(_iW>=_iX){if(_iW!=_iX){return new T3(0,_iG,_z,_iI);}else{var _iY=E(_iU);if(E(_iQ.c)<_iY){var _iZ=B(_hi(_iy>>1,_iV,_iX,_iY,_iP,_iN));return new T3(0,new T(function(){return B(_h1(_iQ,_iL,_iG,_iZ.a));}),_iZ.b,_iZ.c);}else{return new T3(0,_iG,_z,_iI);}}}else{var _j0=B(_hQ(_iy>>1,_iV,_iX,_iU,_iP,_iN));return new T3(0,new T(function(){return B(_h1(_iQ,_iL,_iG,_j0.a));}),_j0.b,_j0.c);}}}else{var _j1=B(_hS(_iy>>1,_iV,_iT,_iU,_iP,_iN));return new T3(0,new T(function(){return B(_h1(_iQ,_iL,_iG,_j1.a));}),_j1.b,_j1.c);}}}}},_j2=function(_j3,_j4,_j5,_j6,_j7){var _j8=E(_j7);if(!_j8._){var _j9=_j8.c,_ja=_j8.d,_jb=_j8.e,_jc=E(_j8.b),_jd=E(_jc.a);if(_j3>=_jd){if(_j3!=_jd){return new F(function(){return _eQ(_jc,_j9,_ja,B(_j2(_j3,_j4,_j5,_j6,_jb)));});}else{var _je=E(_jc.b);if(_j4>=_je){if(_j4!=_je){return new F(function(){return _eQ(_jc,_j9,_ja,B(_j2(_j3,_j4,_j5,_j6,_jb)));});}else{var _jf=E(_jc.c);if(_j5>=_jf){if(_j5!=_jf){return new F(function(){return _eQ(_jc,_j9,_ja,B(_j2(_j3,_j4,_j5,_j6,_jb)));});}else{return new T5(0,_j8.a,E(new T3(0,_j3,_j4,_j5)),_j6,E(_ja),E(_jb));}}else{return new F(function(){return _fH(_jc,_j9,B(_j2(_j3,_j4,_j5,_j6,_ja)),_jb);});}}}else{return new F(function(){return _fH(_jc,_j9,B(_j2(_j3,_j4,_j5,_j6,_ja)),_jb);});}}}else{return new F(function(){return _fH(_jc,_j9,B(_j2(_j3,_j4,_j5,_j6,_ja)),_jb);});}}else{return new T5(0,1,E(new T3(0,_j3,_j4,_j5)),_j6,E(_eL),E(_eL));}},_jg=function(_jh,_ji,_jj,_jk,_jl){var _jm=E(_jl);if(!_jm._){var _jn=_jm.c,_jo=_jm.d,_jp=_jm.e,_jq=E(_jm.b),_jr=E(_jq.a);if(_jh>=_jr){if(_jh!=_jr){return new F(function(){return _eQ(_jq,_jn,_jo,B(_jg(_jh,_ji,_jj,_jk,_jp)));});}else{var _js=E(_jq.b);if(_ji>=_js){if(_ji!=_js){return new F(function(){return _eQ(_jq,_jn,_jo,B(_jg(_jh,_ji,_jj,_jk,_jp)));});}else{var _jt=E(_jj),_ju=E(_jq.c);if(_jt>=_ju){if(_jt!=_ju){return new F(function(){return _eQ(_jq,_jn,_jo,B(_j2(_jh,_ji,_jt,_jk,_jp)));});}else{return new T5(0,_jm.a,E(new T3(0,_jh,_ji,_jt)),_jk,E(_jo),E(_jp));}}else{return new F(function(){return _fH(_jq,_jn,B(_j2(_jh,_ji,_jt,_jk,_jo)),_jp);});}}}else{return new F(function(){return _fH(_jq,_jn,B(_jg(_jh,_ji,_jj,_jk,_jo)),_jp);});}}}else{return new F(function(){return _fH(_jq,_jn,B(_jg(_jh,_ji,_jj,_jk,_jo)),_jp);});}}else{return new T5(0,1,E(new T3(0,_jh,_ji,_jj)),_jk,E(_eL),E(_eL));}},_jv=function(_jw,_jx,_jy,_jz,_jA){var _jB=E(_jA);if(!_jB._){var _jC=_jB.c,_jD=_jB.d,_jE=_jB.e,_jF=E(_jB.b),_jG=E(_jF.a);if(_jw>=_jG){if(_jw!=_jG){return new F(function(){return _eQ(_jF,_jC,_jD,B(_jv(_jw,_jx,_jy,_jz,_jE)));});}else{var _jH=E(_jx),_jI=E(_jF.b);if(_jH>=_jI){if(_jH!=_jI){return new F(function(){return _eQ(_jF,_jC,_jD,B(_jg(_jw,_jH,_jy,_jz,_jE)));});}else{var _jJ=E(_jy),_jK=E(_jF.c);if(_jJ>=_jK){if(_jJ!=_jK){return new F(function(){return _eQ(_jF,_jC,_jD,B(_j2(_jw,_jH,_jJ,_jz,_jE)));});}else{return new T5(0,_jB.a,E(new T3(0,_jw,_jH,_jJ)),_jz,E(_jD),E(_jE));}}else{return new F(function(){return _fH(_jF,_jC,B(_j2(_jw,_jH,_jJ,_jz,_jD)),_jE);});}}}else{return new F(function(){return _fH(_jF,_jC,B(_jg(_jw,_jH,_jy,_jz,_jD)),_jE);});}}}else{return new F(function(){return _fH(_jF,_jC,B(_jv(_jw,_jx,_jy,_jz,_jD)),_jE);});}}else{return new T5(0,1,E(new T3(0,_jw,_jx,_jy)),_jz,E(_eL),E(_eL));}},_jL=function(_jM,_jN,_jO,_jP,_jQ){var _jR=E(_jQ);if(!_jR._){var _jS=_jR.c,_jT=_jR.d,_jU=_jR.e,_jV=E(_jR.b),_jW=E(_jM),_jX=E(_jV.a);if(_jW>=_jX){if(_jW!=_jX){return new F(function(){return _eQ(_jV,_jS,_jT,B(_jv(_jW,_jN,_jO,_jP,_jU)));});}else{var _jY=E(_jN),_jZ=E(_jV.b);if(_jY>=_jZ){if(_jY!=_jZ){return new F(function(){return _eQ(_jV,_jS,_jT,B(_jg(_jW,_jY,_jO,_jP,_jU)));});}else{var _k0=E(_jO),_k1=E(_jV.c);if(_k0>=_k1){if(_k0!=_k1){return new F(function(){return _eQ(_jV,_jS,_jT,B(_j2(_jW,_jY,_k0,_jP,_jU)));});}else{return new T5(0,_jR.a,E(new T3(0,_jW,_jY,_k0)),_jP,E(_jT),E(_jU));}}else{return new F(function(){return _fH(_jV,_jS,B(_j2(_jW,_jY,_k0,_jP,_jT)),_jU);});}}}else{return new F(function(){return _fH(_jV,_jS,B(_jg(_jW,_jY,_jO,_jP,_jT)),_jU);});}}}else{return new F(function(){return _fH(_jV,_jS,B(_jv(_jW,_jN,_jO,_jP,_jT)),_jU);});}}else{return new T5(0,1,E(new T3(0,_jM,_jN,_jO)),_jP,E(_eL),E(_eL));}},_k2=function(_k3,_k4){while(1){var _k5=E(_k4);if(!_k5._){return E(_k3);}else{var _k6=E(_k5.a),_k7=E(_k6.a),_k8=B(_jL(_k7.a,_k7.b,_k7.c,_k6.b,_k3));_k3=_k8;_k4=_k5.b;continue;}}},_k9=function(_ka,_kb,_kc,_kd,_ke,_kf){return new F(function(){return _k2(B(_jL(_kb,_kc,_kd,_ke,_ka)),_kf);});},_kg=function(_kh,_ki,_kj){var _kk=E(_ki),_kl=E(_kk.a);return new F(function(){return _k2(B(_jL(_kl.a,_kl.b,_kl.c,_kk.b,_kh)),_kj);});},_km=function(_kn,_ko,_kp){var _kq=E(_kp);if(!_kq._){return E(_ko);}else{var _kr=E(_kq.a),_ks=_kr.a,_kt=_kr.b,_ku=E(_kq.b);if(!_ku._){return new F(function(){return _fy(_ks,_kt,_ko);});}else{var _kv=E(_ku.a),_kw=E(_ks),_kx=_kw.b,_ky=_kw.c,_kz=E(_kw.a),_kA=E(_kv.a),_kB=_kA.b,_kC=_kA.c,_kD=E(_kA.a),_kE=function(_kF){var _kG=B(_hS(_kn,_kD,_kB,_kC,_kv.b,_ku.b)),_kH=_kG.a,_kI=E(_kG.c);if(!_kI._){return new F(function(){return _km(_kn<<1,B(_h1(_kw,_kt,_ko,_kH)),_kG.b);});}else{return new F(function(){return _kg(B(_h1(_kw,_kt,_ko,_kH)),_kI.a,_kI.b);});}};if(_kz>=_kD){if(_kz!=_kD){return new F(function(){return _k9(_ko,_kz,_kx,_ky,_kt,_ku);});}else{var _kJ=E(_kx),_kK=E(_kB);if(_kJ>=_kK){if(_kJ!=_kK){return new F(function(){return _k9(_ko,_kz,_kJ,_ky,_kt,_ku);});}else{var _kL=E(_ky);if(_kL<E(_kC)){return new F(function(){return _kE(_);});}else{return new F(function(){return _k9(_ko,_kz,_kJ,_kL,_kt,_ku);});}}}else{return new F(function(){return _kE(_);});}}}else{return new F(function(){return _kE(_);});}}}},_kM=function(_kN,_kO,_kP,_kQ,_kR,_kS,_kT){var _kU=E(_kT);if(!_kU._){return new F(function(){return _fy(new T3(0,_kP,_kQ,_kR),_kS,_kO);});}else{var _kV=E(_kU.a),_kW=E(_kV.a),_kX=_kW.b,_kY=_kW.c,_kZ=E(_kW.a),_l0=function(_l1){var _l2=B(_hS(_kN,_kZ,_kX,_kY,_kV.b,_kU.b)),_l3=_l2.a,_l4=E(_l2.c);if(!_l4._){return new F(function(){return _km(_kN<<1,B(_h1(new T3(0,_kP,_kQ,_kR),_kS,_kO,_l3)),_l2.b);});}else{return new F(function(){return _kg(B(_h1(new T3(0,_kP,_kQ,_kR),_kS,_kO,_l3)),_l4.a,_l4.b);});}};if(_kP>=_kZ){if(_kP!=_kZ){return new F(function(){return _k9(_kO,_kP,_kQ,_kR,_kS,_kU);});}else{var _l5=E(_kX);if(_kQ>=_l5){if(_kQ!=_l5){return new F(function(){return _k9(_kO,_kP,_kQ,_kR,_kS,_kU);});}else{var _l6=E(_kR);if(_l6<E(_kY)){return new F(function(){return _l0(_);});}else{return new F(function(){return _k9(_kO,_kP,_kQ,_l6,_kS,_kU);});}}}else{return new F(function(){return _l0(_);});}}}else{return new F(function(){return _l0(_);});}}},_l7=function(_l8,_l9,_la,_lb,_lc,_ld,_le){var _lf=E(_le);if(!_lf._){return new F(function(){return _fy(new T3(0,_la,_lb,_lc),_ld,_l9);});}else{var _lg=E(_lf.a),_lh=E(_lg.a),_li=_lh.b,_lj=_lh.c,_lk=E(_lh.a),_ll=function(_lm){var _ln=B(_hS(_l8,_lk,_li,_lj,_lg.b,_lf.b)),_lo=_ln.a,_lp=E(_ln.c);if(!_lp._){return new F(function(){return _km(_l8<<1,B(_h1(new T3(0,_la,_lb,_lc),_ld,_l9,_lo)),_ln.b);});}else{return new F(function(){return _kg(B(_h1(new T3(0,_la,_lb,_lc),_ld,_l9,_lo)),_lp.a,_lp.b);});}};if(_la>=_lk){if(_la!=_lk){return new F(function(){return _k9(_l9,_la,_lb,_lc,_ld,_lf);});}else{var _lq=E(_lb),_lr=E(_li);if(_lq>=_lr){if(_lq!=_lr){return new F(function(){return _k9(_l9,_la,_lq,_lc,_ld,_lf);});}else{var _ls=E(_lc);if(_ls<E(_lj)){return new F(function(){return _ll(_);});}else{return new F(function(){return _k9(_l9,_la,_lq,_ls,_ld,_lf);});}}}else{return new F(function(){return _ll(_);});}}}else{return new F(function(){return _ll(_);});}}},_lt=function(_lu,_lv,_lw,_lx,_ly,_lz,_lA){var _lB=E(_lA);if(!_lB._){return new F(function(){return _fy(new T3(0,_lw,_lx,_ly),_lz,_lv);});}else{var _lC=E(_lB.a),_lD=E(_lC.a),_lE=_lD.b,_lF=_lD.c,_lG=E(_lD.a),_lH=function(_lI){var _lJ=B(_hS(_lu,_lG,_lE,_lF,_lC.b,_lB.b)),_lK=_lJ.a,_lL=E(_lJ.c);if(!_lL._){return new F(function(){return _km(_lu<<1,B(_h1(new T3(0,_lw,_lx,_ly),_lz,_lv,_lK)),_lJ.b);});}else{return new F(function(){return _kg(B(_h1(new T3(0,_lw,_lx,_ly),_lz,_lv,_lK)),_lL.a,_lL.b);});}};if(_lw>=_lG){if(_lw!=_lG){return new F(function(){return _k9(_lv,_lw,_lx,_ly,_lz,_lB);});}else{var _lM=E(_lE);if(_lx>=_lM){if(_lx!=_lM){return new F(function(){return _k9(_lv,_lw,_lx,_ly,_lz,_lB);});}else{if(_ly<E(_lF)){return new F(function(){return _lH(_);});}else{return new F(function(){return _k9(_lv,_lw,_lx,_ly,_lz,_lB);});}}}else{return new F(function(){return _lH(_);});}}}else{return new F(function(){return _lH(_);});}}},_lN=function(_lO){var _lP=E(_lO);if(!_lP._){return new T0(1);}else{var _lQ=E(_lP.a),_lR=_lQ.a,_lS=_lQ.b,_lT=E(_lP.b);if(!_lT._){return new T5(0,1,E(_lR),_lS,E(_eL),E(_eL));}else{var _lU=_lT.b,_lV=E(_lT.a),_lW=_lV.b,_lX=E(_lR),_lY=E(_lX.a),_lZ=E(_lV.a),_m0=_lZ.b,_m1=_lZ.c,_m2=E(_lZ.a);if(_lY>=_m2){if(_lY!=_m2){return new F(function(){return _k9(new T5(0,1,E(_lX),_lS,E(_eL),E(_eL)),_m2,_m0,_m1,_lW,_lU);});}else{var _m3=E(_lX.b),_m4=E(_m0);if(_m3>=_m4){if(_m3!=_m4){return new F(function(){return _k9(new T5(0,1,E(_lX),_lS,E(_eL),E(_eL)),_m2,_m4,_m1,_lW,_lU);});}else{var _m5=E(_m1);if(E(_lX.c)<_m5){return new F(function(){return _lt(1,new T5(0,1,E(_lX),_lS,E(_eL),E(_eL)),_m2,_m4,_m5,_lW,_lU);});}else{return new F(function(){return _k9(new T5(0,1,E(_lX),_lS,E(_eL),E(_eL)),_m2,_m4,_m5,_lW,_lU);});}}}else{return new F(function(){return _kM(1,new T5(0,1,E(_lX),_lS,E(_eL),E(_eL)),_m2,_m4,_m1,_lW,_lU);});}}}else{return new F(function(){return _l7(1,new T5(0,1,E(_lX),_lS,E(_eL),E(_eL)),_m2,_m0,_m1,_lW,_lU);});}}}},_m6=function(_m7,_m8){var _m9=function(_ma,_mb){while(1){var _mc=B((function(_md,_me){var _mf=E(_me);if(!_mf._){_ma=new T2(1,new T2(0,new T(function(){return B(A1(_m7,_mf.b));}),_mf.c),new T(function(){return B(_m9(_md,_mf.e));}));_mb=_mf.d;return __continue;}else{return E(_md);}})(_ma,_mb));if(_mc!=__continue){return _mc;}}};return new F(function(){return _lN(B(_m9(_z,_m8)));});},_mg=__Z,_mh=function(_mi){return E(E(_mi).b);},_mj=function(_mk){return E(E(_mk).c);},_ml=function(_mm){return new T3(0,new T(function(){return E(E(_mm).a)+1|0;}),new T(function(){return B(_mh(_mm));}),new T(function(){return B(_mj(_mm));}));},_mn=function(_mo,_mp,_mq,_mr,_ms){var _mt=E(_ms);if(!_mt._){var _mu=new T(function(){var _mv=B(_mn(_mt.a,_mt.b,_mt.c,_mt.d,_mt.e));return new T2(0,_mv.a,_mv.b);});return new T2(0,new T(function(){return E(E(_mu).a);}),new T(function(){return B(_fH(_mp,_mq,_mr,E(_mu).b));}));}else{return new T2(0,new T2(0,_mp,_mq),_mr);}},_mw=function(_mx,_my,_mz,_mA,_mB){var _mC=E(_mA);if(!_mC._){var _mD=new T(function(){var _mE=B(_mw(_mC.a,_mC.b,_mC.c,_mC.d,_mC.e));return new T2(0,_mE.a,_mE.b);});return new T2(0,new T(function(){return E(E(_mD).a);}),new T(function(){return B(_eQ(_my,_mz,E(_mD).b,_mB));}));}else{return new T2(0,new T2(0,_my,_mz),_mB);}},_mF=function(_mG,_mH){var _mI=E(_mG);if(!_mI._){var _mJ=_mI.a,_mK=E(_mH);if(!_mK._){var _mL=_mK.a;if(_mJ<=_mL){var _mM=B(_mw(_mL,_mK.b,_mK.c,_mK.d,_mK.e)),_mN=E(_mM.a);return new F(function(){return _fH(_mN.a,_mN.b,_mI,_mM.b);});}else{var _mO=B(_mn(_mJ,_mI.b,_mI.c,_mI.d,_mI.e)),_mP=E(_mO.a);return new F(function(){return _eQ(_mP.a,_mP.b,_mO.b,_mK);});}}else{return E(_mI);}}else{return E(_mH);}},_mQ=function(_mR,_mS,_mT,_mU,_mV,_mW){var _mX=E(_mR);if(!_mX._){var _mY=_mX.a,_mZ=_mX.b,_n0=_mX.c,_n1=_mX.d,_n2=_mX.e;if((imul(3,_mY)|0)>=_mS){if((imul(3,_mS)|0)>=_mY){return new F(function(){return _mF(_mX,new T5(0,_mS,E(_mT),_mU,E(_mV),E(_mW)));});}else{return new F(function(){return _eQ(_mZ,_n0,_n1,B(_mQ(_n2,_mS,_mT,_mU,_mV,_mW)));});}}else{return new F(function(){return _fH(_mT,_mU,B(_n3(_mY,_mZ,_n0,_n1,_n2,_mV)),_mW);});}}else{return new T5(0,_mS,E(_mT),_mU,E(_mV),E(_mW));}},_n3=function(_n4,_n5,_n6,_n7,_n8,_n9){var _na=E(_n9);if(!_na._){var _nb=_na.a,_nc=_na.b,_nd=_na.c,_ne=_na.d,_nf=_na.e;if((imul(3,_n4)|0)>=_nb){if((imul(3,_nb)|0)>=_n4){return new F(function(){return _mF(new T5(0,_n4,E(_n5),_n6,E(_n7),E(_n8)),_na);});}else{return new F(function(){return _eQ(_n5,_n6,_n7,B(_mQ(_n8,_nb,_nc,_nd,_ne,_nf)));});}}else{return new F(function(){return _fH(_nc,_nd,B(_n3(_n4,_n5,_n6,_n7,_n8,_ne)),_nf);});}}else{return new T5(0,_n4,E(_n5),_n6,E(_n7),E(_n8));}},_ng=function(_nh,_ni){var _nj=E(_nh);if(!_nj._){var _nk=_nj.a,_nl=_nj.b,_nm=_nj.c,_nn=_nj.d,_no=_nj.e,_np=E(_ni);if(!_np._){var _nq=_np.a,_nr=_np.b,_ns=_np.c,_nt=_np.d,_nu=_np.e;if((imul(3,_nk)|0)>=_nq){if((imul(3,_nq)|0)>=_nk){return new F(function(){return _mF(_nj,_np);});}else{return new F(function(){return _eQ(_nl,_nm,_nn,B(_mQ(_no,_nq,_nr,_ns,_nt,_nu)));});}}else{return new F(function(){return _fH(_nr,_ns,B(_n3(_nk,_nl,_nm,_nn,_no,_nt)),_nu);});}}else{return E(_nj);}}else{return E(_ni);}},_nv=function(_nw,_nx){var _ny=E(_nx);if(!_ny._){var _nz=_ny.b,_nA=_ny.c,_nB=_ny.d,_nC=_ny.e;if(!B(A2(_nw,_nz,_nA))){return new F(function(){return _ng(B(_nv(_nw,_nB)),B(_nv(_nw,_nC)));});}else{return new F(function(){return _h1(_nz,_nA,B(_nv(_nw,_nB)),B(_nv(_nw,_nC)));});}}else{return new T0(1);}},_nD=true,_nE=function(_nF){var _nG=E(_nF);return (_nG._==0)?E(_nG.a):E(_66);},_nH=new T(function(){return B(_63("kind"));}),_nI=function(_nJ){var _nK=E(_nJ);return (_nK._==0)?E(_nK.b):E(_nH);},_nL=function(_nM,_nN){return new T5(0,new T(function(){return B(_nE(_nN));}),new T(function(){return B(_nI(_nN));}),_nD,_2u,new T1(1,_nM));},_nO=new T(function(){return B(_63("previousLocation"));}),_nP=function(_nQ){var _nR=E(_nQ);return (_nR._==0)?E(_nR.e):E(_nO);},_nS=function(_nT,_nU){return new T5(0,new T(function(){return B(_nE(_nU));}),new T(function(){return B(_nI(_nU));}),_nD,new T1(1,new T(function(){return B(_ml(_nT));})),new T(function(){return B(_nP(_nU));}));},_nV=new T(function(){return B(_63("nextLocation"));}),_nW=function(_nX,_nY){var _nZ=E(_nY);return (_nZ._==0)?(E(_nZ.d)._==0)?true:false:E(_nV);},_o0=function(_o1,_o2){var _o3=E(_o2);if(!_o3._){var _o4=_o3.b;return new T5(0,_o3.a,E(_o4),new T(function(){return B(A2(_o1,_o4,_o3.c));}),E(B(_o0(_o1,_o3.d))),E(B(_o0(_o1,_o3.e))));}else{return new T0(1);}},_o5=function(_o6){return E(E(_o6).b);},_o7=function(_o8,_o9,_oa){var _ob=E(_o9);if(!_ob._){return E(_oa);}else{var _oc=function(_od,_oe){while(1){var _of=E(_oe);if(!_of._){var _og=_of.b,_oh=_of.e;switch(B(A3(_o5,_o8,_od,_og))){case 0:return new F(function(){return _h1(_og,_of.c,B(_oc(_od,_of.d)),_oh);});break;case 1:return E(_oh);default:_oe=_oh;continue;}}else{return new T0(1);}}};return new F(function(){return _oc(_ob.a,_oa);});}},_oi=function(_oj,_ok,_ol){var _om=E(_ok);if(!_om._){return E(_ol);}else{var _on=function(_oo,_op){while(1){var _oq=E(_op);if(!_oq._){var _or=_oq.b,_os=_oq.d;switch(B(A3(_o5,_oj,_or,_oo))){case 0:return new F(function(){return _h1(_or,_oq.c,_os,B(_on(_oo,_oq.e)));});break;case 1:return E(_os);default:_op=_os;continue;}}else{return new T0(1);}}};return new F(function(){return _on(_om.a,_ol);});}},_ot=function(_ou,_ov,_ow,_ox){var _oy=E(_ov),_oz=E(_ox);if(!_oz._){var _oA=_oz.b,_oB=_oz.c,_oC=_oz.d,_oD=_oz.e;switch(B(A3(_o5,_ou,_oy,_oA))){case 0:return new F(function(){return _fH(_oA,_oB,B(_ot(_ou,_oy,_ow,_oC)),_oD);});break;case 1:return E(_oz);default:return new F(function(){return _eQ(_oA,_oB,_oC,B(_ot(_ou,_oy,_ow,_oD)));});}}else{return new T5(0,1,E(_oy),_ow,E(_eL),E(_eL));}},_oE=function(_oF,_oG,_oH,_oI){return new F(function(){return _ot(_oF,_oG,_oH,_oI);});},_oJ=function(_oK){return E(E(_oK).d);},_oL=function(_oM){return E(E(_oM).f);},_oN=function(_oO,_oP,_oQ,_oR){var _oS=E(_oP);if(!_oS._){var _oT=E(_oQ);if(!_oT._){return E(_oR);}else{var _oU=function(_oV,_oW){while(1){var _oX=E(_oW);if(!_oX._){if(!B(A3(_oL,_oO,_oX.b,_oV))){return E(_oX);}else{_oW=_oX.d;continue;}}else{return new T0(1);}}};return new F(function(){return _oU(_oT.a,_oR);});}}else{var _oY=_oS.a,_oZ=E(_oQ);if(!_oZ._){var _p0=function(_p1,_p2){while(1){var _p3=E(_p2);if(!_p3._){if(!B(A3(_oJ,_oO,_p3.b,_p1))){return E(_p3);}else{_p2=_p3.e;continue;}}else{return new T0(1);}}};return new F(function(){return _p0(_oY,_oR);});}else{var _p4=function(_p5,_p6,_p7){while(1){var _p8=E(_p7);if(!_p8._){var _p9=_p8.b;if(!B(A3(_oJ,_oO,_p9,_p5))){if(!B(A3(_oL,_oO,_p9,_p6))){return E(_p8);}else{_p7=_p8.d;continue;}}else{_p7=_p8.e;continue;}}else{return new T0(1);}}};return new F(function(){return _p4(_oY,_oZ.a,_oR);});}}},_pa=function(_pb,_pc,_pd,_pe,_pf){var _pg=E(_pf);if(!_pg._){var _ph=_pg.b,_pi=_pg.c,_pj=_pg.d,_pk=_pg.e,_pl=E(_pe);if(!_pl._){var _pm=_pl.b,_pn=function(_po){var _pp=new T1(1,E(_pm));return new F(function(){return _h1(_pm,_pl.c,B(_pa(_pb,_pc,_pp,_pl.d,B(_oN(_pb,_pc,_pp,_pg)))),B(_pa(_pb,_pp,_pd,_pl.e,B(_oN(_pb,_pp,_pd,_pg)))));});};if(!E(_pj)._){return new F(function(){return _pn(_);});}else{if(!E(_pk)._){return new F(function(){return _pn(_);});}else{return new F(function(){return _oE(_pb,_ph,_pi,_pl);});}}}else{return new F(function(){return _h1(_ph,_pi,B(_o7(_pb,_pc,_pj)),B(_oi(_pb,_pd,_pk)));});}}else{return E(_pe);}},_pq=function(_pr,_ps,_pt,_pu,_pv,_pw,_px,_py,_pz,_pA,_pB,_pC,_pD){var _pE=function(_pF){var _pG=new T1(1,E(_pv));return new F(function(){return _h1(_pv,_pw,B(_pa(_pr,_ps,_pG,_px,B(_oN(_pr,_ps,_pG,new T5(0,_pz,E(_pA),_pB,E(_pC),E(_pD)))))),B(_pa(_pr,_pG,_pt,_py,B(_oN(_pr,_pG,_pt,new T5(0,_pz,E(_pA),_pB,E(_pC),E(_pD)))))));});};if(!E(_pC)._){return new F(function(){return _pE(_);});}else{if(!E(_pD)._){return new F(function(){return _pE(_);});}else{return new F(function(){return _oE(_pr,_pA,_pB,new T5(0,_pu,E(_pv),_pw,E(_px),E(_py)));});}}},_pH=function(_pI){var _pJ=B(_nv(_nW,_pI)),_pK=function(_pL,_pM,_pN,_pO,_pP,_pQ){var _pR=E(_pI);if(!_pR._){return new F(function(){return _pq(_eK,_mg,_mg,_pL,_pM,_pN,_pO,_pP,_pR.a,_pR.b,_pR.c,_pR.d,_pR.e);});}else{return E(_pQ);}},_pS=B(_m6(_ml,B(_o0(_nL,_pJ))));if(!_pS._){var _pT=_pS.a,_pU=_pS.b,_pV=_pS.c,_pW=_pS.d,_pX=_pS.e,_pY=B(_o0(_nS,_pJ));if(!_pY._){var _pZ=B(_pq(_eK,_mg,_mg,_pT,_pU,_pV,_pW,_pX,_pY.a,_pY.b,_pY.c,_pY.d,_pY.e));if(!_pZ._){return new F(function(){return _pK(_pZ.a,_pZ.b,_pZ.c,_pZ.d,_pZ.e,_pZ);});}else{return E(_pI);}}else{return new F(function(){return _pK(_pT,_pU,_pV,_pW,_pX,_pS);});}}else{var _q0=B(_o0(_nS,_pJ));if(!_q0._){return new F(function(){return _pK(_q0.a,_q0.b,_q0.c,_q0.d,_q0.e,_q0);});}else{return E(_pI);}}},_q1=function(_q2,_q3,_q4,_q5){while(1){var _q6=E(_q5);if(!_q6._){var _q7=_q6.d,_q8=_q6.e,_q9=E(_q6.b),_qa=E(_q9.a);if(_q2>=_qa){if(_q2!=_qa){_q5=_q8;continue;}else{var _qb=E(_q9.b);if(_q3>=_qb){if(_q3!=_qb){_q5=_q8;continue;}else{var _qc=E(_q9.c);if(_q4>=_qc){if(_q4!=_qc){_q5=_q8;continue;}else{return new T1(1,_q6.c);}}else{_q5=_q7;continue;}}}else{_q5=_q7;continue;}}}else{_q5=_q7;continue;}}else{return __Z;}}},_qd=function(_qe,_qf,_qg,_qh){while(1){var _qi=E(_qh);if(!_qi._){var _qj=_qi.d,_qk=_qi.e,_ql=E(_qi.b),_qm=E(_ql.a);if(_qe>=_qm){if(_qe!=_qm){_qh=_qk;continue;}else{var _qn=E(_ql.b);if(_qf>=_qn){if(_qf!=_qn){_qh=_qk;continue;}else{var _qo=E(_qg),_qp=E(_ql.c);if(_qo>=_qp){if(_qo!=_qp){return new F(function(){return _q1(_qe,_qf,_qo,_qk);});}else{return new T1(1,_qi.c);}}else{return new F(function(){return _q1(_qe,_qf,_qo,_qj);});}}}else{_qh=_qj;continue;}}}else{_qh=_qj;continue;}}else{return __Z;}}},_qq=function(_qr,_qs,_qt,_qu){while(1){var _qv=E(_qu);if(!_qv._){var _qw=_qv.d,_qx=_qv.e,_qy=E(_qv.b),_qz=E(_qy.a);if(_qr>=_qz){if(_qr!=_qz){_qu=_qx;continue;}else{var _qA=E(_qs),_qB=E(_qy.b);if(_qA>=_qB){if(_qA!=_qB){return new F(function(){return _qd(_qr,_qA,_qt,_qx);});}else{var _qC=E(_qt),_qD=E(_qy.c);if(_qC>=_qD){if(_qC!=_qD){return new F(function(){return _q1(_qr,_qA,_qC,_qx);});}else{return new T1(1,_qv.c);}}else{return new F(function(){return _q1(_qr,_qA,_qC,_qw);});}}}else{return new F(function(){return _qd(_qr,_qA,_qt,_qw);});}}}else{_qu=_qw;continue;}}else{return __Z;}}},_qE=function(_qF,_qG,_qH,_qI){var _qJ=E(_qI);if(!_qJ._){var _qK=_qJ.d,_qL=_qJ.e,_qM=E(_qJ.b),_qN=E(_qF),_qO=E(_qM.a);if(_qN>=_qO){if(_qN!=_qO){return new F(function(){return _qq(_qN,_qG,_qH,_qL);});}else{var _qP=E(_qG),_qQ=E(_qM.b);if(_qP>=_qQ){if(_qP!=_qQ){return new F(function(){return _qd(_qN,_qP,_qH,_qL);});}else{var _qR=E(_qH),_qS=E(_qM.c);if(_qR>=_qS){if(_qR!=_qS){return new F(function(){return _q1(_qN,_qP,_qR,_qL);});}else{return new T1(1,_qJ.c);}}else{return new F(function(){return _q1(_qN,_qP,_qR,_qK);});}}}else{return new F(function(){return _qd(_qN,_qP,_qH,_qK);});}}}else{return new F(function(){return _qq(_qN,_qG,_qH,_qK);});}}else{return __Z;}},_qT=function(_qU){return false;},_qV=function(_qW,_qX,_qY,_qZ){var _r0=E(_qZ);if(!_r0._){var _r1=_r0.c,_r2=_r0.d,_r3=_r0.e,_r4=E(_r0.b),_r5=E(_r4.a);if(_qW>=_r5){if(_qW!=_r5){return new F(function(){return _fH(_r4,_r1,_r2,B(_qV(_qW,_qX,_qY,_r3)));});}else{var _r6=E(_r4.b);if(_qX>=_r6){if(_qX!=_r6){return new F(function(){return _fH(_r4,_r1,_r2,B(_qV(_qW,_qX,_qY,_r3)));});}else{var _r7=E(_r4.c);if(_qY>=_r7){if(_qY!=_r7){return new F(function(){return _fH(_r4,_r1,_r2,B(_qV(_qW,_qX,_qY,_r3)));});}else{return new F(function(){return _mF(_r2,_r3);});}}else{return new F(function(){return _eQ(_r4,_r1,B(_qV(_qW,_qX,_qY,_r2)),_r3);});}}}else{return new F(function(){return _eQ(_r4,_r1,B(_qV(_qW,_qX,_qY,_r2)),_r3);});}}}else{return new F(function(){return _eQ(_r4,_r1,B(_qV(_qW,_qX,_qY,_r2)),_r3);});}}else{return new T0(1);}},_r8=function(_r9,_ra,_rb,_rc){var _rd=E(_rc);if(!_rd._){var _re=_rd.c,_rf=_rd.d,_rg=_rd.e,_rh=E(_rd.b),_ri=E(_rh.a);if(_r9>=_ri){if(_r9!=_ri){return new F(function(){return _fH(_rh,_re,_rf,B(_r8(_r9,_ra,_rb,_rg)));});}else{var _rj=E(_rh.b);if(_ra>=_rj){if(_ra!=_rj){return new F(function(){return _fH(_rh,_re,_rf,B(_r8(_r9,_ra,_rb,_rg)));});}else{var _rk=E(_rb),_rl=E(_rh.c);if(_rk>=_rl){if(_rk!=_rl){return new F(function(){return _fH(_rh,_re,_rf,B(_qV(_r9,_ra,_rk,_rg)));});}else{return new F(function(){return _mF(_rf,_rg);});}}else{return new F(function(){return _eQ(_rh,_re,B(_qV(_r9,_ra,_rk,_rf)),_rg);});}}}else{return new F(function(){return _eQ(_rh,_re,B(_r8(_r9,_ra,_rb,_rf)),_rg);});}}}else{return new F(function(){return _eQ(_rh,_re,B(_r8(_r9,_ra,_rb,_rf)),_rg);});}}else{return new T0(1);}},_rm=function(_rn,_ro,_rp,_rq){var _rr=E(_rq);if(!_rr._){var _rs=_rr.c,_rt=_rr.d,_ru=_rr.e,_rv=E(_rr.b),_rw=E(_rv.a);if(_rn>=_rw){if(_rn!=_rw){return new F(function(){return _fH(_rv,_rs,_rt,B(_rm(_rn,_ro,_rp,_ru)));});}else{var _rx=E(_ro),_ry=E(_rv.b);if(_rx>=_ry){if(_rx!=_ry){return new F(function(){return _fH(_rv,_rs,_rt,B(_r8(_rn,_rx,_rp,_ru)));});}else{var _rz=E(_rp),_rA=E(_rv.c);if(_rz>=_rA){if(_rz!=_rA){return new F(function(){return _fH(_rv,_rs,_rt,B(_qV(_rn,_rx,_rz,_ru)));});}else{return new F(function(){return _mF(_rt,_ru);});}}else{return new F(function(){return _eQ(_rv,_rs,B(_qV(_rn,_rx,_rz,_rt)),_ru);});}}}else{return new F(function(){return _eQ(_rv,_rs,B(_r8(_rn,_rx,_rp,_rt)),_ru);});}}}else{return new F(function(){return _eQ(_rv,_rs,B(_rm(_rn,_ro,_rp,_rt)),_ru);});}}else{return new T0(1);}},_rB=function(_rC,_rD,_rE,_rF){var _rG=E(_rF);if(!_rG._){var _rH=_rG.c,_rI=_rG.d,_rJ=_rG.e,_rK=E(_rG.b),_rL=E(_rC),_rM=E(_rK.a);if(_rL>=_rM){if(_rL!=_rM){return new F(function(){return _fH(_rK,_rH,_rI,B(_rm(_rL,_rD,_rE,_rJ)));});}else{var _rN=E(_rD),_rO=E(_rK.b);if(_rN>=_rO){if(_rN!=_rO){return new F(function(){return _fH(_rK,_rH,_rI,B(_r8(_rL,_rN,_rE,_rJ)));});}else{var _rP=E(_rE),_rQ=E(_rK.c);if(_rP>=_rQ){if(_rP!=_rQ){return new F(function(){return _fH(_rK,_rH,_rI,B(_qV(_rL,_rN,_rP,_rJ)));});}else{return new F(function(){return _mF(_rI,_rJ);});}}else{return new F(function(){return _eQ(_rK,_rH,B(_qV(_rL,_rN,_rP,_rI)),_rJ);});}}}else{return new F(function(){return _eQ(_rK,_rH,B(_r8(_rL,_rN,_rE,_rI)),_rJ);});}}}else{return new F(function(){return _eQ(_rK,_rH,B(_rm(_rL,_rD,_rE,_rI)),_rJ);});}}else{return new T0(1);}},_rR=function(_rS,_rT,_rU){while(1){var _rV=E(_rT);if(!_rV._){return E(_rU);}else{var _rW=E(_rV.a),_rX=_rW.a,_rY=_rW.b,_rZ=_rW.c,_s0=B(_qE(_rX,_rY,_rZ,_rU));if(!_s0._){return new F(function(){return _rB(_rX,_rY,_rZ,_rU);});}else{var _s1=B(A1(_rS,_s0.a)),_s2=B(_rB(_rX,_rY,_rZ,_rU));_rT=_s1;_rU=_s2;continue;}}}},_s3=function(_s4,_s5,_s6,_s7,_s8){var _s9=B(_qE(_s5,_s6,_s7,_s8));if(!_s9._){return new F(function(){return _rB(_s5,_s6,_s7,_s8);});}else{return new F(function(){return _rR(_s4,B(A1(_s4,_s9.a)),B(_rB(_s5,_s6,_s7,_s8)));});}},_sa=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_sb=new T(function(){return B(err(_sa));}),_sc=function(_sd){var _se=E(_sd);return (_se._==0)?E(_sb):E(_se.a);},_sf=function(_sg,_sh,_si,_sj){while(1){var _sk=B((function(_sl,_sm,_sn,_so){var _sp=E(_sn);if(!_sp._){return E(_so);}else{var _sq=_sp.a,_sr=new T(function(){var _ss=E(_sq);return B(_qE(_ss.a,_ss.b,_ss.c,_so));});if(!B(A1(_sm,new T(function(){return B(_sc(_sr));})))){var _st=E(_sr);if(!_st._){var _su=E(_sq);return new F(function(){return _rB(_su.a,_su.b,_su.c,_so);});}else{var _sv=E(_sq),_sw=_sl,_sx=_sm,_sy=B(A1(_sl,_st.a)),_sz=B(_rB(_sv.a,_sv.b,_sv.c,_so));_sg=_sw;_sh=_sx;_si=_sy;_sj=_sz;return __continue;}}else{return E(_so);}}})(_sg,_sh,_si,_sj));if(_sk!=__continue){return _sk;}}},_sA=new T(function(){return B(_63("isStop"));}),_sB=function(_sC){var _sD=E(_sC);return (_sD._==0)?E(_sD.c):E(_sA);},_sE=function(_sF){var _sG=E(_sF);return (_sG._==0)?E(_sG.d):E(_nV);},_sH=function(_sI,_sJ,_sK,_sL){var _sM=B(_qE(_sI,_sJ,_sK,_sL));if(!_sM._){return new F(function(){return _s3(_sE,_sI,_sJ,_sK,_sL);});}else{var _sN=E(_sM.a);if(!_sN._){return new F(function(){return _s3(_sE,_sI,_sJ,_sK,B(_sf(_nP,new T(function(){var _sO=B(_qE(_sI,_sJ,_sK,_sL));if(!_sO._){return E(_qT);}else{var _sP=E(_sO.a);if(!_sP._){if(!E(_sP.c)){return E(_qT);}else{return E(_sB);}}else{return E(_sA);}}}),_sN.e,_sL)));});}else{return E(_nO);}}},_sQ=function(_sR,_sS){var _sT=E(_sR);return new F(function(){return _sH(_sT.a,_sT.b,_sT.c,_sS);});},_sU=function(_sV){return (E(_sV)==0)?1:0;},_sW=function(_sX,_sY,_sZ,_t0,_t1){var _t2=E(_t1);if(!_t2._){var _t3=_t2.c,_t4=_t2.d,_t5=_t2.e,_t6=E(_t2.b),_t7=E(_t6.a);if(_sX>=_t7){if(_sX!=_t7){return new F(function(){return _eQ(_t6,_t3,_t4,B(_sW(_sX,_sY,_sZ,_t0,_t5)));});}else{var _t8=E(_t6.b);if(_sY>=_t8){if(_sY!=_t8){return new F(function(){return _eQ(_t6,_t3,_t4,B(_sW(_sX,_sY,_sZ,_t0,_t5)));});}else{var _t9=E(_t6.c);if(_sZ>=_t9){if(_sZ!=_t9){return new F(function(){return _eQ(_t6,_t3,_t4,B(_sW(_sX,_sY,_sZ,_t0,_t5)));});}else{return new T5(0,_t2.a,E(new T3(0,_sX,_sY,_sZ)),_t0,E(_t4),E(_t5));}}else{return new F(function(){return _fH(_t6,_t3,B(_sW(_sX,_sY,_sZ,_t0,_t4)),_t5);});}}}else{return new F(function(){return _fH(_t6,_t3,B(_sW(_sX,_sY,_sZ,_t0,_t4)),_t5);});}}}else{return new F(function(){return _fH(_t6,_t3,B(_sW(_sX,_sY,_sZ,_t0,_t4)),_t5);});}}else{return new T5(0,1,E(new T3(0,_sX,_sY,_sZ)),_t0,E(_eL),E(_eL));}},_ta=function(_tb,_tc,_td,_te,_tf){var _tg=E(_tf);if(!_tg._){var _th=_tg.c,_ti=_tg.d,_tj=_tg.e,_tk=E(_tg.b),_tl=E(_tk.a);if(_tb>=_tl){if(_tb!=_tl){return new F(function(){return _eQ(_tk,_th,_ti,B(_ta(_tb,_tc,_td,_te,_tj)));});}else{var _tm=E(_tk.b);if(_tc>=_tm){if(_tc!=_tm){return new F(function(){return _eQ(_tk,_th,_ti,B(_ta(_tb,_tc,_td,_te,_tj)));});}else{var _tn=E(_td),_to=E(_tk.c);if(_tn>=_to){if(_tn!=_to){return new F(function(){return _eQ(_tk,_th,_ti,B(_sW(_tb,_tc,_tn,_te,_tj)));});}else{return new T5(0,_tg.a,E(new T3(0,_tb,_tc,_tn)),_te,E(_ti),E(_tj));}}else{return new F(function(){return _fH(_tk,_th,B(_sW(_tb,_tc,_tn,_te,_ti)),_tj);});}}}else{return new F(function(){return _fH(_tk,_th,B(_ta(_tb,_tc,_td,_te,_ti)),_tj);});}}}else{return new F(function(){return _fH(_tk,_th,B(_ta(_tb,_tc,_td,_te,_ti)),_tj);});}}else{return new T5(0,1,E(new T3(0,_tb,_tc,_td)),_te,E(_eL),E(_eL));}},_tp=function(_tq,_tr,_ts,_tt,_tu){var _tv=E(_tu);if(!_tv._){var _tw=_tv.c,_tx=_tv.d,_ty=_tv.e,_tz=E(_tv.b),_tA=E(_tz.a);if(_tq>=_tA){if(_tq!=_tA){return new F(function(){return _eQ(_tz,_tw,_tx,B(_tp(_tq,_tr,_ts,_tt,_ty)));});}else{var _tB=E(_tr),_tC=E(_tz.b);if(_tB>=_tC){if(_tB!=_tC){return new F(function(){return _eQ(_tz,_tw,_tx,B(_ta(_tq,_tB,_ts,_tt,_ty)));});}else{var _tD=E(_ts),_tE=E(_tz.c);if(_tD>=_tE){if(_tD!=_tE){return new F(function(){return _eQ(_tz,_tw,_tx,B(_sW(_tq,_tB,_tD,_tt,_ty)));});}else{return new T5(0,_tv.a,E(new T3(0,_tq,_tB,_tD)),_tt,E(_tx),E(_ty));}}else{return new F(function(){return _fH(_tz,_tw,B(_sW(_tq,_tB,_tD,_tt,_tx)),_ty);});}}}else{return new F(function(){return _fH(_tz,_tw,B(_ta(_tq,_tB,_ts,_tt,_tx)),_ty);});}}}else{return new F(function(){return _fH(_tz,_tw,B(_tp(_tq,_tr,_ts,_tt,_tx)),_ty);});}}else{return new T5(0,1,E(new T3(0,_tq,_tr,_ts)),_tt,E(_eL),E(_eL));}},_tF=function(_tG,_tH,_tI,_tJ,_tK){var _tL=E(_tK);if(!_tL._){var _tM=_tL.c,_tN=_tL.d,_tO=_tL.e,_tP=E(_tL.b),_tQ=E(_tG),_tR=E(_tP.a);if(_tQ>=_tR){if(_tQ!=_tR){return new F(function(){return _eQ(_tP,_tM,_tN,B(_tp(_tQ,_tH,_tI,_tJ,_tO)));});}else{var _tS=E(_tH),_tT=E(_tP.b);if(_tS>=_tT){if(_tS!=_tT){return new F(function(){return _eQ(_tP,_tM,_tN,B(_ta(_tQ,_tS,_tI,_tJ,_tO)));});}else{var _tU=E(_tI),_tV=E(_tP.c);if(_tU>=_tV){if(_tU!=_tV){return new F(function(){return _eQ(_tP,_tM,_tN,B(_sW(_tQ,_tS,_tU,_tJ,_tO)));});}else{return new T5(0,_tL.a,E(new T3(0,_tQ,_tS,_tU)),_tJ,E(_tN),E(_tO));}}else{return new F(function(){return _fH(_tP,_tM,B(_sW(_tQ,_tS,_tU,_tJ,_tN)),_tO);});}}}else{return new F(function(){return _fH(_tP,_tM,B(_ta(_tQ,_tS,_tI,_tJ,_tN)),_tO);});}}}else{return new F(function(){return _fH(_tP,_tM,B(_tp(_tQ,_tH,_tI,_tJ,_tN)),_tO);});}}else{return new T5(0,1,E(new T3(0,_tG,_tH,_tI)),_tJ,E(_eL),E(_eL));}},_tW=function(_tX,_tY,_tZ,_u0){while(1){var _u1=E(_u0);if(!_u1._){var _u2=_u1.d,_u3=_u1.e,_u4=E(_u1.b),_u5=E(_u4.a);if(_tX>=_u5){if(_tX!=_u5){_u0=_u3;continue;}else{var _u6=E(_u4.b);if(_tY>=_u6){if(_tY!=_u6){_u0=_u3;continue;}else{var _u7=E(_u4.c);if(_tZ>=_u7){if(_tZ!=_u7){_u0=_u3;continue;}else{return new T1(1,_u1.c);}}else{_u0=_u2;continue;}}}else{_u0=_u2;continue;}}}else{_u0=_u2;continue;}}else{return __Z;}}},_u8=function(_u9,_ua,_ub,_uc){while(1){var _ud=E(_uc);if(!_ud._){var _ue=_ud.d,_uf=_ud.e,_ug=E(_ud.b),_uh=E(_ug.a);if(_u9>=_uh){if(_u9!=_uh){_uc=_uf;continue;}else{var _ui=E(_ug.b);if(_ua>=_ui){if(_ua!=_ui){_uc=_uf;continue;}else{var _uj=E(_ub),_uk=E(_ug.c);if(_uj>=_uk){if(_uj!=_uk){return new F(function(){return _tW(_u9,_ua,_uj,_uf);});}else{return new T1(1,_ud.c);}}else{return new F(function(){return _tW(_u9,_ua,_uj,_ue);});}}}else{_uc=_ue;continue;}}}else{_uc=_ue;continue;}}else{return __Z;}}},_ul=function(_um,_un,_uo,_up){while(1){var _uq=E(_up);if(!_uq._){var _ur=_uq.d,_us=_uq.e,_ut=E(_uq.b),_uu=E(_ut.a);if(_um>=_uu){if(_um!=_uu){_up=_us;continue;}else{var _uv=E(_un),_uw=E(_ut.b);if(_uv>=_uw){if(_uv!=_uw){return new F(function(){return _u8(_um,_uv,_uo,_us);});}else{var _ux=E(_uo),_uy=E(_ut.c);if(_ux>=_uy){if(_ux!=_uy){return new F(function(){return _tW(_um,_uv,_ux,_us);});}else{return new T1(1,_uq.c);}}else{return new F(function(){return _tW(_um,_uv,_ux,_ur);});}}}else{return new F(function(){return _u8(_um,_uv,_uo,_ur);});}}}else{_up=_ur;continue;}}else{return __Z;}}},_uz=function(_uA,_uB,_uC,_uD){var _uE=E(_uD);if(!_uE._){var _uF=_uE.d,_uG=_uE.e,_uH=E(_uE.b),_uI=E(_uA),_uJ=E(_uH.a);if(_uI>=_uJ){if(_uI!=_uJ){return new F(function(){return _ul(_uI,_uB,_uC,_uG);});}else{var _uK=E(_uB),_uL=E(_uH.b);if(_uK>=_uL){if(_uK!=_uL){return new F(function(){return _u8(_uI,_uK,_uC,_uG);});}else{var _uM=E(_uC),_uN=E(_uH.c);if(_uM>=_uN){if(_uM!=_uN){return new F(function(){return _tW(_uI,_uK,_uM,_uG);});}else{return new T1(1,_uE.c);}}else{return new F(function(){return _tW(_uI,_uK,_uM,_uF);});}}}else{return new F(function(){return _u8(_uI,_uK,_uC,_uF);});}}}else{return new F(function(){return _ul(_uI,_uB,_uC,_uF);});}}else{return __Z;}},_uO=function(_uP){while(1){var _uQ=E(_uP);if(!_uQ._){return __Z;}else{_uP=_uQ.b;continue;}}},_uR=function(_uS,_uT){while(1){var _uU=E(_uS);if(!_uU._){return new T1(1,_uT);}else{var _uV=_uU.b;if(E(_uU.a)!=_uT){return new F(function(){return _uO(_uV);});}else{_uS=_uV;continue;}}}},_uW=new T(function(){return B(unCStr("head"));}),_uX=new T(function(){return B(_91(_uW));}),_uY=function(_uZ){while(1){var _v0=B((function(_v1){var _v2=E(_v1);if(!_v2._){return __Z;}else{var _v3=_v2.b,_v4=E(_v2.a),_v5=E(_v4);if(!_v5){_uZ=_v3;return __continue;}else{return new T2(1,new T(function(){if(_v5<0){return  -_v5;}else{return E(_v4);}}),new T(function(){return B(_uY(_v3));}));}}})(_uZ));if(_v0!=__continue){return _v0;}}},_v6=new T2(1,_mj,_z),_v7=new T2(1,_mh,_v6),_v8=function(_v9){return E(E(_v9).a);},_va=new T2(1,_v8,_v7),_vb=0,_vc=new T1(1,_vb),_vd=-1,_ve=new T1(1,_vd),_vf=1,_vg=new T1(1,_vf),_vh=function(_vi,_vj,_vk,_vl,_vm){var _vn=B(_4j(function(_vo){return B(A1(_vo,_vm))-B(A1(_vo,_vl))|0;},_va)),_vp=B(_uY(_vn)),_vq=E(_vp);if(!_vq._){var _vr=new T1(1,_uX);}else{var _vr=B(_uR(_vq.b,E(_vq.a)));}var _vs=function(_vt){var _vu=function(_vv){var _vw=E(_vl),_vx=E(_vm),_vy=function(_vz){var _vA=function(_vB){var _vC=B(_7e(_vn,_vB));return (_vC<=0)?(_vC>=0)?E(_vc):E(_ve):E(_vg);},_vD=B(_vA(0));if(!_vD._){return __Z;}else{var _vE=B(_vA(1));if(!_vE._){return __Z;}else{var _vF=B(_vA(2));if(!_vF._){return __Z;}else{var _vG=E(_vr);return (_vG._==0)?__Z:new T1(1,new T5(0,_vD.a,_vE.a,_vF.a,_vG.a,_vw));}}}};if(E(_vw.a)!=E(_vx.a)){return new F(function(){return _vy(_);});}else{if(E(_vw.b)!=E(_vx.b)){return new F(function(){return _vy(_);});}else{if(E(_vw.c)!=E(_vx.c)){return new F(function(){return _vy(_);});}else{return new T1(1,new T5(0,_vb,_vb,_vb,_vb,_vw));}}}};if(!E(_vi)){if(!E(_vj)){return __Z;}else{if(B(_7h(_vp,0))==2){return new F(function(){return _vu(_);});}else{return __Z;}}}else{var _vH=B(_7h(_vp,0));if(_vH==1){return new F(function(){return _vu(_);});}else{if(!E(_vj)){return __Z;}else{if(E(_vH)==2){return new F(function(){return _vu(_);});}else{return __Z;}}}}},_vI=E(_vr);if(!_vI._){return new F(function(){return _vs(_);});}else{var _vJ=E(_vk);if(!_vJ._){return new F(function(){return _vs(_);});}else{if(E(_vI.a)<=E(_vJ.a)){return new F(function(){return _vs(_);});}else{return __Z;}}}},_vK=false,_vL=function(_vM,_vN,_vO,_vP,_vQ,_vR,_vS){var _vT=E(_vP);if(!_vT){return __Z;}else{var _vU=new T(function(){return E(_vO)+E(_vS)|0;}),_vV=new T(function(){return E(_vN)+E(_vR)|0;}),_vW=new T(function(){return E(_vM)+E(_vQ)|0;});return new T2(1,new T3(0,_vW,_vV,_vU),new T(function(){return B(_vL(_vM,_vN,_vO,_vT-1|0,_vW,_vV,_vU));}));}},_vX=function(_vY,_vZ,_w0,_w1,_w2){var _w3=E(_w1);if(!_w3){return __Z;}else{var _w4=new T(function(){return E(_w0)+E(E(_w2).c)|0;}),_w5=new T(function(){return E(_vZ)+E(E(_w2).b)|0;}),_w6=new T(function(){return E(_vY)+E(E(_w2).a)|0;});return new T2(1,new T3(0,_w6,_w5,_w4),new T(function(){return B(_vL(_vY,_vZ,_w0,_w3-1|0,_w6,_w5,_w4));}));}},_w7=function(_w8){var _w9=E(_w8);return new F(function(){return _vX(_w9.a,_w9.b,_w9.c,E(_w9.d),_w9.e);});},_wa=function(_wb,_wc,_wd,_we,_wf){while(1){var _wg=B((function(_wh,_wi,_wj,_wk,_wl){var _wm=E(_wk);if(!_wm._){return E(_wl);}else{var _wn=_wm.b,_wo=E(_wm.a),_wp=new T(function(){if(!B(_7h(_wn,0))){return __Z;}else{return new T1(1,new T(function(){var _wq=E(_wn);if(!_wq._){return E(_uX);}else{return E(_wq.a);}}));}}),_wr=_wh,_ws=_wi,_wt=B(_tF(_wo.a,_wo.b,_wo.c,new T5(0,_wh,_wi,_vK,_wp,_wj),_wl));_wb=_wr;_wc=_ws;_wd=new T1(1,_wo);_we=_wn;_wf=_wt;return __continue;}})(_wb,_wc,_wd,_we,_wf));if(_wg!=__continue){return _wg;}}},_wu=function(_wv,_ww,_wx,_wy,_wz,_wA,_wB){var _wC=B(_vh(_wv,_ww,_wx,_wz,_wA));if(!_wC._){return __Z;}else{var _wD=B(_w7(_wC.a)),_wE=function(_wF,_wG){while(1){var _wH=B((function(_wI,_wJ){var _wK=E(_wI);if(!_wK._){return E(_wJ);}else{_wF=_wK.b;_wG=new T(function(){var _wL=E(_wK.a);if(!B(_uz(_wL.a,_wL.b,_wL.c,_wB))._){return E(_wJ);}else{return true;}},1);return __continue;}})(_wF,_wG));if(_wH!=__continue){return _wH;}}};if(!B(_wE(_wD,_vK))){var _wM=E(_wz),_wN=_wM.a,_wO=_wM.b,_wP=_wM.c,_wQ=B(_uz(_wN,_wO,_wP,_wB));if(!_wQ._){return __Z;}else{var _wR=_wQ.a,_wS=E(_wy);if(!_wS._){return __Z;}else{var _wT=_wS.a,_wU=new T(function(){return B(_tF(_wN,_wO,_wP,new T5(0,new T(function(){var _wV=E(_wR);if(!_wV._){return E(_wV.a);}else{return E(_66);}}),new T(function(){var _wW=E(_wR);if(!_wW._){return E(_wW.b);}else{return E(_nH);}}),_nD,new T1(1,new T(function(){var _wX=E(_wD);if(!_wX._){return E(_uX);}else{return E(_wX.a);}})),new T(function(){var _wY=E(_wR);if(!_wY._){return E(_wY.e);}else{return E(_nO);}})),B(_wa(new T(function(){var _wZ=E(_wT);if(!_wZ._){return E(_wZ.a);}else{return E(_66);}}),new T(function(){var _x0=E(_wT);if(!_x0._){return E(_x0.b);}else{return E(_nH);}}),new T1(1,_wM),_wD,_wB))));});return new T1(1,_wU);}}}else{return __Z;}}},_x1=function(_x2,_x3){while(1){var _x4=E(_x2);if(!_x4._){return (E(_x3)._==0)?true:false;}else{var _x5=E(_x3);if(!_x5._){return false;}else{if(E(_x4.a)!=E(_x5.a)){return false;}else{_x2=_x4.b;_x3=_x5.b;continue;}}}}},_x6=new T2(1,_mj,_z),_x7=new T2(1,_mh,_x6),_x8=new T2(1,_v8,_x7),_x9=new T2(1,_z,_z),_xa=function(_xb,_xc){var _xd=function(_xe,_xf){var _xg=E(_xe);if(!_xg._){return E(_xf);}else{var _xh=_xg.a,_xi=E(_xf);if(!_xi._){return E(_xg);}else{var _xj=_xi.a;return (B(A2(_xb,_xh,_xj))==2)?new T2(1,_xj,new T(function(){return B(_xd(_xg,_xi.b));})):new T2(1,_xh,new T(function(){return B(_xd(_xg.b,_xi));}));}}},_xk=function(_xl){var _xm=E(_xl);if(!_xm._){return __Z;}else{var _xn=E(_xm.b);return (_xn._==0)?E(_xm):new T2(1,new T(function(){return B(_xd(_xm.a,_xn.a));}),new T(function(){return B(_xk(_xn.b));}));}},_xo=new T(function(){return B(_xp(B(_xk(_z))));}),_xp=function(_xq){while(1){var _xr=E(_xq);if(!_xr._){return E(_xo);}else{if(!E(_xr.b)._){return E(_xr.a);}else{_xq=B(_xk(_xr));continue;}}}},_xs=new T(function(){return B(_xt(_z));}),_xu=function(_xv,_xw,_xx){while(1){var _xy=B((function(_xz,_xA,_xB){var _xC=E(_xB);if(!_xC._){return new T2(1,new T2(1,_xz,_xA),_xs);}else{var _xD=_xC.a;if(B(A2(_xb,_xz,_xD))==2){var _xE=new T2(1,_xz,_xA);_xv=_xD;_xw=_xE;_xx=_xC.b;return __continue;}else{return new T2(1,new T2(1,_xz,_xA),new T(function(){return B(_xt(_xC));}));}}})(_xv,_xw,_xx));if(_xy!=__continue){return _xy;}}},_xF=function(_xG,_xH,_xI){while(1){var _xJ=B((function(_xK,_xL,_xM){var _xN=E(_xM);if(!_xN._){return new T2(1,new T(function(){return B(A1(_xL,new T2(1,_xK,_z)));}),_xs);}else{var _xO=_xN.a,_xP=_xN.b;switch(B(A2(_xb,_xK,_xO))){case 0:_xG=_xO;_xH=function(_xQ){return new F(function(){return A1(_xL,new T2(1,_xK,_xQ));});};_xI=_xP;return __continue;case 1:_xG=_xO;_xH=function(_xR){return new F(function(){return A1(_xL,new T2(1,_xK,_xR));});};_xI=_xP;return __continue;default:return new T2(1,new T(function(){return B(A1(_xL,new T2(1,_xK,_z)));}),new T(function(){return B(_xt(_xN));}));}}})(_xG,_xH,_xI));if(_xJ!=__continue){return _xJ;}}},_xt=function(_xS){var _xT=E(_xS);if(!_xT._){return E(_x9);}else{var _xU=_xT.a,_xV=E(_xT.b);if(!_xV._){return new T2(1,_xT,_z);}else{var _xW=_xV.a,_xX=_xV.b;if(B(A2(_xb,_xU,_xW))==2){return new F(function(){return _xu(_xW,new T2(1,_xU,_z),_xX);});}else{return new F(function(){return _xF(_xW,function(_xY){return new T2(1,_xU,_xY);},_xX);});}}}};return new F(function(){return _xp(B(_xt(_xc)));});},_xZ=function(_y0,_y1,_y2,_y3,_y4){if(!B(_x1(B(_xa(_6G,B(_4j(function(_y5){var _y6=B(A1(_y5,_y3))-B(A1(_y5,_y2))|0;return (_y6<0)? -_y6:_y6;},_x8)))),_y0))){return __Z;}else{var _y7=E(_y1);if(!_y7._){return __Z;}else{var _y8=_y7.a,_y9=new T(function(){var _ya=E(_y2),_yb=E(_y3),_yc=new T(function(){var _yd=E(_y8);if(!_yd._){return E(_yd.a);}else{return E(_66);}}),_ye=new T(function(){var _yf=E(_y8);if(!_yf._){return E(_yf.b);}else{return E(_nH);}});return B(_tF(_ya.a,_ya.b,_ya.c,new T5(0,_yc,_ye,_nD,new T1(1,_yb),new T(function(){var _yg=E(_y8);if(!_yg._){return E(_yg.e);}else{return E(_nO);}})),B(_tF(_yb.a,_yb.b,_yb.c,new T5(0,_yc,_ye,_nD,_2u,new T1(1,_ya)),_y4))));});return new T1(1,_y9);}}},_yh=1,_yi=new T1(1,_yh),_yj=2,_yk=new T2(1,_yj,_z),_yl=new T2(1,_yh,_yk),_ym=0,_yn=new T2(1,_ym,_yl),_yo=function(_yp,_yq,_yr,_ys,_yt){var _yu=E(_yp);switch(_yu._){case 0:return new F(function(){return _wu(_nD,_vK,new T1(1,new T(function(){if(!E(_yu.a)){return E(_yj);}else{return E(_yh);}})),_yq,_yr,_ys,_yt);});break;case 1:return new F(function(){return _wu(_nD,_vK,_2u,_yq,_yr,_ys,_yt);});break;case 2:return new F(function(){return _xZ(_yn,_yq,_yr,_ys,_yt);});break;case 3:return new F(function(){return _wu(_vK,_nD,_2u,_yq,_yr,_ys,_yt);});break;case 4:return new F(function(){return _wu(_nD,_nD,_2u,_yq,_yr,_ys,_yt);});break;default:return new F(function(){return _wu(_nD,_nD,_yi,_yq,_yr,_ys,_yt);});}},_yv=function(_yw,_yx,_yy,_yz,_yA){var _yB=E(_yz);if(!_yB._){return __Z;}else{var _yC=E(_yB.a),_yD=B(_cN(_yC.a,_yC.b,_yC.c,_yA));if(!_yD._){return __Z;}else{var _yE=E(_yD.a);if(!_yE._){var _yF=B(_yo(_yE.b,_yD,_yC,_yw,new T(function(){return B(_sQ(_yw,_yA));})));return (_yF._==0)?__Z:new T1(1,new T4(0,new T(function(){return E(_yx)+1|0;}),new T(function(){return B(_sU(_yy));}),_2u,new T(function(){return B(_pH(_yF.a));})));}else{return E(_nH);}}}},_yG=function(_yH){return E(E(_yH).a);},_yI=function(_yJ){return E(E(_yJ).a);},_yK=function(_yL){return E(E(_yL).b);},_yM=function(_yN){return E(E(_yN).a);},_yO=function(_){return new F(function(){return nMV(_2u);});},_yP=new T(function(){return B(_2N(_yO));}),_yQ=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_yR=function(_yS){return E(E(_yS).b);},_yT=function(_yU,_yV,_yW,_yX,_yY,_yZ){var _z0=B(_yG(_yU)),_z1=B(_70(_z0)),_z2=new T(function(){return B(_8U(_z0));}),_z3=new T(function(){return B(_9A(_z1));}),_z4=new T(function(){return B(A2(_yI,_yV,_yX));}),_z5=new T(function(){return B(A2(_yM,_yW,_yY));}),_z6=function(_z7){return new F(function(){return A1(_z3,new T3(0,_z5,_z4,_z7));});},_z8=function(_z9){var _za=new T(function(){var _zb=new T(function(){var _zc=__createJSFunc(2,function(_zd,_){var _ze=B(A2(E(_z9),_zd,_));return _2R;}),_zf=_zc;return function(_){return new F(function(){return __app3(E(_yQ),E(_z4),E(_z5),_zf);});};});return B(A1(_z2,_zb));});return new F(function(){return A3(_7I,_z1,_za,_z6);});},_zg=new T(function(){var _zh=new T(function(){return B(_8U(_z0));}),_zi=function(_zj){var _zk=new T(function(){return B(A1(_zh,function(_){var _=wMV(E(_yP),new T1(1,_zj));return new F(function(){return A(_yK,[_yW,_yY,_zj,_]);});}));});return new F(function(){return A3(_7I,_z1,_zk,_yZ);});};return B(A2(_yR,_yU,_zi));});return new F(function(){return A3(_7I,_z1,_zg,_z8);});},_zl=new T(function(){return eval("(function(e,ch){while(e.firstChild) {e.removeChild(e.firstChild);}for(var i in ch) {e.appendChild(ch[i]);}})");}),_zm=function(_zn){return E(_zn);},_zo=function(_zp,_zq,_zr,_zs,_zt){var _zu=new T(function(){var _zv=__lst2arr(B(_4j(_zm,B(_4j(new T(function(){return B(_yI(_zq));}),_zt))))),_zw=_zv;return function(_){var _zx=__app2(E(_zl),B(A2(_yI,_zp,_zs)),_zw);return new F(function(){return _6l(_);});};});return new F(function(){return A2(_8U,_zr,_zu);});},_zy=function(_zz,_zA,_zB,_zC,_zD,_zE,_zF,_){var _zG=B(A1(_c9,_)),_zH=E(_zG);if(!_zH._){return new F(function(){return die(_c0);});}else{var _zI=B(A(_4s,[_zz,_zA,_zB,_zC,new T4(0,_zD,_zE,_2u,_zF)])),_zJ=B(A(_9N,[_45,_zI.a,_zI.b,_zI.c,_zI.d,_zI.e,_])),_zK=function(_zL){while(1){var _zM=B((function(_zN){var _zO=E(_zN);if(!_zO._){return __Z;}else{var _zP=_zO.b,_zQ=E(_zO.a);if(!_zQ._){var _zR=new T(function(){var _zS=new T(function(){var _zT=B(_6b(_zQ.a,new T4(0,_zD,_zE,_2u,_zF)));return new T4(0,_zT.a,_zT.b,_zT.c,_zT.d);});return B(_yT(_46,_3n,_3i,_zQ.b,_bK,function(_zU,_){return new F(function(){return _zV(_zz,_zA,_zB,_zC,_zS,_);});}));});return new T2(1,_zR,new T(function(){return B(_zK(_zP));}));}else{_zL=_zP;return __continue;}}})(_zL));if(_zM!=__continue){return _zM;}}},_zW=B(_zK(_zJ));if(!_zW._){return E(_bN);}else{var _zX=B(_bR(_zW.b,_zW.a,_)),_zY=B(A(_zo,[_3n,_3n,_45,_zH.a,new T(function(){return B(_4j(_bO,_zJ));},1),_]));return _0;}}},_zV=function(_zZ,_A0,_A1,_A2,_A3,_){var _A4=B(A1(_c9,_)),_A5=E(_A4);if(!_A5._){return new F(function(){return die(_c0);});}else{var _A6=B(A(_4s,[_zZ,_A0,_A1,_A2,_A3])),_A7=B(A(_9N,[_45,_A6.a,_A6.b,_A6.c,_A6.d,_A6.e,_])),_A8=new T(function(){return E(E(_A3).a);}),_A9=new T(function(){return E(E(_A3).b);}),_Aa=new T(function(){return E(E(_A3).d);}),_Ab=function(_Ac,_){return new F(function(){return _zy(_zZ,_A0,_A1,_A2,_A8,_A9,_Aa,_);});},_Ad=function(_Ae){while(1){var _Af=B((function(_Ag){var _Ah=E(_Ag);if(!_Ah._){return __Z;}else{var _Ai=_Ah.b,_Aj=E(_Ah.a);if(!_Aj._){var _Ak=_Aj.a,_Al=_Aj.b,_Am=new T(function(){var _An=E(_A3),_Ao=_An.a,_Ap=E(_An.c);if(!_Ap._){var _Aq=new T(function(){var _Ar=B(_6b(_Ak,_An));return new T4(0,_Ar.a,_Ar.b,_Ar.c,_Ar.d);});return B(_yT(_46,_3n,_3i,_Al,_bK,function(_As,_){return new F(function(){return _zV(_zZ,_A0,_A1,_A2,_Aq,_);});}));}else{var _At=E(_Ap.a),_Au=E(_Ak),_Av=function(_Aw){var _Ax=new T(function(){return B(_yv(_Au,_Ao,_An.b,_Ap,_An.d));}),_Ay=new T(function(){if(!E(_Ax)._){return E(_A0);}else{switch(E(_zZ)){case 0:var _Az=E(_A0);if(_Az!=E(_Ao)){return E(_Az);}else{var _AA=E(_Az);if(_AA==2147483647){return E(_6k);}else{return _AA+1|0;}}break;case 1:return E(_A0);break;default:return E(_A0);}}}),_AB=new T(function(){var _AC=E(_Ax);if(!_AC._){return E(_An);}else{return E(_AC.a);}});return new F(function(){return _yT(_46,_3n,_3i,_Al,_bK,function(_AD,_){return new F(function(){return _zV(_zZ,_Ay,_A1,_A2,_AB,_);});});});};if(E(_At.a)!=E(_Au.a)){return B(_Av(_));}else{if(E(_At.b)!=E(_Au.b)){return B(_Av(_));}else{if(E(_At.c)!=E(_Au.c)){return B(_Av(_));}else{return B(_yT(_46,_3n,_3i,_Al,_bK,_Ab));}}}}});return new T2(1,_Am,new T(function(){return B(_Ad(_Ai));}));}else{_Ae=_Ai;return __continue;}}})(_Ae));if(_Af!=__continue){return _Af;}}},_AE=B(_Ad(_A7));if(!_AE._){return E(_bN);}else{var _AF=B(_bR(_AE.b,_AE.a,_)),_AG=B(A(_zo,[_3n,_3n,_45,_A5.a,new T(function(){return B(_4j(_bO,_A7));},1),_]));return _0;}}},_AH=function(_AI,_AJ,_AK,_AL,_){var _AM=B(A1(_c9,_)),_AN=E(_AM);if(!_AN._){return new F(function(){return die(_c0);});}else{var _AO=B(A(_4s,[_bL,_AI,_AJ,_AK,_AL])),_AP=B(A(_9N,[_45,_AO.a,_AO.b,_AO.c,_AO.d,_AO.e,_])),_AQ=new T(function(){return E(E(_AL).a);}),_AR=new T(function(){return E(E(_AL).b);}),_AS=new T(function(){return E(E(_AL).d);}),_AT=function(_AU,_){return new F(function(){return _zy(_bL,_AI,_AJ,_AK,_AQ,_AR,_AS,_);});},_AV=function(_AW){while(1){var _AX=B((function(_AY){var _AZ=E(_AY);if(!_AZ._){return __Z;}else{var _B0=_AZ.b,_B1=E(_AZ.a);if(!_B1._){var _B2=_B1.a,_B3=_B1.b,_B4=new T(function(){var _B5=E(_AL),_B6=_B5.a,_B7=E(_B5.c);if(!_B7._){var _B8=new T(function(){var _B9=B(_6b(_B2,_B5));return new T4(0,_B9.a,_B9.b,_B9.c,_B9.d);});return B(_yT(_46,_3n,_3i,_B3,_bK,function(_Ba,_){return new F(function(){return _AH(_AI,_AJ,_AK,_B8,_);});}));}else{var _Bb=E(_B7.a),_Bc=E(_B2),_Bd=function(_Be){var _Bf=new T(function(){return B(_yv(_Bc,_B6,_B5.b,_B7,_B5.d));}),_Bg=new T(function(){if(!E(_Bf)._){return _AI;}else{if(_AI!=E(_B6)){return _AI;}else{var _Bh=E(_AI);if(_Bh==2147483647){return E(_6k);}else{return _Bh+1|0;}}}}),_Bi=new T(function(){var _Bj=E(_Bf);if(!_Bj._){return E(_B5);}else{return E(_Bj.a);}});return new F(function(){return _yT(_46,_3n,_3i,_B3,_bK,function(_Bk,_){return new F(function(){return _zV(_bL,_Bg,_AJ,_AK,_Bi,_);});});});};if(E(_Bb.a)!=E(_Bc.a)){return B(_Bd(_));}else{if(E(_Bb.b)!=E(_Bc.b)){return B(_Bd(_));}else{if(E(_Bb.c)!=E(_Bc.c)){return B(_Bd(_));}else{return B(_yT(_46,_3n,_3i,_B3,_bK,_AT));}}}}});return new T2(1,_B4,new T(function(){return B(_AV(_B0));}));}else{_AW=_B0;return __continue;}}})(_AW));if(_AX!=__continue){return _AX;}}},_Bl=B(_AV(_AP));if(!_Bl._){return E(_bN);}else{var _Bm=B(_bR(_Bl.b,_Bl.a,_)),_Bn=B(A(_zo,[_3n,_3n,_45,_AN.a,new T(function(){return B(_4j(_bO,_AP));},1),_]));return _0;}}},_Bo=function(_Bp,_Bq,_Br,_Bs,_Bt,_Bu,_){var _Bv=B(A1(_c9,_)),_Bw=E(_Bv);if(!_Bw._){return new F(function(){return die(_c0);});}else{var _Bx=B(A(_4s,[_bL,_Bp,_Bq,_Br,new T4(0,_Bs,_Bt,_2u,_Bu)])),_By=B(A(_9N,[_45,_Bx.a,_Bx.b,_Bx.c,_Bx.d,_Bx.e,_])),_Bz=function(_BA){while(1){var _BB=B((function(_BC){var _BD=E(_BC);if(!_BD._){return __Z;}else{var _BE=_BD.b,_BF=E(_BD.a);if(!_BF._){var _BG=new T(function(){var _BH=new T(function(){var _BI=B(_6b(_BF.a,new T4(0,_Bs,_Bt,_2u,_Bu)));return new T4(0,_BI.a,_BI.b,_BI.c,_BI.d);});return B(_yT(_46,_3n,_3i,_BF.b,_bK,function(_BJ,_){return new F(function(){return _AH(_Bp,_Bq,_Br,_BH,_);});}));});return new T2(1,_BG,new T(function(){return B(_Bz(_BE));}));}else{_BA=_BE;return __continue;}}})(_BA));if(_BB!=__continue){return _BB;}}},_BK=B(_Bz(_By));if(!_BK._){return E(_bN);}else{var _BL=B(_bR(_BK.b,_BK.a,_)),_BM=B(A(_zo,[_3n,_3n,_45,_Bw.a,new T(function(){return B(_4j(_bO,_By));},1),_]));return _0;}}},_BN=new T0(3),_BO=new T0(2),_BP=new T0(4),_BQ=3,_BR=2,_BS=1,_BT=6,_BU=0,_BV=7,_BW=5,_BX=4,_BY=new T1(5,_vK),_BZ=new T1(1,_vK),_C0=function(_C1,_C2){return new T2(0,new T2(0,new T3(0,_BU,_BU,_C2),new T5(0,_C1,_BZ,_nD,_2u,_2u)),new T2(1,new T2(0,new T3(0,_BU,_BS,_C2),new T5(0,_C1,_BO,_nD,_2u,_2u)),new T2(1,new T2(0,new T3(0,_BU,_BR,_C2),new T5(0,_C1,_BN,_nD,_2u,_2u)),new T2(1,new T2(0,new T3(0,_BU,_BQ,_C2),new T5(0,_C1,_BP,_nD,_2u,_2u)),new T2(1,new T2(0,new T3(0,_BU,_BX,_C2),new T5(0,_C1,_BY,_nD,_2u,_2u)),new T2(1,new T2(0,new T3(0,_BU,_BW,_C2),new T5(0,_C1,_BN,_nD,_2u,_2u)),new T2(1,new T2(0,new T3(0,_BU,_BT,_C2),new T5(0,_C1,_BO,_nD,_2u,_2u)),new T2(1,new T2(0,new T3(0,_BU,_BV,_C2),new T5(0,_C1,_BZ,_nD,_2u,_2u)),_z))))))));},_C3=new T(function(){return B(_4d(0,7));}),_C4=new T1(0,_vK),_C5=function(_C6,_C7){var _C8=function(_C9,_Ca){var _Cb=E(_C9);if(!_Cb._){return __Z;}else{var _Cc=E(_Ca);return (_Cc._==0)?__Z:new T2(1,new T2(0,new T3(0,_BU,_Cb.a,_C7),_Cc.a),new T(function(){return B(_C8(_Cb.b,_Cc.b));}));}},_Cd=new T(function(){var _Ce=new T(function(){return new T2(1,new T5(0,_C6,_C4,_nD,_2u,_2u),_Ce);});return E(_Ce);},1);return new F(function(){return _C8(_C3,_Cd);});},_Cf=new T(function(){return B(_C5(_1,_BS));}),_Cg=1,_Ch=new T(function(){return B(_C5(_Cg,_BT));}),_Ci=new T(function(){var _Cj=B(_C0(_Cg,_BV));return B(_7(new T2(1,_Cj.a,_Cj.b),_Ch));}),_Ck=new T(function(){return B(_7(_Cf,_Ci));}),_Cl=new T(function(){var _Cm=B(_C0(_1,_BU));return B(_lN(B(_7(new T2(1,_Cm.a,_Cm.b),_Ck))));}),_Cn=function(_){var _Co=B(_Bo(0,_2,_3,0,_1,_Cl,_));return _0;},_Cp=function(_){return new F(function(){return _Cn(_);});};
var hasteMain = function() {B(A(_Cp, [0]));};window.onload = hasteMain;