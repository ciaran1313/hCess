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

var _0=0,_1=0,_2="deltaZ",_3="deltaY",_4="deltaX",_5=function(_6,_7){var _8=E(_6);return (_8._==0)?E(_7):new T2(1,_8.a,new T(function(){return B(_5(_8.b,_7));}));},_9=function(_a,_b){var _c=jsShowI(_a);return new F(function(){return _5(fromJSStr(_c),_b);});},_d=41,_e=40,_f=function(_g,_h,_i){if(_h>=0){return new F(function(){return _9(_h,_i);});}else{if(_g<=6){return new F(function(){return _9(_h,_i);});}else{return new T2(1,_e,new T(function(){var _j=jsShowI(_h);return B(_5(fromJSStr(_j),new T2(1,_d,_i)));}));}}},_k=new T(function(){return B(unCStr(")"));}),_l=new T(function(){return B(_f(0,2,_k));}),_m=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_l));}),_n=function(_o){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_f(0,_o,_m));}))));});},_p=function(_q,_){return new T(function(){var _r=Number(E(_q)),_s=jsTrunc(_r);if(_s<0){return B(_n(_s));}else{if(_s>2){return B(_n(_s));}else{return _s;}}});},_t=0,_u=new T3(0,_t,_t,_t),_v="button",_w=new T(function(){return eval("jsGetMouseCoords");}),_x=__Z,_y=function(_z,_){var _A=E(_z);if(!_A._){return _x;}else{var _B=B(_y(_A.b,_));return new T2(1,new T(function(){var _C=Number(E(_A.a));return jsTrunc(_C);}),_B);}},_D=function(_E,_){var _F=__arr2lst(0,_E);return new F(function(){return _y(_F,_);});},_G=function(_H,_){return new F(function(){return _D(E(_H),_);});},_I=function(_J,_){return new T(function(){var _K=Number(E(_J));return jsTrunc(_K);});},_L=new T2(0,_I,_G),_M=function(_N,_){var _O=E(_N);if(!_O._){return _x;}else{var _P=B(_M(_O.b,_));return new T2(1,_O.a,_P);}},_Q=new T(function(){return B(unCStr("base"));}),_R=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_S=new T(function(){return B(unCStr("IOException"));}),_T=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Q,_R,_S),_U=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_T,_x,_x),_V=function(_W){return E(_U);},_X=function(_Y){return E(E(_Y).a);},_Z=function(_10,_11,_12){var _13=B(A1(_10,_)),_14=B(A1(_11,_)),_15=hs_eqWord64(_13.a,_14.a);if(!_15){return __Z;}else{var _16=hs_eqWord64(_13.b,_14.b);return (!_16)?__Z:new T1(1,_12);}},_17=function(_18){var _19=E(_18);return new F(function(){return _Z(B(_X(_19.a)),_V,_19.b);});},_1a=new T(function(){return B(unCStr(": "));}),_1b=new T(function(){return B(unCStr(")"));}),_1c=new T(function(){return B(unCStr(" ("));}),_1d=new T(function(){return B(unCStr("interrupted"));}),_1e=new T(function(){return B(unCStr("system error"));}),_1f=new T(function(){return B(unCStr("unsatisified constraints"));}),_1g=new T(function(){return B(unCStr("user error"));}),_1h=new T(function(){return B(unCStr("permission denied"));}),_1i=new T(function(){return B(unCStr("illegal operation"));}),_1j=new T(function(){return B(unCStr("end of file"));}),_1k=new T(function(){return B(unCStr("resource exhausted"));}),_1l=new T(function(){return B(unCStr("resource busy"));}),_1m=new T(function(){return B(unCStr("does not exist"));}),_1n=new T(function(){return B(unCStr("already exists"));}),_1o=new T(function(){return B(unCStr("resource vanished"));}),_1p=new T(function(){return B(unCStr("timeout"));}),_1q=new T(function(){return B(unCStr("unsupported operation"));}),_1r=new T(function(){return B(unCStr("hardware fault"));}),_1s=new T(function(){return B(unCStr("inappropriate type"));}),_1t=new T(function(){return B(unCStr("invalid argument"));}),_1u=new T(function(){return B(unCStr("failed"));}),_1v=new T(function(){return B(unCStr("protocol error"));}),_1w=function(_1x,_1y){switch(E(_1x)){case 0:return new F(function(){return _5(_1n,_1y);});break;case 1:return new F(function(){return _5(_1m,_1y);});break;case 2:return new F(function(){return _5(_1l,_1y);});break;case 3:return new F(function(){return _5(_1k,_1y);});break;case 4:return new F(function(){return _5(_1j,_1y);});break;case 5:return new F(function(){return _5(_1i,_1y);});break;case 6:return new F(function(){return _5(_1h,_1y);});break;case 7:return new F(function(){return _5(_1g,_1y);});break;case 8:return new F(function(){return _5(_1f,_1y);});break;case 9:return new F(function(){return _5(_1e,_1y);});break;case 10:return new F(function(){return _5(_1v,_1y);});break;case 11:return new F(function(){return _5(_1u,_1y);});break;case 12:return new F(function(){return _5(_1t,_1y);});break;case 13:return new F(function(){return _5(_1s,_1y);});break;case 14:return new F(function(){return _5(_1r,_1y);});break;case 15:return new F(function(){return _5(_1q,_1y);});break;case 16:return new F(function(){return _5(_1p,_1y);});break;case 17:return new F(function(){return _5(_1o,_1y);});break;default:return new F(function(){return _5(_1d,_1y);});}},_1z=new T(function(){return B(unCStr("}"));}),_1A=new T(function(){return B(unCStr("{handle: "));}),_1B=function(_1C,_1D,_1E,_1F,_1G,_1H){var _1I=new T(function(){var _1J=new T(function(){var _1K=new T(function(){var _1L=E(_1F);if(!_1L._){return E(_1H);}else{var _1M=new T(function(){return B(_5(_1L,new T(function(){return B(_5(_1b,_1H));},1)));},1);return B(_5(_1c,_1M));}},1);return B(_1w(_1D,_1K));}),_1N=E(_1E);if(!_1N._){return E(_1J);}else{return B(_5(_1N,new T(function(){return B(_5(_1a,_1J));},1)));}}),_1O=E(_1G);if(!_1O._){var _1P=E(_1C);if(!_1P._){return E(_1I);}else{var _1Q=E(_1P.a);if(!_1Q._){var _1R=new T(function(){var _1S=new T(function(){return B(_5(_1z,new T(function(){return B(_5(_1a,_1I));},1)));},1);return B(_5(_1Q.a,_1S));},1);return new F(function(){return _5(_1A,_1R);});}else{var _1T=new T(function(){var _1U=new T(function(){return B(_5(_1z,new T(function(){return B(_5(_1a,_1I));},1)));},1);return B(_5(_1Q.a,_1U));},1);return new F(function(){return _5(_1A,_1T);});}}}else{return new F(function(){return _5(_1O.a,new T(function(){return B(_5(_1a,_1I));},1));});}},_1V=function(_1W){var _1X=E(_1W);return new F(function(){return _1B(_1X.a,_1X.b,_1X.c,_1X.d,_1X.f,_x);});},_1Y=function(_1Z,_20,_21){var _22=E(_20);return new F(function(){return _1B(_22.a,_22.b,_22.c,_22.d,_22.f,_21);});},_23=function(_24,_25){var _26=E(_24);return new F(function(){return _1B(_26.a,_26.b,_26.c,_26.d,_26.f,_25);});},_27=44,_28=93,_29=91,_2a=function(_2b,_2c,_2d){var _2e=E(_2c);if(!_2e._){return new F(function(){return unAppCStr("[]",_2d);});}else{var _2f=new T(function(){var _2g=new T(function(){var _2h=function(_2i){var _2j=E(_2i);if(!_2j._){return E(new T2(1,_28,_2d));}else{var _2k=new T(function(){return B(A2(_2b,_2j.a,new T(function(){return B(_2h(_2j.b));})));});return new T2(1,_27,_2k);}};return B(_2h(_2e.b));});return B(A2(_2b,_2e.a,_2g));});return new T2(1,_29,_2f);}},_2l=function(_2m,_2n){return new F(function(){return _2a(_23,_2m,_2n);});},_2o=new T3(0,_1Y,_1V,_2l),_2p=new T(function(){return new T5(0,_V,_2o,_2q,_17,_1V);}),_2q=function(_2r){return new T2(0,_2p,_2r);},_2s=__Z,_2t=7,_2u=new T(function(){return B(unCStr("Pattern match failure in do expression at src\\Haste\\Prim\\Any.hs:272:5-9"));}),_2v=new T6(0,_2s,_2t,_x,_2u,_2s,_2s),_2w=new T(function(){return B(_2q(_2v));}),_2x=function(_){return new F(function(){return die(_2w);});},_2y=function(_2z){return E(E(_2z).a);},_2A=function(_2B,_2C,_2D,_){var _2E=__arr2lst(0,_2D),_2F=B(_M(_2E,_)),_2G=E(_2F);if(!_2G._){return new F(function(){return _2x(_);});}else{var _2H=E(_2G.b);if(!_2H._){return new F(function(){return _2x(_);});}else{if(!E(_2H.b)._){var _2I=B(A3(_2y,_2B,_2G.a,_)),_2J=B(A3(_2y,_2C,_2H.a,_));return new T2(0,_2I,_2J);}else{return new F(function(){return _2x(_);});}}}},_2K=function(_){return new F(function(){return __jsNull();});},_2L=function(_2M){var _2N=B(A1(_2M,_));return E(_2N);},_2O=new T(function(){return B(_2L(_2K));}),_2P=new T(function(){return E(_2O);}),_2Q=function(_2R,_2S,_){if(E(_2R)==7){var _2T=__app1(E(_w),_2S),_2U=B(_2A(_L,_L,_2T,_)),_2V=__get(_2S,E(_4)),_2W=__get(_2S,E(_3)),_2X=__get(_2S,E(_2));return new T(function(){return new T3(0,E(_2U),E(_2s),E(new T3(0,_2V,_2W,_2X)));});}else{var _2Y=__app1(E(_w),_2S),_2Z=B(_2A(_L,_L,_2Y,_)),_30=__get(_2S,E(_v)),_31=__eq(_30,E(_2P));if(!E(_31)){var _32=B(_p(_30,_));return new T(function(){return new T3(0,E(_2Z),E(new T1(1,_32)),E(_u));});}else{return new T(function(){return new T3(0,E(_2Z),E(_2s),E(_u));});}}},_33=function(_34,_35,_){return new F(function(){return _2Q(_34,E(_35),_);});},_36="mouseout",_37="mouseover",_38="mousemove",_39="mouseup",_3a="mousedown",_3b="dblclick",_3c="click",_3d="wheel",_3e=function(_3f){switch(E(_3f)){case 0:return E(_3c);case 1:return E(_3b);case 2:return E(_3a);case 3:return E(_39);case 4:return E(_38);case 5:return E(_37);case 6:return E(_36);default:return E(_3d);}},_3g=new T2(0,_3e,_33),_3h=function(_3i,_){return new T1(1,_3i);},_3j=function(_3k){return E(_3k);},_3l=new T2(0,_3j,_3h),_3m=function(_3n,_3o,_){var _3p=B(A1(_3n,_)),_3q=B(A1(_3o,_));return _3p;},_3r=function(_3s,_3t,_){var _3u=B(A1(_3s,_)),_3v=B(A1(_3t,_));return new T(function(){return B(A1(_3u,_3v));});},_3w=function(_3x,_3y,_){var _3z=B(A1(_3y,_));return _3x;},_3A=function(_3B,_3C,_){var _3D=B(A1(_3C,_));return new T(function(){return B(A1(_3B,_3D));});},_3E=new T2(0,_3A,_3w),_3F=function(_3G,_){return _3G;},_3H=function(_3I,_3J,_){var _3K=B(A1(_3I,_));return new F(function(){return A1(_3J,_);});},_3L=new T5(0,_3E,_3F,_3r,_3H,_3m),_3M=new T(function(){return E(_2p);}),_3N=function(_3O){return E(E(_3O).c);},_3P=function(_3Q){return new T6(0,_2s,_2t,_x,_3Q,_2s,_2s);},_3R=function(_3S,_){var _3T=new T(function(){return B(A2(_3N,_3M,new T(function(){return B(A1(_3P,_3S));})));});return new F(function(){return die(_3T);});},_3U=function(_3V,_){return new F(function(){return _3R(_3V,_);});},_3W=function(_3X){return new F(function(){return A1(_3U,_3X);});},_3Y=function(_3Z,_40,_){var _41=B(A1(_3Z,_));return new F(function(){return A2(_40,_41,_);});},_42=new T5(0,_3L,_3Y,_3H,_3F,_3W),_43=new T2(0,_42,_3j),_44=new T2(0,_43,_3F),_45=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_46=new T(function(){return B(err(_45));}),_47=function(_48,_49,_4a,_4b,_4c){return new T5(0,_48,_49,_4a,_4b,_4c);},_4d=function(_4e,_4f){if(_4e<=_4f){var _4g=function(_4h){return new T2(1,_4h,new T(function(){if(_4h!=_4f){return B(_4g(_4h+1|0));}else{return __Z;}}));};return new F(function(){return _4g(_4e);});}else{return __Z;}},_4i=new T(function(){return B(_4d(0,2147483647));}),_4j=function(_4k,_4l){var _4m=E(_4l);return (_4m._==0)?__Z:new T2(1,new T(function(){return B(A1(_4k,_4m.a));}),new T(function(){return B(_4j(_4k,_4m.b));}));},_4n=function(_4o,_4p,_4q,_4r){switch(E(_4r)){case 0:return E(_4o);case 1:return E(_4p);default:return E(_4q);}},_4s=function(_4t,_4u,_4v,_4w){var _4x=new T(function(){var _4y=function(_4z){var _4A=function(_4B){return new T3(0,new T(function(){return B(_4n(_4u,_4B,_4z,_4t));}),new T(function(){return B(_4n(_4u,_4B,_4z,_4v));}),new T(function(){return B(_4n(_4u,_4B,_4z,_4w));}));};return new F(function(){return _4j(_4A,_4i);});};return B(_4j(_4y,_4i));});return function(_4C){return new F(function(){return _47(new T2(0,_4t,_4u),_4v,_4w,_4x,_4C);});};},_4D=function(_4E,_4F,_4G,_4H){while(1){var _4I=E(_4H);if(!_4I._){var _4J=_4I.d,_4K=_4I.e,_4L=E(_4I.b),_4M=E(_4L.a);if(_4E>=_4M){if(_4E!=_4M){_4H=_4K;continue;}else{var _4N=E(_4L.b);if(_4F>=_4N){if(_4F!=_4N){_4H=_4K;continue;}else{var _4O=E(_4L.c);if(_4G>=_4O){if(_4G!=_4O){_4H=_4K;continue;}else{return new T1(1,_4I.c);}}else{_4H=_4J;continue;}}}else{_4H=_4J;continue;}}}else{_4H=_4J;continue;}}else{return __Z;}}},_4P=function(_4Q,_4R,_4S,_4T){while(1){var _4U=E(_4T);if(!_4U._){var _4V=_4U.d,_4W=_4U.e,_4X=E(_4U.b),_4Y=E(_4X.a);if(_4Q>=_4Y){if(_4Q!=_4Y){_4T=_4W;continue;}else{var _4Z=E(_4X.b);if(_4R>=_4Z){if(_4R!=_4Z){_4T=_4W;continue;}else{var _50=E(_4S),_51=E(_4X.c);if(_50>=_51){if(_50!=_51){return new F(function(){return _4D(_4Q,_4R,_50,_4W);});}else{return new T1(1,_4U.c);}}else{return new F(function(){return _4D(_4Q,_4R,_50,_4V);});}}}else{_4T=_4V;continue;}}}else{_4T=_4V;continue;}}else{return __Z;}}},_52=function(_53,_54,_55,_56){while(1){var _57=E(_56);if(!_57._){var _58=_57.d,_59=_57.e,_5a=E(_57.b),_5b=E(_5a.a);if(_53>=_5b){if(_53!=_5b){_56=_59;continue;}else{var _5c=E(_54),_5d=E(_5a.b);if(_5c>=_5d){if(_5c!=_5d){return new F(function(){return _4P(_53,_5c,_55,_59);});}else{var _5e=E(_55),_5f=E(_5a.c);if(_5e>=_5f){if(_5e!=_5f){return new F(function(){return _4D(_53,_5c,_5e,_59);});}else{return new T1(1,_57.c);}}else{return new F(function(){return _4D(_53,_5c,_5e,_58);});}}}else{return new F(function(){return _4P(_53,_5c,_55,_58);});}}}else{_56=_58;continue;}}else{return __Z;}}},_5g=function(_5h,_5i,_5j,_5k){var _5l=E(_5k);if(!_5l._){var _5m=_5l.d,_5n=_5l.e,_5o=E(_5l.b),_5p=E(_5h),_5q=E(_5o.a);if(_5p>=_5q){if(_5p!=_5q){return new F(function(){return _52(_5p,_5i,_5j,_5n);});}else{var _5r=E(_5i),_5s=E(_5o.b);if(_5r>=_5s){if(_5r!=_5s){return new F(function(){return _4P(_5p,_5r,_5j,_5n);});}else{var _5t=E(_5j),_5u=E(_5o.c);if(_5t>=_5u){if(_5t!=_5u){return new F(function(){return _4D(_5p,_5r,_5t,_5n);});}else{return new T1(1,_5l.c);}}else{return new F(function(){return _4D(_5p,_5r,_5t,_5m);});}}}else{return new F(function(){return _4P(_5p,_5r,_5j,_5m);});}}}else{return new F(function(){return _52(_5p,_5i,_5j,_5m);});}}else{return __Z;}},_5v=function(_5w,_5x,_5y,_5z){while(1){var _5A=E(_5z);if(!_5A._){var _5B=_5A.d,_5C=_5A.e,_5D=E(_5A.b),_5E=E(_5D.a);if(_5w>=_5E){if(_5w!=_5E){_5z=_5C;continue;}else{var _5F=E(_5D.b);if(_5x>=_5F){if(_5x!=_5F){_5z=_5C;continue;}else{var _5G=E(_5D.c);if(_5y>=_5G){if(_5y!=_5G){_5z=_5C;continue;}else{return new T1(1,_5A.c);}}else{_5z=_5B;continue;}}}else{_5z=_5B;continue;}}}else{_5z=_5B;continue;}}else{return __Z;}}},_5H=function(_5I,_5J,_5K,_5L){while(1){var _5M=E(_5L);if(!_5M._){var _5N=_5M.d,_5O=_5M.e,_5P=E(_5M.b),_5Q=E(_5P.a);if(_5I>=_5Q){if(_5I!=_5Q){_5L=_5O;continue;}else{var _5R=E(_5P.b);if(_5J>=_5R){if(_5J!=_5R){_5L=_5O;continue;}else{var _5S=E(_5K),_5T=E(_5P.c);if(_5S>=_5T){if(_5S!=_5T){return new F(function(){return _5v(_5I,_5J,_5S,_5O);});}else{return new T1(1,_5M.c);}}else{return new F(function(){return _5v(_5I,_5J,_5S,_5N);});}}}else{_5L=_5N;continue;}}}else{_5L=_5N;continue;}}else{return __Z;}}},_5U=function(_5V,_5W,_5X,_5Y){while(1){var _5Z=E(_5Y);if(!_5Z._){var _60=_5Z.d,_61=_5Z.e,_62=E(_5Z.b),_63=E(_62.a);if(_5V>=_63){if(_5V!=_63){_5Y=_61;continue;}else{var _64=E(_5W),_65=E(_62.b);if(_64>=_65){if(_64!=_65){return new F(function(){return _5H(_5V,_64,_5X,_61);});}else{var _66=E(_5X),_67=E(_62.c);if(_66>=_67){if(_66!=_67){return new F(function(){return _5v(_5V,_64,_66,_61);});}else{return new T1(1,_5Z.c);}}else{return new F(function(){return _5v(_5V,_64,_66,_60);});}}}else{return new F(function(){return _5H(_5V,_64,_5X,_60);});}}}else{_5Y=_60;continue;}}else{return __Z;}}},_68=function(_69,_6a,_6b,_6c){var _6d=E(_6c);if(!_6d._){var _6e=_6d.d,_6f=_6d.e,_6g=E(_6d.b),_6h=E(_69),_6i=E(_6g.a);if(_6h>=_6i){if(_6h!=_6i){return new F(function(){return _5U(_6h,_6a,_6b,_6f);});}else{var _6j=E(_6a),_6k=E(_6g.b);if(_6j>=_6k){if(_6j!=_6k){return new F(function(){return _5H(_6h,_6j,_6b,_6f);});}else{var _6l=E(_6b),_6m=E(_6g.c);if(_6l>=_6m){if(_6l!=_6m){return new F(function(){return _5v(_6h,_6j,_6l,_6f);});}else{return new T1(1,_6d.c);}}else{return new F(function(){return _5v(_6h,_6j,_6l,_6e);});}}}else{return new F(function(){return _5H(_6h,_6j,_6b,_6e);});}}}else{return new F(function(){return _5U(_6h,_6a,_6b,_6e);});}}else{return __Z;}},_6n=new T0(1),_6o=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_6p=function(_6q){return new F(function(){return err(_6o);});},_6r=new T(function(){return B(_6p(_));}),_6s=function(_6t,_6u,_6v,_6w){var _6x=E(_6w);if(!_6x._){var _6y=_6x.a,_6z=E(_6v);if(!_6z._){var _6A=_6z.a,_6B=_6z.b,_6C=_6z.c;if(_6A<=(imul(3,_6y)|0)){return new T5(0,(1+_6A|0)+_6y|0,E(_6t),_6u,E(_6z),E(_6x));}else{var _6D=E(_6z.d);if(!_6D._){var _6E=_6D.a,_6F=E(_6z.e);if(!_6F._){var _6G=_6F.a,_6H=_6F.b,_6I=_6F.c,_6J=_6F.d;if(_6G>=(imul(2,_6E)|0)){var _6K=function(_6L){var _6M=E(_6F.e);return (_6M._==0)?new T5(0,(1+_6A|0)+_6y|0,E(_6H),_6I,E(new T5(0,(1+_6E|0)+_6L|0,E(_6B),_6C,E(_6D),E(_6J))),E(new T5(0,(1+_6y|0)+_6M.a|0,E(_6t),_6u,E(_6M),E(_6x)))):new T5(0,(1+_6A|0)+_6y|0,E(_6H),_6I,E(new T5(0,(1+_6E|0)+_6L|0,E(_6B),_6C,E(_6D),E(_6J))),E(new T5(0,1+_6y|0,E(_6t),_6u,E(_6n),E(_6x))));},_6N=E(_6J);if(!_6N._){return new F(function(){return _6K(_6N.a);});}else{return new F(function(){return _6K(0);});}}else{return new T5(0,(1+_6A|0)+_6y|0,E(_6B),_6C,E(_6D),E(new T5(0,(1+_6y|0)+_6G|0,E(_6t),_6u,E(_6F),E(_6x))));}}else{return E(_6r);}}else{return E(_6r);}}}else{return new T5(0,1+_6y|0,E(_6t),_6u,E(_6n),E(_6x));}}else{var _6O=E(_6v);if(!_6O._){var _6P=_6O.a,_6Q=_6O.b,_6R=_6O.c,_6S=_6O.e,_6T=E(_6O.d);if(!_6T._){var _6U=_6T.a,_6V=E(_6S);if(!_6V._){var _6W=_6V.a,_6X=_6V.b,_6Y=_6V.c,_6Z=_6V.d;if(_6W>=(imul(2,_6U)|0)){var _70=function(_71){var _72=E(_6V.e);return (_72._==0)?new T5(0,1+_6P|0,E(_6X),_6Y,E(new T5(0,(1+_6U|0)+_71|0,E(_6Q),_6R,E(_6T),E(_6Z))),E(new T5(0,1+_72.a|0,E(_6t),_6u,E(_72),E(_6n)))):new T5(0,1+_6P|0,E(_6X),_6Y,E(new T5(0,(1+_6U|0)+_71|0,E(_6Q),_6R,E(_6T),E(_6Z))),E(new T5(0,1,E(_6t),_6u,E(_6n),E(_6n))));},_73=E(_6Z);if(!_73._){return new F(function(){return _70(_73.a);});}else{return new F(function(){return _70(0);});}}else{return new T5(0,1+_6P|0,E(_6Q),_6R,E(_6T),E(new T5(0,1+_6W|0,E(_6t),_6u,E(_6V),E(_6n))));}}else{return new T5(0,3,E(_6Q),_6R,E(_6T),E(new T5(0,1,E(_6t),_6u,E(_6n),E(_6n))));}}else{var _74=E(_6S);return (_74._==0)?new T5(0,3,E(_74.b),_74.c,E(new T5(0,1,E(_6Q),_6R,E(_6n),E(_6n))),E(new T5(0,1,E(_6t),_6u,E(_6n),E(_6n)))):new T5(0,2,E(_6t),_6u,E(_6O),E(_6n));}}else{return new T5(0,1,E(_6t),_6u,E(_6n),E(_6n));}}},_75=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_76=function(_77){return new F(function(){return err(_75);});},_78=new T(function(){return B(_76(_));}),_79=function(_7a,_7b,_7c,_7d){var _7e=E(_7c);if(!_7e._){var _7f=_7e.a,_7g=E(_7d);if(!_7g._){var _7h=_7g.a,_7i=_7g.b,_7j=_7g.c;if(_7h<=(imul(3,_7f)|0)){return new T5(0,(1+_7f|0)+_7h|0,E(_7a),_7b,E(_7e),E(_7g));}else{var _7k=E(_7g.d);if(!_7k._){var _7l=_7k.a,_7m=_7k.b,_7n=_7k.c,_7o=_7k.d,_7p=E(_7g.e);if(!_7p._){var _7q=_7p.a;if(_7l>=(imul(2,_7q)|0)){var _7r=function(_7s){var _7t=E(_7a),_7u=E(_7k.e);return (_7u._==0)?new T5(0,(1+_7f|0)+_7h|0,E(_7m),_7n,E(new T5(0,(1+_7f|0)+_7s|0,E(_7t),_7b,E(_7e),E(_7o))),E(new T5(0,(1+_7q|0)+_7u.a|0,E(_7i),_7j,E(_7u),E(_7p)))):new T5(0,(1+_7f|0)+_7h|0,E(_7m),_7n,E(new T5(0,(1+_7f|0)+_7s|0,E(_7t),_7b,E(_7e),E(_7o))),E(new T5(0,1+_7q|0,E(_7i),_7j,E(_6n),E(_7p))));},_7v=E(_7o);if(!_7v._){return new F(function(){return _7r(_7v.a);});}else{return new F(function(){return _7r(0);});}}else{return new T5(0,(1+_7f|0)+_7h|0,E(_7i),_7j,E(new T5(0,(1+_7f|0)+_7l|0,E(_7a),_7b,E(_7e),E(_7k))),E(_7p));}}else{return E(_78);}}else{return E(_78);}}}else{return new T5(0,1+_7f|0,E(_7a),_7b,E(_7e),E(_6n));}}else{var _7w=E(_7d);if(!_7w._){var _7x=_7w.a,_7y=_7w.b,_7z=_7w.c,_7A=_7w.e,_7B=E(_7w.d);if(!_7B._){var _7C=_7B.a,_7D=_7B.b,_7E=_7B.c,_7F=_7B.d,_7G=E(_7A);if(!_7G._){var _7H=_7G.a;if(_7C>=(imul(2,_7H)|0)){var _7I=function(_7J){var _7K=E(_7a),_7L=E(_7B.e);return (_7L._==0)?new T5(0,1+_7x|0,E(_7D),_7E,E(new T5(0,1+_7J|0,E(_7K),_7b,E(_6n),E(_7F))),E(new T5(0,(1+_7H|0)+_7L.a|0,E(_7y),_7z,E(_7L),E(_7G)))):new T5(0,1+_7x|0,E(_7D),_7E,E(new T5(0,1+_7J|0,E(_7K),_7b,E(_6n),E(_7F))),E(new T5(0,1+_7H|0,E(_7y),_7z,E(_6n),E(_7G))));},_7M=E(_7F);if(!_7M._){return new F(function(){return _7I(_7M.a);});}else{return new F(function(){return _7I(0);});}}else{return new T5(0,1+_7x|0,E(_7y),_7z,E(new T5(0,1+_7C|0,E(_7a),_7b,E(_6n),E(_7B))),E(_7G));}}else{return new T5(0,3,E(_7D),_7E,E(new T5(0,1,E(_7a),_7b,E(_6n),E(_6n))),E(new T5(0,1,E(_7y),_7z,E(_6n),E(_6n))));}}else{var _7N=E(_7A);return (_7N._==0)?new T5(0,3,E(_7y),_7z,E(new T5(0,1,E(_7a),_7b,E(_6n),E(_6n))),E(_7N)):new T5(0,2,E(_7a),_7b,E(_6n),E(_7w));}}else{return new T5(0,1,E(_7a),_7b,E(_6n),E(_6n));}}},_7O=function(_7P,_7Q,_7R,_7S,_7T){var _7U=E(_7T);if(!_7U._){var _7V=new T(function(){var _7W=B(_7O(_7U.a,_7U.b,_7U.c,_7U.d,_7U.e));return new T2(0,_7W.a,_7W.b);});return new T2(0,new T(function(){return E(E(_7V).a);}),new T(function(){return B(_6s(_7Q,_7R,_7S,E(_7V).b));}));}else{return new T2(0,new T2(0,_7Q,_7R),_7S);}},_7X=function(_7Y,_7Z,_80,_81,_82){var _83=E(_81);if(!_83._){var _84=new T(function(){var _85=B(_7X(_83.a,_83.b,_83.c,_83.d,_83.e));return new T2(0,_85.a,_85.b);});return new T2(0,new T(function(){return E(E(_84).a);}),new T(function(){return B(_79(_7Z,_80,E(_84).b,_82));}));}else{return new T2(0,new T2(0,_7Z,_80),_82);}},_86=function(_87,_88){var _89=E(_87);if(!_89._){var _8a=_89.a,_8b=E(_88);if(!_8b._){var _8c=_8b.a;if(_8a<=_8c){var _8d=B(_7X(_8c,_8b.b,_8b.c,_8b.d,_8b.e)),_8e=E(_8d.a);return new F(function(){return _6s(_8e.a,_8e.b,_89,_8d.b);});}else{var _8f=B(_7O(_8a,_89.b,_89.c,_89.d,_89.e)),_8g=E(_8f.a);return new F(function(){return _79(_8g.a,_8g.b,_8f.b,_8b);});}}else{return E(_89);}}else{return E(_88);}},_8h=function(_8i,_8j,_8k,_8l){var _8m=E(_8l);if(!_8m._){var _8n=_8m.c,_8o=_8m.d,_8p=_8m.e,_8q=E(_8m.b),_8r=E(_8q.a);if(_8i>=_8r){if(_8i!=_8r){return new F(function(){return _6s(_8q,_8n,_8o,B(_8h(_8i,_8j,_8k,_8p)));});}else{var _8s=E(_8q.b);if(_8j>=_8s){if(_8j!=_8s){return new F(function(){return _6s(_8q,_8n,_8o,B(_8h(_8i,_8j,_8k,_8p)));});}else{var _8t=E(_8q.c);if(_8k>=_8t){if(_8k!=_8t){return new F(function(){return _6s(_8q,_8n,_8o,B(_8h(_8i,_8j,_8k,_8p)));});}else{return new F(function(){return _86(_8o,_8p);});}}else{return new F(function(){return _79(_8q,_8n,B(_8h(_8i,_8j,_8k,_8o)),_8p);});}}}else{return new F(function(){return _79(_8q,_8n,B(_8h(_8i,_8j,_8k,_8o)),_8p);});}}}else{return new F(function(){return _79(_8q,_8n,B(_8h(_8i,_8j,_8k,_8o)),_8p);});}}else{return new T0(1);}},_8u=function(_8v,_8w,_8x,_8y){var _8z=E(_8y);if(!_8z._){var _8A=_8z.c,_8B=_8z.d,_8C=_8z.e,_8D=E(_8z.b),_8E=E(_8D.a);if(_8v>=_8E){if(_8v!=_8E){return new F(function(){return _6s(_8D,_8A,_8B,B(_8u(_8v,_8w,_8x,_8C)));});}else{var _8F=E(_8D.b);if(_8w>=_8F){if(_8w!=_8F){return new F(function(){return _6s(_8D,_8A,_8B,B(_8u(_8v,_8w,_8x,_8C)));});}else{var _8G=E(_8x),_8H=E(_8D.c);if(_8G>=_8H){if(_8G!=_8H){return new F(function(){return _6s(_8D,_8A,_8B,B(_8h(_8v,_8w,_8G,_8C)));});}else{return new F(function(){return _86(_8B,_8C);});}}else{return new F(function(){return _79(_8D,_8A,B(_8h(_8v,_8w,_8G,_8B)),_8C);});}}}else{return new F(function(){return _79(_8D,_8A,B(_8u(_8v,_8w,_8x,_8B)),_8C);});}}}else{return new F(function(){return _79(_8D,_8A,B(_8u(_8v,_8w,_8x,_8B)),_8C);});}}else{return new T0(1);}},_8I=function(_8J,_8K,_8L,_8M){var _8N=E(_8M);if(!_8N._){var _8O=_8N.c,_8P=_8N.d,_8Q=_8N.e,_8R=E(_8N.b),_8S=E(_8R.a);if(_8J>=_8S){if(_8J!=_8S){return new F(function(){return _6s(_8R,_8O,_8P,B(_8I(_8J,_8K,_8L,_8Q)));});}else{var _8T=E(_8K),_8U=E(_8R.b);if(_8T>=_8U){if(_8T!=_8U){return new F(function(){return _6s(_8R,_8O,_8P,B(_8u(_8J,_8T,_8L,_8Q)));});}else{var _8V=E(_8L),_8W=E(_8R.c);if(_8V>=_8W){if(_8V!=_8W){return new F(function(){return _6s(_8R,_8O,_8P,B(_8h(_8J,_8T,_8V,_8Q)));});}else{return new F(function(){return _86(_8P,_8Q);});}}else{return new F(function(){return _79(_8R,_8O,B(_8h(_8J,_8T,_8V,_8P)),_8Q);});}}}else{return new F(function(){return _79(_8R,_8O,B(_8u(_8J,_8T,_8L,_8P)),_8Q);});}}}else{return new F(function(){return _79(_8R,_8O,B(_8I(_8J,_8K,_8L,_8P)),_8Q);});}}else{return new T0(1);}},_8X=function(_8Y,_8Z,_90,_91){var _92=E(_91);if(!_92._){var _93=_92.c,_94=_92.d,_95=_92.e,_96=E(_92.b),_97=E(_8Y),_98=E(_96.a);if(_97>=_98){if(_97!=_98){return new F(function(){return _6s(_96,_93,_94,B(_8I(_97,_8Z,_90,_95)));});}else{var _99=E(_8Z),_9a=E(_96.b);if(_99>=_9a){if(_99!=_9a){return new F(function(){return _6s(_96,_93,_94,B(_8u(_97,_99,_90,_95)));});}else{var _9b=E(_90),_9c=E(_96.c);if(_9b>=_9c){if(_9b!=_9c){return new F(function(){return _6s(_96,_93,_94,B(_8h(_97,_99,_9b,_95)));});}else{return new F(function(){return _86(_94,_95);});}}else{return new F(function(){return _79(_96,_93,B(_8h(_97,_99,_9b,_94)),_95);});}}}else{return new F(function(){return _79(_96,_93,B(_8u(_97,_99,_90,_94)),_95);});}}}else{return new F(function(){return _79(_96,_93,B(_8I(_97,_8Z,_90,_94)),_95);});}}else{return new T0(1);}},_9d=function(_9e,_9f,_9g){while(1){var _9h=E(_9f);if(!_9h._){return E(_9g);}else{var _9i=E(_9h.a),_9j=_9i.a,_9k=_9i.b,_9l=_9i.c,_9m=B(_5g(_9j,_9k,_9l,_9g));if(!_9m._){return E(_9g);}else{var _9n=_9m.a;if(!B(A1(_9e,_9n))){var _9o=B(_8X(_9j,_9k,_9l,_9g));_9f=E(_9n).e;_9g=_9o;continue;}else{return E(_9g);}}}}},_9p=function(_9q,_9r,_9s,_9t){while(1){var _9u=E(_9s);if(!_9u._){return E(_9t);}else{var _9v=E(_9u.a),_9w=_9v.a,_9x=_9v.b,_9y=_9v.c,_9z=B(_5g(_9w,_9x,_9y,_9t));if(!_9z._){return E(_9t);}else{var _9A=_9z.a;if(!B(A1(_9r,_9A))){var _9B=B(A1(_9q,_9A)),_9C=B(_8X(_9w,_9x,_9y,_9t));_9s=_9B;_9t=_9C;continue;}else{return E(_9t);}}}}},_9D=function(_9E){return E(E(_9E).d);},_9F=function(_9G,_9H,_9I,_9J,_9K){var _9L=B(_5g(_9H,_9I,_9J,_9K));if(!_9L._){return E(_9K);}else{var _9M=_9L.a;if(!B(A1(_9G,_9M))){return new F(function(){return _9p(_9D,_9G,E(_9M).d,B(_8X(_9H,_9I,_9J,_9K)));});}else{return E(_9K);}}},_9N=function(_9O){return false;},_9P=function(_9Q){return E(E(_9Q).c);},_9R=function(_9S,_9T,_9U,_9V){var _9W=B(_68(_9S,_9T,_9U,_9V));if(!_9W._){return new F(function(){return _9F(_9N,_9S,_9T,_9U,_9V);});}else{return new F(function(){return _9F(_9N,_9S,_9T,_9U,B(_9d(new T(function(){var _9X=B(_5g(_9S,_9T,_9U,_9V));if(!_9X._){return E(_9P);}else{if(!E(E(_9X.a).c)){return E(_9P);}else{return E(_9N);}}}),E(_9W.a).e,_9V)));});}},_9Y=function(_9Z,_a0,_a1,_a2,_a3){var _a4=E(_a3);if(!_a4._){var _a5=_a4.c,_a6=_a4.d,_a7=_a4.e,_a8=E(_a4.b),_a9=E(_a8.a);if(_9Z>=_a9){if(_9Z!=_a9){return new F(function(){return _79(_a8,_a5,_a6,B(_9Y(_9Z,_a0,_a1,_a2,_a7)));});}else{var _aa=E(_a8.b);if(_a0>=_aa){if(_a0!=_aa){return new F(function(){return _79(_a8,_a5,_a6,B(_9Y(_9Z,_a0,_a1,_a2,_a7)));});}else{var _ab=E(_a8.c);if(_a1>=_ab){if(_a1!=_ab){return new F(function(){return _79(_a8,_a5,_a6,B(_9Y(_9Z,_a0,_a1,_a2,_a7)));});}else{return new T5(0,_a4.a,E(new T3(0,_9Z,_a0,_a1)),_a2,E(_a6),E(_a7));}}else{return new F(function(){return _6s(_a8,_a5,B(_9Y(_9Z,_a0,_a1,_a2,_a6)),_a7);});}}}else{return new F(function(){return _6s(_a8,_a5,B(_9Y(_9Z,_a0,_a1,_a2,_a6)),_a7);});}}}else{return new F(function(){return _6s(_a8,_a5,B(_9Y(_9Z,_a0,_a1,_a2,_a6)),_a7);});}}else{return new T5(0,1,E(new T3(0,_9Z,_a0,_a1)),_a2,E(_6n),E(_6n));}},_ac=function(_ad,_ae,_af,_ag,_ah){var _ai=E(_ah);if(!_ai._){var _aj=_ai.c,_ak=_ai.d,_al=_ai.e,_am=E(_ai.b),_an=E(_am.a);if(_ad>=_an){if(_ad!=_an){return new F(function(){return _79(_am,_aj,_ak,B(_ac(_ad,_ae,_af,_ag,_al)));});}else{var _ao=E(_am.b);if(_ae>=_ao){if(_ae!=_ao){return new F(function(){return _79(_am,_aj,_ak,B(_ac(_ad,_ae,_af,_ag,_al)));});}else{var _ap=E(_af),_aq=E(_am.c);if(_ap>=_aq){if(_ap!=_aq){return new F(function(){return _79(_am,_aj,_ak,B(_9Y(_ad,_ae,_ap,_ag,_al)));});}else{return new T5(0,_ai.a,E(new T3(0,_ad,_ae,_ap)),_ag,E(_ak),E(_al));}}else{return new F(function(){return _6s(_am,_aj,B(_9Y(_ad,_ae,_ap,_ag,_ak)),_al);});}}}else{return new F(function(){return _6s(_am,_aj,B(_ac(_ad,_ae,_af,_ag,_ak)),_al);});}}}else{return new F(function(){return _6s(_am,_aj,B(_ac(_ad,_ae,_af,_ag,_ak)),_al);});}}else{return new T5(0,1,E(new T3(0,_ad,_ae,_af)),_ag,E(_6n),E(_6n));}},_ar=function(_as,_at,_au,_av,_aw){var _ax=E(_aw);if(!_ax._){var _ay=_ax.c,_az=_ax.d,_aA=_ax.e,_aB=E(_ax.b),_aC=E(_aB.a);if(_as>=_aC){if(_as!=_aC){return new F(function(){return _79(_aB,_ay,_az,B(_ar(_as,_at,_au,_av,_aA)));});}else{var _aD=E(_at),_aE=E(_aB.b);if(_aD>=_aE){if(_aD!=_aE){return new F(function(){return _79(_aB,_ay,_az,B(_ac(_as,_aD,_au,_av,_aA)));});}else{var _aF=E(_au),_aG=E(_aB.c);if(_aF>=_aG){if(_aF!=_aG){return new F(function(){return _79(_aB,_ay,_az,B(_9Y(_as,_aD,_aF,_av,_aA)));});}else{return new T5(0,_ax.a,E(new T3(0,_as,_aD,_aF)),_av,E(_az),E(_aA));}}else{return new F(function(){return _6s(_aB,_ay,B(_9Y(_as,_aD,_aF,_av,_az)),_aA);});}}}else{return new F(function(){return _6s(_aB,_ay,B(_ac(_as,_aD,_au,_av,_az)),_aA);});}}}else{return new F(function(){return _6s(_aB,_ay,B(_ar(_as,_at,_au,_av,_az)),_aA);});}}else{return new T5(0,1,E(new T3(0,_as,_at,_au)),_av,E(_6n),E(_6n));}},_aH=function(_aI,_aJ,_aK,_aL,_aM){var _aN=E(_aM);if(!_aN._){var _aO=_aN.c,_aP=_aN.d,_aQ=_aN.e,_aR=E(_aN.b),_aS=E(_aI),_aT=E(_aR.a);if(_aS>=_aT){if(_aS!=_aT){return new F(function(){return _79(_aR,_aO,_aP,B(_ar(_aS,_aJ,_aK,_aL,_aQ)));});}else{var _aU=E(_aJ),_aV=E(_aR.b);if(_aU>=_aV){if(_aU!=_aV){return new F(function(){return _79(_aR,_aO,_aP,B(_ac(_aS,_aU,_aK,_aL,_aQ)));});}else{var _aW=E(_aK),_aX=E(_aR.c);if(_aW>=_aX){if(_aW!=_aX){return new F(function(){return _79(_aR,_aO,_aP,B(_9Y(_aS,_aU,_aW,_aL,_aQ)));});}else{return new T5(0,_aN.a,E(new T3(0,_aS,_aU,_aW)),_aL,E(_aP),E(_aQ));}}else{return new F(function(){return _6s(_aR,_aO,B(_9Y(_aS,_aU,_aW,_aL,_aP)),_aQ);});}}}else{return new F(function(){return _6s(_aR,_aO,B(_ac(_aS,_aU,_aK,_aL,_aP)),_aQ);});}}}else{return new F(function(){return _6s(_aR,_aO,B(_ar(_aS,_aJ,_aK,_aL,_aP)),_aQ);});}}else{return new T5(0,1,E(new T3(0,_aI,_aJ,_aK)),_aL,E(_6n),E(_6n));}},_aY=function(_aZ,_b0,_b1,_b2){while(1){var _b3=E(_b2);if(!_b3._){var _b4=_b3.d,_b5=_b3.e,_b6=E(_b3.b),_b7=E(_b6.a);if(_aZ>=_b7){if(_aZ!=_b7){_b2=_b5;continue;}else{var _b8=E(_b6.b);if(_b0>=_b8){if(_b0!=_b8){_b2=_b5;continue;}else{var _b9=E(_b6.c);if(_b1>=_b9){if(_b1!=_b9){_b2=_b5;continue;}else{return new T1(1,_b3.c);}}else{_b2=_b4;continue;}}}else{_b2=_b4;continue;}}}else{_b2=_b4;continue;}}else{return __Z;}}},_ba=function(_bb,_bc,_bd,_be){while(1){var _bf=E(_be);if(!_bf._){var _bg=_bf.d,_bh=_bf.e,_bi=E(_bf.b),_bj=E(_bi.a);if(_bb>=_bj){if(_bb!=_bj){_be=_bh;continue;}else{var _bk=E(_bi.b);if(_bc>=_bk){if(_bc!=_bk){_be=_bh;continue;}else{var _bl=E(_bd),_bm=E(_bi.c);if(_bl>=_bm){if(_bl!=_bm){return new F(function(){return _aY(_bb,_bc,_bl,_bh);});}else{return new T1(1,_bf.c);}}else{return new F(function(){return _aY(_bb,_bc,_bl,_bg);});}}}else{_be=_bg;continue;}}}else{_be=_bg;continue;}}else{return __Z;}}},_bn=function(_bo,_bp,_bq,_br){while(1){var _bs=E(_br);if(!_bs._){var _bt=_bs.d,_bu=_bs.e,_bv=E(_bs.b),_bw=E(_bv.a);if(_bo>=_bw){if(_bo!=_bw){_br=_bu;continue;}else{var _bx=E(_bp),_by=E(_bv.b);if(_bx>=_by){if(_bx!=_by){return new F(function(){return _ba(_bo,_bx,_bq,_bu);});}else{var _bz=E(_bq),_bA=E(_bv.c);if(_bz>=_bA){if(_bz!=_bA){return new F(function(){return _aY(_bo,_bx,_bz,_bu);});}else{return new T1(1,_bs.c);}}else{return new F(function(){return _aY(_bo,_bx,_bz,_bt);});}}}else{return new F(function(){return _ba(_bo,_bx,_bq,_bt);});}}}else{_br=_bt;continue;}}else{return __Z;}}},_bB=function(_bC,_bD,_bE,_bF){var _bG=E(_bF);if(!_bG._){var _bH=_bG.d,_bI=_bG.e,_bJ=E(_bG.b),_bK=E(_bC),_bL=E(_bJ.a);if(_bK>=_bL){if(_bK!=_bL){return new F(function(){return _bn(_bK,_bD,_bE,_bI);});}else{var _bM=E(_bD),_bN=E(_bJ.b);if(_bM>=_bN){if(_bM!=_bN){return new F(function(){return _ba(_bK,_bM,_bE,_bI);});}else{var _bO=E(_bE),_bP=E(_bJ.c);if(_bO>=_bP){if(_bO!=_bP){return new F(function(){return _aY(_bK,_bM,_bO,_bI);});}else{return new T1(1,_bG.c);}}else{return new F(function(){return _aY(_bK,_bM,_bO,_bH);});}}}else{return new F(function(){return _ba(_bK,_bM,_bE,_bH);});}}}else{return new F(function(){return _bn(_bK,_bD,_bE,_bH);});}}else{return __Z;}},_bQ=function(_bR){while(1){var _bS=E(_bR);if(!_bS._){return __Z;}else{_bR=_bS.b;continue;}}},_bT=function(_bU,_bV){while(1){var _bW=E(_bU);if(!_bW._){return new T1(1,_bV);}else{var _bX=_bW.b;if(E(_bW.a)!=_bV){return new F(function(){return _bQ(_bX);});}else{_bU=_bX;continue;}}}},_bY=new T(function(){return B(unCStr("!!: negative index"));}),_bZ=new T(function(){return B(unCStr("Prelude."));}),_c0=new T(function(){return B(_5(_bZ,_bY));}),_c1=new T(function(){return B(err(_c0));}),_c2=new T(function(){return B(unCStr("!!: index too large"));}),_c3=new T(function(){return B(_5(_bZ,_c2));}),_c4=new T(function(){return B(err(_c3));}),_c5=function(_c6,_c7){while(1){var _c8=E(_c6);if(!_c8._){return E(_c4);}else{var _c9=E(_c7);if(!_c9){return E(_c8.a);}else{_c6=_c8.b;_c7=_c9-1|0;continue;}}}},_ca=function(_cb,_cc){if(_cc>=0){return new F(function(){return _c5(_cb,_cc);});}else{return E(_c1);}},_cd=function(_ce,_cf){while(1){var _cg=E(_ce);if(!_cg._){return E(_cf);}else{var _ch=_cf+1|0;_ce=_cg.b;_cf=_ch;continue;}}},_ci=new T(function(){return B(unCStr(": empty list"));}),_cj=function(_ck){return new F(function(){return err(B(_5(_bZ,new T(function(){return B(_5(_ck,_ci));},1))));});},_cl=new T(function(){return B(unCStr("head"));}),_cm=new T(function(){return B(_cj(_cl));}),_cn=function(_co){while(1){var _cp=B((function(_cq){var _cr=E(_cq);if(!_cr._){return __Z;}else{var _cs=_cr.b,_ct=E(_cr.a),_cu=E(_ct);if(!_cu){_co=_cs;return __continue;}else{return new T2(1,new T(function(){if(_cu<0){return  -_cu;}else{return E(_ct);}}),new T(function(){return B(_cn(_cs));}));}}})(_co));if(_cp!=__continue){return _cp;}}},_cv=function(_cw){return E(E(_cw).c);},_cx=new T2(1,_cv,_x),_cy=function(_cz){return E(E(_cz).b);},_cA=new T2(1,_cy,_cx),_cB=function(_cC){return E(E(_cC).a);},_cD=new T2(1,_cB,_cA),_cE=0,_cF=new T1(1,_cE),_cG=-1,_cH=new T1(1,_cG),_cI=1,_cJ=new T1(1,_cI),_cK=function(_cL,_cM,_cN,_cO,_cP){var _cQ=B(_4j(function(_cR){return B(A1(_cR,_cP))-B(A1(_cR,_cO))|0;},_cD)),_cS=B(_cn(_cQ)),_cT=E(_cS);if(!_cT._){var _cU=new T1(1,_cm);}else{var _cU=B(_bT(_cT.b,E(_cT.a)));}var _cV=function(_cW){var _cX=function(_cY){var _cZ=E(_cO),_d0=E(_cP),_d1=function(_d2){var _d3=function(_d4){var _d5=B(_ca(_cQ,_d4));return (_d5<=0)?(_d5>=0)?E(_cF):E(_cH):E(_cJ);},_d6=B(_d3(0));if(!_d6._){return __Z;}else{var _d7=B(_d3(1));if(!_d7._){return __Z;}else{var _d8=B(_d3(2));if(!_d8._){return __Z;}else{var _d9=E(_cU);return (_d9._==0)?__Z:new T1(1,new T5(0,_d6.a,_d7.a,_d8.a,_d9.a,_cZ));}}}};if(E(_cZ.a)!=E(_d0.a)){return new F(function(){return _d1(_);});}else{if(E(_cZ.b)!=E(_d0.b)){return new F(function(){return _d1(_);});}else{if(E(_cZ.c)!=E(_d0.c)){return new F(function(){return _d1(_);});}else{return new T1(1,new T5(0,_cE,_cE,_cE,_cE,_cZ));}}}};if(!E(_cL)){if(!E(_cM)){return __Z;}else{if(B(_cd(_cS,0))==2){return new F(function(){return _cX(_);});}else{return __Z;}}}else{var _da=B(_cd(_cS,0));if(_da==1){return new F(function(){return _cX(_);});}else{if(!E(_cM)){return __Z;}else{if(E(_da)==2){return new F(function(){return _cX(_);});}else{return __Z;}}}}},_db=E(_cU);if(!_db._){return new F(function(){return _cV(_);});}else{var _dc=E(_cN);if(!_dc._){return new F(function(){return _cV(_);});}else{if(E(_db.a)<=E(_dc.a)){return new F(function(){return _cV(_);});}else{return __Z;}}}},_dd=false,_de=true,_df=function(_dg,_dh,_di,_dj,_dk,_dl,_dm){var _dn=E(_dj);if(!_dn){return __Z;}else{var _do=new T(function(){return E(_di)+E(_dm)|0;}),_dp=new T(function(){return E(_dh)+E(_dl)|0;}),_dq=new T(function(){return E(_dg)+E(_dk)|0;});return new T2(1,new T3(0,_dq,_dp,_do),new T(function(){return B(_df(_dg,_dh,_di,_dn-1|0,_dq,_dp,_do));}));}},_dr=function(_ds,_dt,_du,_dv,_dw){var _dx=E(_dv);if(!_dx){return __Z;}else{var _dy=new T(function(){return E(_du)+E(E(_dw).c)|0;}),_dz=new T(function(){return E(_dt)+E(E(_dw).b)|0;}),_dA=new T(function(){return E(_ds)+E(E(_dw).a)|0;});return new T2(1,new T3(0,_dA,_dz,_dy),new T(function(){return B(_df(_ds,_dt,_du,_dx-1|0,_dA,_dz,_dy));}));}},_dB=function(_dC){var _dD=E(_dC);return new F(function(){return _dr(_dD.a,_dD.b,_dD.c,E(_dD.d),_dD.e);});},_dE=function(_dF,_dG,_dH,_dI,_dJ){while(1){var _dK=B((function(_dL,_dM,_dN,_dO,_dP){var _dQ=E(_dO);if(!_dQ._){return E(_dP);}else{var _dR=_dQ.b,_dS=E(_dQ.a),_dT=new T(function(){if(!B(_cd(_dR,0))){return __Z;}else{return new T1(1,new T(function(){var _dU=E(_dR);if(!_dU._){return E(_cm);}else{return E(_dU.a);}}));}}),_dV=_dL,_dW=_dM,_dX=B(_aH(_dS.a,_dS.b,_dS.c,new T5(0,_dL,_dM,_dd,_dT,_dN),_dP));_dF=_dV;_dG=_dW;_dH=new T1(1,_dS);_dI=_dR;_dJ=_dX;return __continue;}})(_dF,_dG,_dH,_dI,_dJ));if(_dK!=__continue){return _dK;}}},_dY=function(_dZ,_e0,_e1,_e2,_e3,_e4,_e5){var _e6=B(_cK(_dZ,_e0,_e1,_e3,_e4));if(!_e6._){return __Z;}else{var _e7=B(_dB(_e6.a)),_e8=function(_e9,_ea){while(1){var _eb=B((function(_ec,_ed){var _ee=E(_ec);if(!_ee._){return E(_ed);}else{_e9=_ee.b;_ea=new T(function(){var _ef=E(_ee.a);if(!B(_bB(_ef.a,_ef.b,_ef.c,_e5))._){return E(_ed);}else{return true;}},1);return __continue;}})(_e9,_ea));if(_eb!=__continue){return _eb;}}};if(!B(_e8(_e7,_dd))){var _eg=E(_e3),_eh=_eg.a,_ei=_eg.b,_ej=_eg.c,_ek=B(_bB(_eh,_ei,_ej,_e5));if(!_ek._){return __Z;}else{var _el=_ek.a,_em=E(_e2);if(!_em._){return __Z;}else{var _en=_em.a,_eo=new T(function(){return B(_aH(_eh,_ei,_ej,new T5(0,new T(function(){return E(E(_el).a);}),new T(function(){return E(E(_el).b);}),_de,new T1(1,new T(function(){var _ep=E(_e7);if(!_ep._){return E(_cm);}else{return E(_ep.a);}})),new T(function(){return E(E(_el).e);})),B(_dE(new T(function(){return E(E(_en).a);}),new T(function(){return E(E(_en).b);}),new T1(1,_eg),_e7,_e5))));});return new T1(1,_eo);}}}else{return __Z;}}},_eq=function(_er,_es,_et,_eu){while(1){var _ev=E(_eu);if(!_ev._){var _ew=_ev.d,_ex=_ev.e,_ey=E(_ev.b),_ez=E(_ey.a);if(_er>=_ez){if(_er!=_ez){_eu=_ex;continue;}else{var _eA=E(_ey.b);if(_es>=_eA){if(_es!=_eA){_eu=_ex;continue;}else{var _eB=E(_ey.c);if(_et>=_eB){if(_et!=_eB){_eu=_ex;continue;}else{return new T1(1,_ev.c);}}else{_eu=_ew;continue;}}}else{_eu=_ew;continue;}}}else{_eu=_ew;continue;}}else{return __Z;}}},_eC=function(_eD,_eE,_eF,_eG){while(1){var _eH=E(_eG);if(!_eH._){var _eI=_eH.d,_eJ=_eH.e,_eK=E(_eH.b),_eL=E(_eK.a);if(_eD>=_eL){if(_eD!=_eL){_eG=_eJ;continue;}else{var _eM=E(_eK.b);if(_eE>=_eM){if(_eE!=_eM){_eG=_eJ;continue;}else{var _eN=E(_eF),_eO=E(_eK.c);if(_eN>=_eO){if(_eN!=_eO){return new F(function(){return _eq(_eD,_eE,_eN,_eJ);});}else{return new T1(1,_eH.c);}}else{return new F(function(){return _eq(_eD,_eE,_eN,_eI);});}}}else{_eG=_eI;continue;}}}else{_eG=_eI;continue;}}else{return __Z;}}},_eP=function(_eQ,_eR,_eS,_eT){while(1){var _eU=E(_eT);if(!_eU._){var _eV=_eU.d,_eW=_eU.e,_eX=E(_eU.b),_eY=E(_eX.a);if(_eQ>=_eY){if(_eQ!=_eY){_eT=_eW;continue;}else{var _eZ=E(_eR),_f0=E(_eX.b);if(_eZ>=_f0){if(_eZ!=_f0){return new F(function(){return _eC(_eQ,_eZ,_eS,_eW);});}else{var _f1=E(_eS),_f2=E(_eX.c);if(_f1>=_f2){if(_f1!=_f2){return new F(function(){return _eq(_eQ,_eZ,_f1,_eW);});}else{return new T1(1,_eU.c);}}else{return new F(function(){return _eq(_eQ,_eZ,_f1,_eV);});}}}else{return new F(function(){return _eC(_eQ,_eZ,_eS,_eV);});}}}else{_eT=_eV;continue;}}else{return __Z;}}},_f3=function(_f4,_f5,_f6,_f7){var _f8=E(_f7);if(!_f8._){var _f9=_f8.d,_fa=_f8.e,_fb=E(_f8.b),_fc=E(_f4),_fd=E(_fb.a);if(_fc>=_fd){if(_fc!=_fd){return new F(function(){return _eP(_fc,_f5,_f6,_fa);});}else{var _fe=E(_f5),_ff=E(_fb.b);if(_fe>=_ff){if(_fe!=_ff){return new F(function(){return _eC(_fc,_fe,_f6,_fa);});}else{var _fg=E(_f6),_fh=E(_fb.c);if(_fg>=_fh){if(_fg!=_fh){return new F(function(){return _eq(_fc,_fe,_fg,_fa);});}else{return new T1(1,_f8.c);}}else{return new F(function(){return _eq(_fc,_fe,_fg,_f9);});}}}else{return new F(function(){return _eC(_fc,_fe,_f6,_f9);});}}}else{return new F(function(){return _eP(_fc,_f5,_f6,_f9);});}}else{return __Z;}},_fi=function(_fj,_fk){var _fl=E(_fj),_fm=E(_fk);return (E(_fl.a)!=E(_fm.a))?true:(E(_fl.b)!=E(_fm.b))?true:(E(_fl.c)!=E(_fm.c))?true:false;},_fn=function(_fo,_fp){return E(_fo)==E(_fp);},_fq=function(_fr,_fs,_ft,_fu,_fv,_fw){if(_fr!=_fu){return false;}else{if(E(_fs)!=E(_fv)){return false;}else{return new F(function(){return _fn(_ft,_fw);});}}},_fx=function(_fy,_fz){var _fA=E(_fy),_fB=E(_fz);return new F(function(){return _fq(E(_fA.a),_fA.b,_fA.c,E(_fB.a),_fB.b,_fB.c);});},_fC=new T2(0,_fx,_fi),_fD=function(_fE,_fF){return E(_fE)<E(_fF);},_fG=function(_fH,_fI,_fJ,_fK,_fL,_fM){if(_fH>=_fK){if(_fH!=_fK){return false;}else{var _fN=E(_fI),_fO=E(_fL);if(_fN>=_fO){if(_fN!=_fO){return false;}else{return new F(function(){return _fD(_fJ,_fM);});}}else{return true;}}}else{return true;}},_fP=function(_fQ,_fR){var _fS=E(_fQ),_fT=E(_fR);return new F(function(){return _fG(E(_fS.a),_fS.b,_fS.c,E(_fT.a),_fT.b,_fT.c);});},_fU=function(_fV,_fW){return E(_fV)<=E(_fW);},_fX=function(_fY,_fZ,_g0,_g1,_g2,_g3){if(_fY>=_g1){if(_fY!=_g1){return false;}else{var _g4=E(_fZ),_g5=E(_g2);if(_g4>=_g5){if(_g4!=_g5){return false;}else{return new F(function(){return _fU(_g0,_g3);});}}else{return true;}}}else{return true;}},_g6=function(_g7,_g8){var _g9=E(_g7),_ga=E(_g8);return new F(function(){return _fX(E(_g9.a),_g9.b,_g9.c,E(_ga.a),_ga.b,_ga.c);});},_gb=function(_gc,_gd){return E(_gc)>E(_gd);},_ge=function(_gf,_gg,_gh,_gi,_gj,_gk){if(_gf>=_gi){if(_gf!=_gi){return true;}else{var _gl=E(_gg),_gm=E(_gj);if(_gl>=_gm){if(_gl!=_gm){return true;}else{return new F(function(){return _gb(_gh,_gk);});}}else{return false;}}}else{return false;}},_gn=function(_go,_gp){var _gq=E(_go),_gr=E(_gp);return new F(function(){return _ge(E(_gq.a),_gq.b,_gq.c,E(_gr.a),_gr.b,_gr.c);});},_gs=function(_gt,_gu){return E(_gt)>=E(_gu);},_gv=function(_gw,_gx,_gy,_gz,_gA,_gB){if(_gw>=_gz){if(_gw!=_gz){return true;}else{var _gC=E(_gx),_gD=E(_gA);if(_gC>=_gD){if(_gC!=_gD){return true;}else{return new F(function(){return _gs(_gy,_gB);});}}else{return false;}}}else{return false;}},_gE=function(_gF,_gG){var _gH=E(_gF),_gI=E(_gG);return new F(function(){return _gv(E(_gH.a),_gH.b,_gH.c,E(_gI.a),_gI.b,_gI.c);});},_gJ=function(_gK,_gL){return (_gK>=_gL)?(_gK!=_gL)?2:1:0;},_gM=function(_gN,_gO){return new F(function(){return _gJ(E(_gN),E(_gO));});},_gP=function(_gQ,_gR,_gS,_gT,_gU,_gV){if(_gQ>=_gT){if(_gQ!=_gT){return 2;}else{var _gW=E(_gR),_gX=E(_gU);if(_gW>=_gX){if(_gW!=_gX){return 2;}else{return new F(function(){return _gM(_gS,_gV);});}}else{return 0;}}}else{return 0;}},_gY=function(_gZ,_h0){var _h1=E(_gZ),_h2=E(_h0);return new F(function(){return _gP(E(_h1.a),_h1.b,_h1.c,E(_h2.a),_h2.b,_h2.c);});},_h3=function(_h4,_h5){var _h6=E(_h4),_h7=E(_h6.a),_h8=E(_h5),_h9=E(_h8.a);if(_h7>=_h9){if(_h7!=_h9){return E(_h6);}else{var _ha=E(_h6.b),_hb=E(_h8.b);return (_ha>=_hb)?(_ha!=_hb)?E(_h6):(E(_h6.c)>E(_h8.c))?E(_h6):E(_h8):E(_h8);}}else{return E(_h8);}},_hc=function(_hd,_he){var _hf=E(_hd),_hg=E(_hf.a),_hh=E(_he),_hi=E(_hh.a);if(_hg>=_hi){if(_hg!=_hi){return E(_hh);}else{var _hj=E(_hf.b),_hk=E(_hh.b);return (_hj>=_hk)?(_hj!=_hk)?E(_hh):(E(_hf.c)>E(_hh.c))?E(_hh):E(_hf):E(_hf);}}else{return E(_hf);}},_hl={_:0,a:_fC,b:_gY,c:_fP,d:_g6,e:_gn,f:_gE,g:_h3,h:_hc},_hm=function(_hn,_ho){return new T5(0,1,E(_hn),_ho,E(_6n),E(_6n));},_hp=function(_hq,_hr,_hs){var _ht=E(_hs);if(!_ht._){return new F(function(){return _79(_ht.b,_ht.c,_ht.d,B(_hp(_hq,_hr,_ht.e)));});}else{return new F(function(){return _hm(_hq,_hr);});}},_hu=function(_hv,_hw,_hx){var _hy=E(_hx);if(!_hy._){return new F(function(){return _6s(_hy.b,_hy.c,B(_hu(_hv,_hw,_hy.d)),_hy.e);});}else{return new F(function(){return _hm(_hv,_hw);});}},_hz=function(_hA,_hB,_hC,_hD,_hE,_hF,_hG){return new F(function(){return _6s(_hD,_hE,B(_hu(_hA,_hB,_hF)),_hG);});},_hH=function(_hI,_hJ,_hK,_hL,_hM,_hN,_hO,_hP){var _hQ=E(_hK);if(!_hQ._){var _hR=_hQ.a,_hS=_hQ.b,_hT=_hQ.c,_hU=_hQ.d,_hV=_hQ.e;if((imul(3,_hR)|0)>=_hL){if((imul(3,_hL)|0)>=_hR){return new T5(0,(_hR+_hL|0)+1|0,E(_hI),_hJ,E(_hQ),E(new T5(0,_hL,E(_hM),_hN,E(_hO),E(_hP))));}else{return new F(function(){return _79(_hS,_hT,_hU,B(_hH(_hI,_hJ,_hV,_hL,_hM,_hN,_hO,_hP)));});}}else{return new F(function(){return _6s(_hM,_hN,B(_hW(_hI,_hJ,_hR,_hS,_hT,_hU,_hV,_hO)),_hP);});}}else{return new F(function(){return _hz(_hI,_hJ,_hL,_hM,_hN,_hO,_hP);});}},_hW=function(_hX,_hY,_hZ,_i0,_i1,_i2,_i3,_i4){var _i5=E(_i4);if(!_i5._){var _i6=_i5.a,_i7=_i5.b,_i8=_i5.c,_i9=_i5.d,_ia=_i5.e;if((imul(3,_hZ)|0)>=_i6){if((imul(3,_i6)|0)>=_hZ){return new T5(0,(_hZ+_i6|0)+1|0,E(_hX),_hY,E(new T5(0,_hZ,E(_i0),_i1,E(_i2),E(_i3))),E(_i5));}else{return new F(function(){return _79(_i0,_i1,_i2,B(_hH(_hX,_hY,_i3,_i6,_i7,_i8,_i9,_ia)));});}}else{return new F(function(){return _6s(_i7,_i8,B(_hW(_hX,_hY,_hZ,_i0,_i1,_i2,_i3,_i9)),_ia);});}}else{return new F(function(){return _hp(_hX,_hY,new T5(0,_hZ,E(_i0),_i1,E(_i2),E(_i3)));});}},_ib=function(_ic,_id,_ie,_if){var _ig=E(_ie);if(!_ig._){var _ih=_ig.a,_ii=_ig.b,_ij=_ig.c,_ik=_ig.d,_il=_ig.e,_im=E(_if);if(!_im._){var _in=_im.a,_io=_im.b,_ip=_im.c,_iq=_im.d,_ir=_im.e;if((imul(3,_ih)|0)>=_in){if((imul(3,_in)|0)>=_ih){return new T5(0,(_ih+_in|0)+1|0,E(_ic),_id,E(_ig),E(_im));}else{return new F(function(){return _79(_ii,_ij,_ik,B(_hH(_ic,_id,_il,_in,_io,_ip,_iq,_ir)));});}}else{return new F(function(){return _6s(_io,_ip,B(_hW(_ic,_id,_ih,_ii,_ij,_ik,_il,_iq)),_ir);});}}else{return new F(function(){return _hp(_ic,_id,_ig);});}}else{return new F(function(){return _hu(_ic,_id,_if);});}},_is=function(_it,_iu,_iv,_iw,_ix,_iy){var _iz=E(_it);if(_iz==1){var _iA=E(_iy);if(!_iA._){return new T3(0,new T5(0,1,E(new T3(0,_iu,_iv,_iw)),_ix,E(_6n),E(_6n)),_x,_x);}else{var _iB=E(E(_iA.a).a),_iC=E(_iB.a);if(_iu>=_iC){if(_iu!=_iC){return new T3(0,new T5(0,1,E(new T3(0,_iu,_iv,_iw)),_ix,E(_6n),E(_6n)),_x,_iA);}else{var _iD=E(_iB.b);return (_iv>=_iD)?(_iv!=_iD)?new T3(0,new T5(0,1,E(new T3(0,_iu,_iv,_iw)),_ix,E(_6n),E(_6n)),_x,_iA):(_iw<E(_iB.c))?new T3(0,new T5(0,1,E(new T3(0,_iu,_iv,_iw)),_ix,E(_6n),E(_6n)),_iA,_x):new T3(0,new T5(0,1,E(new T3(0,_iu,_iv,_iw)),_ix,E(_6n),E(_6n)),_x,_iA):new T3(0,new T5(0,1,E(new T3(0,_iu,_iv,_iw)),_ix,E(_6n),E(_6n)),_iA,_x);}}else{return new T3(0,new T5(0,1,E(new T3(0,_iu,_iv,_iw)),_ix,E(_6n),E(_6n)),_iA,_x);}}}else{var _iE=B(_is(_iz>>1,_iu,_iv,_iw,_ix,_iy)),_iF=_iE.a,_iG=_iE.c,_iH=E(_iE.b);if(!_iH._){return new T3(0,_iF,_x,_iG);}else{var _iI=E(_iH.a),_iJ=_iI.a,_iK=_iI.b,_iL=E(_iH.b);if(!_iL._){return new T3(0,new T(function(){return B(_hp(_iJ,_iK,_iF));}),_x,_iG);}else{var _iM=_iL.b,_iN=E(_iL.a),_iO=_iN.b,_iP=E(_iJ),_iQ=E(_iP.a),_iR=E(_iN.a),_iS=_iR.b,_iT=_iR.c,_iU=E(_iR.a);if(_iQ>=_iU){if(_iQ!=_iU){return new T3(0,_iF,_x,_iH);}else{var _iV=E(_iP.b),_iW=E(_iS);if(_iV>=_iW){if(_iV!=_iW){return new T3(0,_iF,_x,_iH);}else{var _iX=E(_iT);if(E(_iP.c)<_iX){var _iY=B(_is(_iz>>1,_iU,_iW,_iX,_iO,_iM));return new T3(0,new T(function(){return B(_ib(_iP,_iK,_iF,_iY.a));}),_iY.b,_iY.c);}else{return new T3(0,_iF,_x,_iH);}}}else{var _iZ=B(_j0(_iz>>1,_iU,_iW,_iT,_iO,_iM));return new T3(0,new T(function(){return B(_ib(_iP,_iK,_iF,_iZ.a));}),_iZ.b,_iZ.c);}}}else{var _j1=B(_j2(_iz>>1,_iU,_iS,_iT,_iO,_iM));return new T3(0,new T(function(){return B(_ib(_iP,_iK,_iF,_j1.a));}),_j1.b,_j1.c);}}}}},_j0=function(_j3,_j4,_j5,_j6,_j7,_j8){var _j9=E(_j3);if(_j9==1){var _ja=E(_j8);if(!_ja._){return new T3(0,new T5(0,1,E(new T3(0,_j4,_j5,_j6)),_j7,E(_6n),E(_6n)),_x,_x);}else{var _jb=E(E(_ja.a).a),_jc=E(_jb.a);if(_j4>=_jc){if(_j4!=_jc){return new T3(0,new T5(0,1,E(new T3(0,_j4,_j5,_j6)),_j7,E(_6n),E(_6n)),_x,_ja);}else{var _jd=E(_jb.b);if(_j5>=_jd){if(_j5!=_jd){return new T3(0,new T5(0,1,E(new T3(0,_j4,_j5,_j6)),_j7,E(_6n),E(_6n)),_x,_ja);}else{var _je=E(_j6);return (_je<E(_jb.c))?new T3(0,new T5(0,1,E(new T3(0,_j4,_j5,_je)),_j7,E(_6n),E(_6n)),_ja,_x):new T3(0,new T5(0,1,E(new T3(0,_j4,_j5,_je)),_j7,E(_6n),E(_6n)),_x,_ja);}}else{return new T3(0,new T5(0,1,E(new T3(0,_j4,_j5,_j6)),_j7,E(_6n),E(_6n)),_ja,_x);}}}else{return new T3(0,new T5(0,1,E(new T3(0,_j4,_j5,_j6)),_j7,E(_6n),E(_6n)),_ja,_x);}}}else{var _jf=B(_j0(_j9>>1,_j4,_j5,_j6,_j7,_j8)),_jg=_jf.a,_jh=_jf.c,_ji=E(_jf.b);if(!_ji._){return new T3(0,_jg,_x,_jh);}else{var _jj=E(_ji.a),_jk=_jj.a,_jl=_jj.b,_jm=E(_ji.b);if(!_jm._){return new T3(0,new T(function(){return B(_hp(_jk,_jl,_jg));}),_x,_jh);}else{var _jn=_jm.b,_jo=E(_jm.a),_jp=_jo.b,_jq=E(_jk),_jr=E(_jq.a),_js=E(_jo.a),_jt=_js.b,_ju=_js.c,_jv=E(_js.a);if(_jr>=_jv){if(_jr!=_jv){return new T3(0,_jg,_x,_ji);}else{var _jw=E(_jq.b),_jx=E(_jt);if(_jw>=_jx){if(_jw!=_jx){return new T3(0,_jg,_x,_ji);}else{var _jy=E(_ju);if(E(_jq.c)<_jy){var _jz=B(_is(_j9>>1,_jv,_jx,_jy,_jp,_jn));return new T3(0,new T(function(){return B(_ib(_jq,_jl,_jg,_jz.a));}),_jz.b,_jz.c);}else{return new T3(0,_jg,_x,_ji);}}}else{var _jA=B(_j0(_j9>>1,_jv,_jx,_ju,_jp,_jn));return new T3(0,new T(function(){return B(_ib(_jq,_jl,_jg,_jA.a));}),_jA.b,_jA.c);}}}else{var _jB=B(_j2(_j9>>1,_jv,_jt,_ju,_jp,_jn));return new T3(0,new T(function(){return B(_ib(_jq,_jl,_jg,_jB.a));}),_jB.b,_jB.c);}}}}},_j2=function(_jC,_jD,_jE,_jF,_jG,_jH){var _jI=E(_jC);if(_jI==1){var _jJ=E(_jH);if(!_jJ._){return new T3(0,new T5(0,1,E(new T3(0,_jD,_jE,_jF)),_jG,E(_6n),E(_6n)),_x,_x);}else{var _jK=E(E(_jJ.a).a),_jL=E(_jK.a);if(_jD>=_jL){if(_jD!=_jL){return new T3(0,new T5(0,1,E(new T3(0,_jD,_jE,_jF)),_jG,E(_6n),E(_6n)),_x,_jJ);}else{var _jM=E(_jE),_jN=E(_jK.b);if(_jM>=_jN){if(_jM!=_jN){return new T3(0,new T5(0,1,E(new T3(0,_jD,_jM,_jF)),_jG,E(_6n),E(_6n)),_x,_jJ);}else{var _jO=E(_jF);return (_jO<E(_jK.c))?new T3(0,new T5(0,1,E(new T3(0,_jD,_jM,_jO)),_jG,E(_6n),E(_6n)),_jJ,_x):new T3(0,new T5(0,1,E(new T3(0,_jD,_jM,_jO)),_jG,E(_6n),E(_6n)),_x,_jJ);}}else{return new T3(0,new T5(0,1,E(new T3(0,_jD,_jM,_jF)),_jG,E(_6n),E(_6n)),_jJ,_x);}}}else{return new T3(0,new T5(0,1,E(new T3(0,_jD,_jE,_jF)),_jG,E(_6n),E(_6n)),_jJ,_x);}}}else{var _jP=B(_j2(_jI>>1,_jD,_jE,_jF,_jG,_jH)),_jQ=_jP.a,_jR=_jP.c,_jS=E(_jP.b);if(!_jS._){return new T3(0,_jQ,_x,_jR);}else{var _jT=E(_jS.a),_jU=_jT.a,_jV=_jT.b,_jW=E(_jS.b);if(!_jW._){return new T3(0,new T(function(){return B(_hp(_jU,_jV,_jQ));}),_x,_jR);}else{var _jX=_jW.b,_jY=E(_jW.a),_jZ=_jY.b,_k0=E(_jU),_k1=E(_k0.a),_k2=E(_jY.a),_k3=_k2.b,_k4=_k2.c,_k5=E(_k2.a);if(_k1>=_k5){if(_k1!=_k5){return new T3(0,_jQ,_x,_jS);}else{var _k6=E(_k0.b),_k7=E(_k3);if(_k6>=_k7){if(_k6!=_k7){return new T3(0,_jQ,_x,_jS);}else{var _k8=E(_k4);if(E(_k0.c)<_k8){var _k9=B(_is(_jI>>1,_k5,_k7,_k8,_jZ,_jX));return new T3(0,new T(function(){return B(_ib(_k0,_jV,_jQ,_k9.a));}),_k9.b,_k9.c);}else{return new T3(0,_jQ,_x,_jS);}}}else{var _ka=B(_j0(_jI>>1,_k5,_k7,_k4,_jZ,_jX));return new T3(0,new T(function(){return B(_ib(_k0,_jV,_jQ,_ka.a));}),_ka.b,_ka.c);}}}else{var _kb=B(_j2(_jI>>1,_k5,_k3,_k4,_jZ,_jX));return new T3(0,new T(function(){return B(_ib(_k0,_jV,_jQ,_kb.a));}),_kb.b,_kb.c);}}}}},_kc=function(_kd,_ke,_kf,_kg,_kh){var _ki=E(_kh);if(!_ki._){var _kj=_ki.c,_kk=_ki.d,_kl=_ki.e,_km=E(_ki.b),_kn=E(_km.a);if(_kd>=_kn){if(_kd!=_kn){return new F(function(){return _79(_km,_kj,_kk,B(_kc(_kd,_ke,_kf,_kg,_kl)));});}else{var _ko=E(_km.b);if(_ke>=_ko){if(_ke!=_ko){return new F(function(){return _79(_km,_kj,_kk,B(_kc(_kd,_ke,_kf,_kg,_kl)));});}else{var _kp=E(_km.c);if(_kf>=_kp){if(_kf!=_kp){return new F(function(){return _79(_km,_kj,_kk,B(_kc(_kd,_ke,_kf,_kg,_kl)));});}else{return new T5(0,_ki.a,E(new T3(0,_kd,_ke,_kf)),_kg,E(_kk),E(_kl));}}else{return new F(function(){return _6s(_km,_kj,B(_kc(_kd,_ke,_kf,_kg,_kk)),_kl);});}}}else{return new F(function(){return _6s(_km,_kj,B(_kc(_kd,_ke,_kf,_kg,_kk)),_kl);});}}}else{return new F(function(){return _6s(_km,_kj,B(_kc(_kd,_ke,_kf,_kg,_kk)),_kl);});}}else{return new T5(0,1,E(new T3(0,_kd,_ke,_kf)),_kg,E(_6n),E(_6n));}},_kq=function(_kr,_ks,_kt,_ku,_kv){var _kw=E(_kv);if(!_kw._){var _kx=_kw.c,_ky=_kw.d,_kz=_kw.e,_kA=E(_kw.b),_kB=E(_kA.a);if(_kr>=_kB){if(_kr!=_kB){return new F(function(){return _79(_kA,_kx,_ky,B(_kq(_kr,_ks,_kt,_ku,_kz)));});}else{var _kC=E(_kA.b);if(_ks>=_kC){if(_ks!=_kC){return new F(function(){return _79(_kA,_kx,_ky,B(_kq(_kr,_ks,_kt,_ku,_kz)));});}else{var _kD=E(_kt),_kE=E(_kA.c);if(_kD>=_kE){if(_kD!=_kE){return new F(function(){return _79(_kA,_kx,_ky,B(_kc(_kr,_ks,_kD,_ku,_kz)));});}else{return new T5(0,_kw.a,E(new T3(0,_kr,_ks,_kD)),_ku,E(_ky),E(_kz));}}else{return new F(function(){return _6s(_kA,_kx,B(_kc(_kr,_ks,_kD,_ku,_ky)),_kz);});}}}else{return new F(function(){return _6s(_kA,_kx,B(_kq(_kr,_ks,_kt,_ku,_ky)),_kz);});}}}else{return new F(function(){return _6s(_kA,_kx,B(_kq(_kr,_ks,_kt,_ku,_ky)),_kz);});}}else{return new T5(0,1,E(new T3(0,_kr,_ks,_kt)),_ku,E(_6n),E(_6n));}},_kF=function(_kG,_kH,_kI,_kJ,_kK){var _kL=E(_kK);if(!_kL._){var _kM=_kL.c,_kN=_kL.d,_kO=_kL.e,_kP=E(_kL.b),_kQ=E(_kP.a);if(_kG>=_kQ){if(_kG!=_kQ){return new F(function(){return _79(_kP,_kM,_kN,B(_kF(_kG,_kH,_kI,_kJ,_kO)));});}else{var _kR=E(_kH),_kS=E(_kP.b);if(_kR>=_kS){if(_kR!=_kS){return new F(function(){return _79(_kP,_kM,_kN,B(_kq(_kG,_kR,_kI,_kJ,_kO)));});}else{var _kT=E(_kI),_kU=E(_kP.c);if(_kT>=_kU){if(_kT!=_kU){return new F(function(){return _79(_kP,_kM,_kN,B(_kc(_kG,_kR,_kT,_kJ,_kO)));});}else{return new T5(0,_kL.a,E(new T3(0,_kG,_kR,_kT)),_kJ,E(_kN),E(_kO));}}else{return new F(function(){return _6s(_kP,_kM,B(_kc(_kG,_kR,_kT,_kJ,_kN)),_kO);});}}}else{return new F(function(){return _6s(_kP,_kM,B(_kq(_kG,_kR,_kI,_kJ,_kN)),_kO);});}}}else{return new F(function(){return _6s(_kP,_kM,B(_kF(_kG,_kH,_kI,_kJ,_kN)),_kO);});}}else{return new T5(0,1,E(new T3(0,_kG,_kH,_kI)),_kJ,E(_6n),E(_6n));}},_kV=function(_kW,_kX,_kY,_kZ,_l0){var _l1=E(_l0);if(!_l1._){var _l2=_l1.c,_l3=_l1.d,_l4=_l1.e,_l5=E(_l1.b),_l6=E(_kW),_l7=E(_l5.a);if(_l6>=_l7){if(_l6!=_l7){return new F(function(){return _79(_l5,_l2,_l3,B(_kF(_l6,_kX,_kY,_kZ,_l4)));});}else{var _l8=E(_kX),_l9=E(_l5.b);if(_l8>=_l9){if(_l8!=_l9){return new F(function(){return _79(_l5,_l2,_l3,B(_kq(_l6,_l8,_kY,_kZ,_l4)));});}else{var _la=E(_kY),_lb=E(_l5.c);if(_la>=_lb){if(_la!=_lb){return new F(function(){return _79(_l5,_l2,_l3,B(_kc(_l6,_l8,_la,_kZ,_l4)));});}else{return new T5(0,_l1.a,E(new T3(0,_l6,_l8,_la)),_kZ,E(_l3),E(_l4));}}else{return new F(function(){return _6s(_l5,_l2,B(_kc(_l6,_l8,_la,_kZ,_l3)),_l4);});}}}else{return new F(function(){return _6s(_l5,_l2,B(_kq(_l6,_l8,_kY,_kZ,_l3)),_l4);});}}}else{return new F(function(){return _6s(_l5,_l2,B(_kF(_l6,_kX,_kY,_kZ,_l3)),_l4);});}}else{return new T5(0,1,E(new T3(0,_kW,_kX,_kY)),_kZ,E(_6n),E(_6n));}},_lc=function(_ld,_le){while(1){var _lf=E(_le);if(!_lf._){return E(_ld);}else{var _lg=E(_lf.a),_lh=E(_lg.a),_li=B(_kV(_lh.a,_lh.b,_lh.c,_lg.b,_ld));_ld=_li;_le=_lf.b;continue;}}},_lj=function(_lk,_ll,_lm,_ln,_lo,_lp){return new F(function(){return _lc(B(_kV(_ll,_lm,_ln,_lo,_lk)),_lp);});},_lq=function(_lr,_ls,_lt){var _lu=E(_ls),_lv=E(_lu.a);return new F(function(){return _lc(B(_kV(_lv.a,_lv.b,_lv.c,_lu.b,_lr)),_lt);});},_lw=function(_lx,_ly,_lz){var _lA=E(_lz);if(!_lA._){return E(_ly);}else{var _lB=E(_lA.a),_lC=_lB.a,_lD=_lB.b,_lE=E(_lA.b);if(!_lE._){return new F(function(){return _hp(_lC,_lD,_ly);});}else{var _lF=E(_lE.a),_lG=E(_lC),_lH=_lG.b,_lI=_lG.c,_lJ=E(_lG.a),_lK=E(_lF.a),_lL=_lK.b,_lM=_lK.c,_lN=E(_lK.a),_lO=function(_lP){var _lQ=B(_j2(_lx,_lN,_lL,_lM,_lF.b,_lE.b)),_lR=_lQ.a,_lS=E(_lQ.c);if(!_lS._){return new F(function(){return _lw(_lx<<1,B(_ib(_lG,_lD,_ly,_lR)),_lQ.b);});}else{return new F(function(){return _lq(B(_ib(_lG,_lD,_ly,_lR)),_lS.a,_lS.b);});}};if(_lJ>=_lN){if(_lJ!=_lN){return new F(function(){return _lj(_ly,_lJ,_lH,_lI,_lD,_lE);});}else{var _lT=E(_lH),_lU=E(_lL);if(_lT>=_lU){if(_lT!=_lU){return new F(function(){return _lj(_ly,_lJ,_lT,_lI,_lD,_lE);});}else{var _lV=E(_lI);if(_lV<E(_lM)){return new F(function(){return _lO(_);});}else{return new F(function(){return _lj(_ly,_lJ,_lT,_lV,_lD,_lE);});}}}else{return new F(function(){return _lO(_);});}}}else{return new F(function(){return _lO(_);});}}}},_lW=function(_lX,_lY,_lZ,_m0,_m1,_m2,_m3){var _m4=E(_m3);if(!_m4._){return new F(function(){return _hp(new T3(0,_lZ,_m0,_m1),_m2,_lY);});}else{var _m5=E(_m4.a),_m6=E(_m5.a),_m7=_m6.b,_m8=_m6.c,_m9=E(_m6.a),_ma=function(_mb){var _mc=B(_j2(_lX,_m9,_m7,_m8,_m5.b,_m4.b)),_md=_mc.a,_me=E(_mc.c);if(!_me._){return new F(function(){return _lw(_lX<<1,B(_ib(new T3(0,_lZ,_m0,_m1),_m2,_lY,_md)),_mc.b);});}else{return new F(function(){return _lq(B(_ib(new T3(0,_lZ,_m0,_m1),_m2,_lY,_md)),_me.a,_me.b);});}};if(_lZ>=_m9){if(_lZ!=_m9){return new F(function(){return _lj(_lY,_lZ,_m0,_m1,_m2,_m4);});}else{var _mf=E(_m7);if(_m0>=_mf){if(_m0!=_mf){return new F(function(){return _lj(_lY,_lZ,_m0,_m1,_m2,_m4);});}else{var _mg=E(_m1);if(_mg<E(_m8)){return new F(function(){return _ma(_);});}else{return new F(function(){return _lj(_lY,_lZ,_m0,_mg,_m2,_m4);});}}}else{return new F(function(){return _ma(_);});}}}else{return new F(function(){return _ma(_);});}}},_mh=function(_mi,_mj,_mk,_ml,_mm,_mn,_mo){var _mp=E(_mo);if(!_mp._){return new F(function(){return _hp(new T3(0,_mk,_ml,_mm),_mn,_mj);});}else{var _mq=E(_mp.a),_mr=E(_mq.a),_ms=_mr.b,_mt=_mr.c,_mu=E(_mr.a),_mv=function(_mw){var _mx=B(_j2(_mi,_mu,_ms,_mt,_mq.b,_mp.b)),_my=_mx.a,_mz=E(_mx.c);if(!_mz._){return new F(function(){return _lw(_mi<<1,B(_ib(new T3(0,_mk,_ml,_mm),_mn,_mj,_my)),_mx.b);});}else{return new F(function(){return _lq(B(_ib(new T3(0,_mk,_ml,_mm),_mn,_mj,_my)),_mz.a,_mz.b);});}};if(_mk>=_mu){if(_mk!=_mu){return new F(function(){return _lj(_mj,_mk,_ml,_mm,_mn,_mp);});}else{var _mA=E(_ml),_mB=E(_ms);if(_mA>=_mB){if(_mA!=_mB){return new F(function(){return _lj(_mj,_mk,_mA,_mm,_mn,_mp);});}else{var _mC=E(_mm);if(_mC<E(_mt)){return new F(function(){return _mv(_);});}else{return new F(function(){return _lj(_mj,_mk,_mA,_mC,_mn,_mp);});}}}else{return new F(function(){return _mv(_);});}}}else{return new F(function(){return _mv(_);});}}},_mD=function(_mE,_mF,_mG,_mH,_mI,_mJ,_mK){var _mL=E(_mK);if(!_mL._){return new F(function(){return _hp(new T3(0,_mG,_mH,_mI),_mJ,_mF);});}else{var _mM=E(_mL.a),_mN=E(_mM.a),_mO=_mN.b,_mP=_mN.c,_mQ=E(_mN.a),_mR=function(_mS){var _mT=B(_j2(_mE,_mQ,_mO,_mP,_mM.b,_mL.b)),_mU=_mT.a,_mV=E(_mT.c);if(!_mV._){return new F(function(){return _lw(_mE<<1,B(_ib(new T3(0,_mG,_mH,_mI),_mJ,_mF,_mU)),_mT.b);});}else{return new F(function(){return _lq(B(_ib(new T3(0,_mG,_mH,_mI),_mJ,_mF,_mU)),_mV.a,_mV.b);});}};if(_mG>=_mQ){if(_mG!=_mQ){return new F(function(){return _lj(_mF,_mG,_mH,_mI,_mJ,_mL);});}else{var _mW=E(_mO);if(_mH>=_mW){if(_mH!=_mW){return new F(function(){return _lj(_mF,_mG,_mH,_mI,_mJ,_mL);});}else{if(_mI<E(_mP)){return new F(function(){return _mR(_);});}else{return new F(function(){return _lj(_mF,_mG,_mH,_mI,_mJ,_mL);});}}}else{return new F(function(){return _mR(_);});}}}else{return new F(function(){return _mR(_);});}}},_mX=function(_mY){var _mZ=E(_mY);if(!_mZ._){return new T0(1);}else{var _n0=E(_mZ.a),_n1=_n0.a,_n2=_n0.b,_n3=E(_mZ.b);if(!_n3._){return new T5(0,1,E(_n1),_n2,E(_6n),E(_6n));}else{var _n4=_n3.b,_n5=E(_n3.a),_n6=_n5.b,_n7=E(_n1),_n8=E(_n7.a),_n9=E(_n5.a),_na=_n9.b,_nb=_n9.c,_nc=E(_n9.a);if(_n8>=_nc){if(_n8!=_nc){return new F(function(){return _lj(new T5(0,1,E(_n7),_n2,E(_6n),E(_6n)),_nc,_na,_nb,_n6,_n4);});}else{var _nd=E(_n7.b),_ne=E(_na);if(_nd>=_ne){if(_nd!=_ne){return new F(function(){return _lj(new T5(0,1,E(_n7),_n2,E(_6n),E(_6n)),_nc,_ne,_nb,_n6,_n4);});}else{var _nf=E(_nb);if(E(_n7.c)<_nf){return new F(function(){return _mD(1,new T5(0,1,E(_n7),_n2,E(_6n),E(_6n)),_nc,_ne,_nf,_n6,_n4);});}else{return new F(function(){return _lj(new T5(0,1,E(_n7),_n2,E(_6n),E(_6n)),_nc,_ne,_nf,_n6,_n4);});}}}else{return new F(function(){return _lW(1,new T5(0,1,E(_n7),_n2,E(_6n),E(_6n)),_nc,_ne,_nb,_n6,_n4);});}}}else{return new F(function(){return _mh(1,new T5(0,1,E(_n7),_n2,E(_6n),E(_6n)),_nc,_na,_nb,_n6,_n4);});}}}},_ng=function(_nh,_ni){var _nj=function(_nk,_nl){while(1){var _nm=B((function(_nn,_no){var _np=E(_no);if(!_np._){_nk=new T2(1,new T2(0,new T(function(){return B(A1(_nh,_np.b));}),_np.c),new T(function(){return B(_nj(_nn,_np.e));}));_nl=_np.d;return __continue;}else{return E(_nn);}})(_nk,_nl));if(_nm!=__continue){return _nm;}}};return new F(function(){return _mX(B(_nj(_x,_ni)));});},_nq=function(_nr,_ns,_nt,_nu){while(1){var _nv=E(_nu);if(!_nv._){var _nw=_nv.d,_nx=_nv.e,_ny=E(_nv.b),_nz=E(_ny.a);if(_nr>=_nz){if(_nr!=_nz){_nu=_nx;continue;}else{var _nA=E(_ny.b);if(_ns>=_nA){if(_ns!=_nA){_nu=_nx;continue;}else{var _nB=E(_ny.c);if(_nt>=_nB){if(_nt!=_nB){_nu=_nx;continue;}else{return new T1(1,_nv.c);}}else{_nu=_nw;continue;}}}else{_nu=_nw;continue;}}}else{_nu=_nw;continue;}}else{return __Z;}}},_nC=function(_nD,_nE,_nF,_nG){while(1){var _nH=E(_nG);if(!_nH._){var _nI=_nH.d,_nJ=_nH.e,_nK=E(_nH.b),_nL=E(_nK.a);if(_nD>=_nL){if(_nD!=_nL){_nG=_nJ;continue;}else{var _nM=E(_nK.b);if(_nE>=_nM){if(_nE!=_nM){_nG=_nJ;continue;}else{var _nN=E(_nF),_nO=E(_nK.c);if(_nN>=_nO){if(_nN!=_nO){return new F(function(){return _nq(_nD,_nE,_nN,_nJ);});}else{return new T1(1,_nH.c);}}else{return new F(function(){return _nq(_nD,_nE,_nN,_nI);});}}}else{_nG=_nI;continue;}}}else{_nG=_nI;continue;}}else{return __Z;}}},_nP=function(_nQ,_nR,_nS,_nT){while(1){var _nU=E(_nT);if(!_nU._){var _nV=_nU.d,_nW=_nU.e,_nX=E(_nU.b),_nY=E(_nX.a);if(_nQ>=_nY){if(_nQ!=_nY){_nT=_nW;continue;}else{var _nZ=E(_nR),_o0=E(_nX.b);if(_nZ>=_o0){if(_nZ!=_o0){return new F(function(){return _nC(_nQ,_nZ,_nS,_nW);});}else{var _o1=E(_nS),_o2=E(_nX.c);if(_o1>=_o2){if(_o1!=_o2){return new F(function(){return _nq(_nQ,_nZ,_o1,_nW);});}else{return new T1(1,_nU.c);}}else{return new F(function(){return _nq(_nQ,_nZ,_o1,_nV);});}}}else{return new F(function(){return _nC(_nQ,_nZ,_nS,_nV);});}}}else{_nT=_nV;continue;}}else{return __Z;}}},_o3=function(_o4,_o5,_o6,_o7){var _o8=E(_o7);if(!_o8._){var _o9=_o8.d,_oa=_o8.e,_ob=E(_o8.b),_oc=E(_o4),_od=E(_ob.a);if(_oc>=_od){if(_oc!=_od){return new F(function(){return _nP(_oc,_o5,_o6,_oa);});}else{var _oe=E(_o5),_of=E(_ob.b);if(_oe>=_of){if(_oe!=_of){return new F(function(){return _nC(_oc,_oe,_o6,_oa);});}else{var _og=E(_o6),_oh=E(_ob.c);if(_og>=_oh){if(_og!=_oh){return new F(function(){return _nq(_oc,_oe,_og,_oa);});}else{return new T1(1,_o8.c);}}else{return new F(function(){return _nq(_oc,_oe,_og,_o9);});}}}else{return new F(function(){return _nC(_oc,_oe,_o6,_o9);});}}}else{return new F(function(){return _nP(_oc,_o5,_o6,_o9);});}}else{return __Z;}},_oi=__Z,_oj=function(_ok){return new T3(0,new T(function(){return E(E(_ok).a)+1|0;}),new T(function(){return B(_cy(_ok));}),new T(function(){return B(_cv(_ok));}));},_ol=function(_om,_on,_oo,_op,_oq,_or){var _os=E(_om);if(!_os._){var _ot=_os.a,_ou=_os.b,_ov=_os.c,_ow=_os.d,_ox=_os.e;if((imul(3,_ot)|0)>=_on){if((imul(3,_on)|0)>=_ot){return new F(function(){return _86(_os,new T5(0,_on,E(_oo),_op,E(_oq),E(_or)));});}else{return new F(function(){return _79(_ou,_ov,_ow,B(_ol(_ox,_on,_oo,_op,_oq,_or)));});}}else{return new F(function(){return _6s(_oo,_op,B(_oy(_ot,_ou,_ov,_ow,_ox,_oq)),_or);});}}else{return new T5(0,_on,E(_oo),_op,E(_oq),E(_or));}},_oy=function(_oz,_oA,_oB,_oC,_oD,_oE){var _oF=E(_oE);if(!_oF._){var _oG=_oF.a,_oH=_oF.b,_oI=_oF.c,_oJ=_oF.d,_oK=_oF.e;if((imul(3,_oz)|0)>=_oG){if((imul(3,_oG)|0)>=_oz){return new F(function(){return _86(new T5(0,_oz,E(_oA),_oB,E(_oC),E(_oD)),_oF);});}else{return new F(function(){return _79(_oA,_oB,_oC,B(_ol(_oD,_oG,_oH,_oI,_oJ,_oK)));});}}else{return new F(function(){return _6s(_oH,_oI,B(_oy(_oz,_oA,_oB,_oC,_oD,_oJ)),_oK);});}}else{return new T5(0,_oz,E(_oA),_oB,E(_oC),E(_oD));}},_oL=function(_oM,_oN){var _oO=E(_oM);if(!_oO._){var _oP=_oO.a,_oQ=_oO.b,_oR=_oO.c,_oS=_oO.d,_oT=_oO.e,_oU=E(_oN);if(!_oU._){var _oV=_oU.a,_oW=_oU.b,_oX=_oU.c,_oY=_oU.d,_oZ=_oU.e;if((imul(3,_oP)|0)>=_oV){if((imul(3,_oV)|0)>=_oP){return new F(function(){return _86(_oO,_oU);});}else{return new F(function(){return _79(_oQ,_oR,_oS,B(_ol(_oT,_oV,_oW,_oX,_oY,_oZ)));});}}else{return new F(function(){return _6s(_oW,_oX,B(_oy(_oP,_oQ,_oR,_oS,_oT,_oY)),_oZ);});}}else{return E(_oO);}}else{return E(_oN);}},_p0=function(_p1,_p2){var _p3=E(_p2);if(!_p3._){var _p4=_p3.b,_p5=_p3.c,_p6=_p3.d,_p7=_p3.e;if(!B(A2(_p1,_p4,_p5))){return new F(function(){return _oL(B(_p0(_p1,_p6)),B(_p0(_p1,_p7)));});}else{return new F(function(){return _ib(_p4,_p5,B(_p0(_p1,_p6)),B(_p0(_p1,_p7)));});}}else{return new T0(1);}},_p8=function(_p9){return E(E(_p9).a);},_pa=function(_pb){return E(E(_pb).b);},_pc=function(_pd,_pe){return new T5(0,new T(function(){return B(_p8(_pe));}),new T(function(){return B(_pa(_pe));}),_de,_2s,new T1(1,_pd));},_pf=function(_pg){return E(E(_pg).e);},_ph=function(_pi,_pj){return new T5(0,new T(function(){return B(_p8(_pj));}),new T(function(){return B(_pa(_pj));}),_de,new T1(1,new T(function(){return B(_oj(_pi));})),new T(function(){return B(_pf(_pj));}));},_pk=function(_pl,_pm){return (E(E(_pm).d)._==0)?true:false;},_pn=function(_po,_pp){var _pq=E(_pp);if(!_pq._){var _pr=_pq.b;return new T5(0,_pq.a,E(_pr),new T(function(){return B(A2(_po,_pr,_pq.c));}),E(B(_pn(_po,_pq.d))),E(B(_pn(_po,_pq.e))));}else{return new T0(1);}},_ps=function(_pt){return E(E(_pt).b);},_pu=function(_pv,_pw,_px){var _py=E(_pw);if(!_py._){return E(_px);}else{var _pz=function(_pA,_pB){while(1){var _pC=E(_pB);if(!_pC._){var _pD=_pC.b,_pE=_pC.e;switch(B(A3(_ps,_pv,_pA,_pD))){case 0:return new F(function(){return _ib(_pD,_pC.c,B(_pz(_pA,_pC.d)),_pE);});break;case 1:return E(_pE);default:_pB=_pE;continue;}}else{return new T0(1);}}};return new F(function(){return _pz(_py.a,_px);});}},_pF=function(_pG,_pH,_pI){var _pJ=E(_pH);if(!_pJ._){return E(_pI);}else{var _pK=function(_pL,_pM){while(1){var _pN=E(_pM);if(!_pN._){var _pO=_pN.b,_pP=_pN.d;switch(B(A3(_ps,_pG,_pO,_pL))){case 0:return new F(function(){return _ib(_pO,_pN.c,_pP,B(_pK(_pL,_pN.e)));});break;case 1:return E(_pP);default:_pM=_pP;continue;}}else{return new T0(1);}}};return new F(function(){return _pK(_pJ.a,_pI);});}},_pQ=function(_pR,_pS,_pT,_pU){var _pV=E(_pS),_pW=E(_pU);if(!_pW._){var _pX=_pW.b,_pY=_pW.c,_pZ=_pW.d,_q0=_pW.e;switch(B(A3(_ps,_pR,_pV,_pX))){case 0:return new F(function(){return _6s(_pX,_pY,B(_pQ(_pR,_pV,_pT,_pZ)),_q0);});break;case 1:return E(_pW);default:return new F(function(){return _79(_pX,_pY,_pZ,B(_pQ(_pR,_pV,_pT,_q0)));});}}else{return new T5(0,1,E(_pV),_pT,E(_6n),E(_6n));}},_q1=function(_q2,_q3,_q4,_q5){return new F(function(){return _pQ(_q2,_q3,_q4,_q5);});},_q6=function(_q7){return E(E(_q7).d);},_q8=function(_q9){return E(E(_q9).f);},_qa=function(_qb,_qc,_qd,_qe){var _qf=E(_qc);if(!_qf._){var _qg=E(_qd);if(!_qg._){return E(_qe);}else{var _qh=function(_qi,_qj){while(1){var _qk=E(_qj);if(!_qk._){if(!B(A3(_q8,_qb,_qk.b,_qi))){return E(_qk);}else{_qj=_qk.d;continue;}}else{return new T0(1);}}};return new F(function(){return _qh(_qg.a,_qe);});}}else{var _ql=_qf.a,_qm=E(_qd);if(!_qm._){var _qn=function(_qo,_qp){while(1){var _qq=E(_qp);if(!_qq._){if(!B(A3(_q6,_qb,_qq.b,_qo))){return E(_qq);}else{_qp=_qq.e;continue;}}else{return new T0(1);}}};return new F(function(){return _qn(_ql,_qe);});}else{var _qr=function(_qs,_qt,_qu){while(1){var _qv=E(_qu);if(!_qv._){var _qw=_qv.b;if(!B(A3(_q6,_qb,_qw,_qs))){if(!B(A3(_q8,_qb,_qw,_qt))){return E(_qv);}else{_qu=_qv.d;continue;}}else{_qu=_qv.e;continue;}}else{return new T0(1);}}};return new F(function(){return _qr(_ql,_qm.a,_qe);});}}},_qx=function(_qy,_qz,_qA,_qB,_qC){var _qD=E(_qC);if(!_qD._){var _qE=_qD.b,_qF=_qD.c,_qG=_qD.d,_qH=_qD.e,_qI=E(_qB);if(!_qI._){var _qJ=_qI.b,_qK=function(_qL){var _qM=new T1(1,E(_qJ));return new F(function(){return _ib(_qJ,_qI.c,B(_qx(_qy,_qz,_qM,_qI.d,B(_qa(_qy,_qz,_qM,_qD)))),B(_qx(_qy,_qM,_qA,_qI.e,B(_qa(_qy,_qM,_qA,_qD)))));});};if(!E(_qG)._){return new F(function(){return _qK(_);});}else{if(!E(_qH)._){return new F(function(){return _qK(_);});}else{return new F(function(){return _q1(_qy,_qE,_qF,_qI);});}}}else{return new F(function(){return _ib(_qE,_qF,B(_pu(_qy,_qz,_qG)),B(_pF(_qy,_qA,_qH)));});}}else{return E(_qB);}},_qN=function(_qO,_qP,_qQ,_qR,_qS,_qT,_qU,_qV,_qW,_qX,_qY,_qZ,_r0){var _r1=function(_r2){var _r3=new T1(1,E(_qS));return new F(function(){return _ib(_qS,_qT,B(_qx(_qO,_qP,_r3,_qU,B(_qa(_qO,_qP,_r3,new T5(0,_qW,E(_qX),_qY,E(_qZ),E(_r0)))))),B(_qx(_qO,_r3,_qQ,_qV,B(_qa(_qO,_r3,_qQ,new T5(0,_qW,E(_qX),_qY,E(_qZ),E(_r0)))))));});};if(!E(_qZ)._){return new F(function(){return _r1(_);});}else{if(!E(_r0)._){return new F(function(){return _r1(_);});}else{return new F(function(){return _q1(_qO,_qX,_qY,new T5(0,_qR,E(_qS),_qT,E(_qU),E(_qV)));});}}},_r4=function(_r5){var _r6=function(_r7,_r8){return (B(_o3(new T(function(){return E(E(_r7).a)+1|0;}),new T(function(){return E(E(_r7).b);}),new T(function(){return E(E(_r7).c);}),_r5))._==0)?true:false;},_r9=B(_p0(_r6,B(_p0(_pk,_r5)))),_ra=function(_rb,_rc,_rd,_re,_rf,_rg){var _rh=E(_r5);if(!_rh._){return new F(function(){return _qN(_hl,_oi,_oi,_rb,_rc,_rd,_re,_rf,_rh.a,_rh.b,_rh.c,_rh.d,_rh.e);});}else{return E(_rg);}},_ri=B(_ng(_oj,B(_pn(_pc,_r9))));if(!_ri._){var _rj=_ri.a,_rk=_ri.b,_rl=_ri.c,_rm=_ri.d,_rn=_ri.e,_ro=B(_pn(_ph,_r9));if(!_ro._){var _rp=B(_qN(_hl,_oi,_oi,_rj,_rk,_rl,_rm,_rn,_ro.a,_ro.b,_ro.c,_ro.d,_ro.e));if(!_rp._){return new F(function(){return _ra(_rp.a,_rp.b,_rp.c,_rp.d,_rp.e,_rp);});}else{return E(_r5);}}else{return new F(function(){return _ra(_rj,_rk,_rl,_rm,_rn,_ri);});}}else{var _rq=B(_pn(_ph,_r9));if(!_rq._){return new F(function(){return _ra(_rq.a,_rq.b,_rq.c,_rq.d,_rq.e,_rq);});}else{return E(_r5);}}},_rr=function(_rs,_rt){while(1){var _ru=E(_rs);if(!_ru._){return (E(_rt)._==0)?true:false;}else{var _rv=E(_rt);if(!_rv._){return false;}else{if(E(_ru.a)!=E(_rv.a)){return false;}else{_rs=_ru.b;_rt=_rv.b;continue;}}}}},_rw=new T2(1,_cv,_x),_rx=new T2(1,_cy,_rw),_ry=new T2(1,_cB,_rx),_rz=new T2(1,_x,_x),_rA=function(_rB,_rC){var _rD=function(_rE,_rF){var _rG=E(_rE);if(!_rG._){return E(_rF);}else{var _rH=_rG.a,_rI=E(_rF);if(!_rI._){return E(_rG);}else{var _rJ=_rI.a;return (B(A2(_rB,_rH,_rJ))==2)?new T2(1,_rJ,new T(function(){return B(_rD(_rG,_rI.b));})):new T2(1,_rH,new T(function(){return B(_rD(_rG.b,_rI));}));}}},_rK=function(_rL){var _rM=E(_rL);if(!_rM._){return __Z;}else{var _rN=E(_rM.b);return (_rN._==0)?E(_rM):new T2(1,new T(function(){return B(_rD(_rM.a,_rN.a));}),new T(function(){return B(_rK(_rN.b));}));}},_rO=new T(function(){return B(_rP(B(_rK(_x))));}),_rP=function(_rQ){while(1){var _rR=E(_rQ);if(!_rR._){return E(_rO);}else{if(!E(_rR.b)._){return E(_rR.a);}else{_rQ=B(_rK(_rR));continue;}}}},_rS=new T(function(){return B(_rT(_x));}),_rU=function(_rV,_rW,_rX){while(1){var _rY=B((function(_rZ,_s0,_s1){var _s2=E(_s1);if(!_s2._){return new T2(1,new T2(1,_rZ,_s0),_rS);}else{var _s3=_s2.a;if(B(A2(_rB,_rZ,_s3))==2){var _s4=new T2(1,_rZ,_s0);_rV=_s3;_rW=_s4;_rX=_s2.b;return __continue;}else{return new T2(1,new T2(1,_rZ,_s0),new T(function(){return B(_rT(_s2));}));}}})(_rV,_rW,_rX));if(_rY!=__continue){return _rY;}}},_s5=function(_s6,_s7,_s8){while(1){var _s9=B((function(_sa,_sb,_sc){var _sd=E(_sc);if(!_sd._){return new T2(1,new T(function(){return B(A1(_sb,new T2(1,_sa,_x)));}),_rS);}else{var _se=_sd.a,_sf=_sd.b;switch(B(A2(_rB,_sa,_se))){case 0:_s6=_se;_s7=function(_sg){return new F(function(){return A1(_sb,new T2(1,_sa,_sg));});};_s8=_sf;return __continue;case 1:_s6=_se;_s7=function(_sh){return new F(function(){return A1(_sb,new T2(1,_sa,_sh));});};_s8=_sf;return __continue;default:return new T2(1,new T(function(){return B(A1(_sb,new T2(1,_sa,_x)));}),new T(function(){return B(_rT(_sd));}));}}})(_s6,_s7,_s8));if(_s9!=__continue){return _s9;}}},_rT=function(_si){var _sj=E(_si);if(!_sj._){return E(_rz);}else{var _sk=_sj.a,_sl=E(_sj.b);if(!_sl._){return new T2(1,_sj,_x);}else{var _sm=_sl.a,_sn=_sl.b;if(B(A2(_rB,_sk,_sm))==2){return new F(function(){return _rU(_sm,new T2(1,_sk,_x),_sn);});}else{return new F(function(){return _s5(_sm,function(_so){return new T2(1,_sk,_so);},_sn);});}}}};return new F(function(){return _rP(B(_rT(_rC)));});},_sp=function(_sq,_sr,_ss,_st,_su){if(!B(_rr(B(_rA(_gM,B(_4j(function(_sv){var _sw=B(A1(_sv,_st))-B(A1(_sv,_ss))|0;return (_sw<0)? -_sw:_sw;},_ry)))),_sq))){return __Z;}else{var _sx=E(_sr);if(!_sx._){return __Z;}else{var _sy=_sx.a,_sz=new T(function(){var _sA=E(_ss),_sB=E(_st),_sC=new T(function(){return E(E(_sy).a);}),_sD=new T(function(){return E(E(_sy).b);});return B(_aH(_sA.a,_sA.b,_sA.c,new T5(0,_sC,_sD,_de,new T1(1,_sB),new T(function(){return E(E(_sy).e);})),B(_aH(_sB.a,_sB.b,_sB.c,new T5(0,_sC,_sD,_de,_2s,new T1(1,_sA)),_su))));});return new T1(1,_sz);}}},_sE=function(_sF){return (E(_sF)==0)?1:0;},_sG=1,_sH=new T1(1,_sG),_sI=2,_sJ=new T2(1,_sI,_x),_sK=new T2(1,_sG,_sJ),_sL=0,_sM=new T2(1,_sL,_sK),_sN=new T1(0,_de),_sO=function(_sP,_sQ,_sR,_sS,_sT){var _sU=E(_sS);if(!_sU._){return __Z;}else{var _sV=E(_sP),_sW=_sV.a,_sX=_sV.b,_sY=_sV.c,_sZ=B(_f3(_sW,_sX,_sY,_sT));if(!_sZ._){var _t0=false;}else{var _t0=E(E(_sZ.a).c);}var _t1=function(_t2){var _t3=E(_sU.a),_t4=B(_f3(_t3.a,_t3.b,_t3.c,_sT));if(!_t4._){return __Z;}else{var _t5=E(_t4.a),_t6=function(_t7){return new T1(1,new T4(0,new T(function(){return E(_sQ)+1|0;}),new T(function(){return B(_sE(_sR));}),_2s,new T(function(){return B(_r4(_t7));})));},_t8=E(_t5.b);switch(_t8._){case 0:var _t9=B(_dY(new T(function(){if(!E(_t0)){return true;}else{return false;}},1),_t0,new T1(1,new T(function(){if(!E(_t8.a)){if(!E(_t0)){return E(_sI);}else{return E(_sG);}}else{return E(_sG);}})),new T1(1,new T5(0,_t5.a,_sN,_dd,_2s,_2s)),_t3,_sV,new T(function(){return B(_9R(_sW,_sX,_sY,_sT));})));if(!_t9._){return __Z;}else{return new F(function(){return _t6(_t9.a);});}break;case 1:var _ta=B(_dY(_de,_dd,_2s,_t4,_t3,_sV,new T(function(){return B(_9R(_sW,_sX,_sY,_sT));})));if(!_ta._){return __Z;}else{return new F(function(){return _t6(_ta.a);});}break;case 2:var _tb=B(_sp(_sM,_t4,_t3,_sV,new T(function(){return B(_9R(_sW,_sX,_sY,_sT));},1)));if(!_tb._){return __Z;}else{return new F(function(){return _t6(_tb.a);});}break;case 3:var _tc=B(_dY(_dd,_de,_2s,_t4,_t3,_sV,new T(function(){return B(_9R(_sW,_sX,_sY,_sT));})));if(!_tc._){return __Z;}else{return new F(function(){return _t6(_tc.a);});}break;case 4:var _td=B(_dY(_de,_de,_2s,_t4,_t3,_sV,new T(function(){return B(_9R(_sW,_sX,_sY,_sT));})));if(!_td._){return __Z;}else{return new F(function(){return _t6(_td.a);});}break;default:var _te=B(_dY(_de,_de,_sH,_t4,_t3,_sV,new T(function(){return B(_9R(_sW,_sX,_sY,_sT));})));if(!_te._){return __Z;}else{return new F(function(){return _t6(_te.a);});}}}};if(!E(_t0)){return new F(function(){return _t1(_);});}else{var _tf=B(_68(_sW,_sX,_sY,_sT));if(!_tf._){return new F(function(){return _t1(_);});}else{if(!E(E(_tf.a).a)){if(!E(_sR)){return __Z;}else{return new F(function(){return _t1(_);});}}else{if(!E(_sR)){return new F(function(){return _t1(_);});}else{return __Z;}}}}}},_tg=function(_th){return E(E(_th).d);},_ti=function(_tj){return E(E(_tj).b);},_tk=function(_tl){return E(E(_tl).a);},_tm=function(_tn,_to){return new T4(0,new T(function(){return B(_tk(_to));}),new T(function(){return B(_ti(_to));}),new T(function(){var _tp=E(_to),_tq=_tp.b,_tr=E(_tn),_ts=B(_68(_tr.a,_tr.b,_tr.c,_tp.d));if(!_ts._){return __Z;}else{var _tt=E(_ts.a),_tu=_tt.d;if(!E(_tt.a)){if(!E(_tq)){if(!E(_tu)._){return new T1(1,_tr);}else{return __Z;}}else{return __Z;}}else{if(!E(_tq)){return __Z;}else{if(!E(_tu)._){return new T1(1,_tr);}else{return __Z;}}}}}),new T(function(){return B(_tg(_to));}));},_tv=function(_){return _0;},_tw=function(_tx,_ty){return E(_tx)!=E(_ty);},_tz=new T2(0,_fn,_tw),_tA=function(_tB,_tC){var _tD=E(_tB),_tE=E(_tC);return (_tD>_tE)?E(_tD):E(_tE);},_tF=function(_tG,_tH){var _tI=E(_tG),_tJ=E(_tH);return (_tI>_tJ)?E(_tJ):E(_tI);},_tK={_:0,a:_tz,b:_gM,c:_fD,d:_fU,e:_gb,f:_gs,g:_tA,h:_tF},_tL=function(_tM){return E(E(_tM).a);},_tN=function(_tO){return E(E(_tO).a);},_tP=function(_tQ){return E(E(_tQ).a);},_tR=109,_tS=100,_tT=99,_tU=108,_tV=120,_tW=118,_tX=105,_tY=function(_tZ){if(_tZ<1000){if(_tZ<900){if(_tZ<500){if(_tZ<400){if(_tZ<100){if(_tZ<90){if(_tZ<50){if(_tZ<40){if(_tZ<10){if(_tZ<9){if(_tZ<5){if(_tZ<4){return (_tZ<1)?__Z:new T2(1,_tX,new T(function(){return B(_tY(_tZ-1|0));}));}else{return new F(function(){return unAppCStr("iv",new T(function(){return B(_tY(_tZ-4|0));}));});}}else{return new T2(1,_tW,new T(function(){return B(_tY(_tZ-5|0));}));}}else{return new F(function(){return unAppCStr("ix",new T(function(){return B(_tY(_tZ-9|0));}));});}}else{return new T2(1,_tV,new T(function(){return B(_tY(_tZ-10|0));}));}}else{return new F(function(){return unAppCStr("xl",new T(function(){return B(_tY(_tZ-40|0));}));});}}else{return new T2(1,_tU,new T(function(){return B(_tY(_tZ-50|0));}));}}else{return new F(function(){return unAppCStr("xc",new T(function(){return B(_tY(_tZ-90|0));}));});}}else{return new T2(1,_tT,new T(function(){return B(_tY(_tZ-100|0));}));}}else{return new F(function(){return unAppCStr("cd",new T(function(){return B(_tY(_tZ-400|0));}));});}}else{return new T2(1,_tS,new T(function(){return B(_tY(_tZ-500|0));}));}}else{return new F(function(){return unAppCStr("cm",new T(function(){return B(_tY(_tZ-900|0));}));});}}else{return new T2(1,_tR,new T(function(){return B(_tY(_tZ-1000|0));}));}},_u0=new T(function(){return B(unCStr("+ - "));}),_u1=new T(function(){return B(unCStr("+"));}),_u2=new T(function(){return B(_5(_u0,_u1));}),_u3=function(_u4){var _u5=E(_u4);if(_u5==1){return E(_u2);}else{return new F(function(){return _5(_u0,new T(function(){return B(_u3(_u5-1|0));},1));});}},_u6=function(_u7,_u8){return new T2(1,_u7,_u8);},_u9=function(_ua){return E(E(_ua).c);},_ub=function(_uc){return E(E(_uc).c);},_ud=function(_ue){return E(E(_ue).b);},_uf=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_ug=function(_uh){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_f(9,_uh,_x));}))));});},_ui=function(_uj){return E(E(_uj).a);},_uk=function(_ul,_um){var _un=E(_ul);return new F(function(){return _68(_un.a,_un.b,_un.c,_um);});},_uo=function(_up,_uq){return new F(function(){return _uk(_up,E(_uq).d);});},_ur=35,_us=new T(function(){return B(unCStr("   "));}),_ut=42,_uu=32,_uv=new T(function(){return B(unCStr("&thinsp;"));}),_uw=new T(function(){return B(unCStr("&#9818;"));}),_ux=new T(function(){return B(unCStr("&#9816"));}),_uy=new T(function(){return B(unCStr("&#9814;"));}),_uz=new T(function(){return B(unCStr("&#9817;"));}),_uA=new T(function(){return B(unCStr("&#9819;"));}),_uB=new T(function(){return B(unCStr("&#9821;"));}),_uC=new T(function(){return B(unCStr("&#9822;"));}),_uD=new T(function(){return B(unCStr("&#9820;"));}),_uE=new T(function(){return B(unCStr("&#9823;"));}),_uF=new T(function(){return B(unCStr("&#9812;"));}),_uG=new T(function(){return B(unCStr("&#9813;"));}),_uH=new T(function(){return B(unCStr("&#9815;"));}),_uI=function(_uJ){var _uK=E(_uJ);if(!_uK._){return E(_us);}else{var _uL=E(_uK.a),_uM=_uL.b,_uN=_uL.c,_uO=_uL.d;if(!E(_uL.a)){switch(E(_uM)._){case 0:return new F(function(){return _5(_uz,new T2(1,new T(function(){if(!E(_uO)._){return E(_uu);}else{if(!E(_uN)){return E(_ut);}else{return E(_ur);}}}),_uv));});break;case 1:return new F(function(){return _5(_uy,new T2(1,new T(function(){if(!E(_uO)._){return E(_uu);}else{if(!E(_uN)){return E(_ut);}else{return E(_ur);}}}),_uv));});break;case 2:return new F(function(){return _5(_ux,new T2(1,new T(function(){if(!E(_uO)._){return E(_uu);}else{if(!E(_uN)){return E(_ut);}else{return E(_ur);}}}),_uv));});break;case 3:return new F(function(){return _5(_uH,new T2(1,new T(function(){if(!E(_uO)._){return E(_uu);}else{if(!E(_uN)){return E(_ut);}else{return E(_ur);}}}),_uv));});break;case 4:return new F(function(){return _5(_uG,new T2(1,new T(function(){if(!E(_uO)._){return E(_uu);}else{if(!E(_uN)){return E(_ut);}else{return E(_ur);}}}),_uv));});break;default:return new F(function(){return _5(_uF,new T2(1,new T(function(){if(!E(_uO)._){return E(_uu);}else{if(!E(_uN)){return E(_ut);}else{return E(_ur);}}}),_uv));});}}else{switch(E(_uM)._){case 0:return new F(function(){return _5(_uE,new T2(1,new T(function(){if(!E(_uO)._){return E(_uu);}else{if(!E(_uN)){return E(_ut);}else{return E(_ur);}}}),_uv));});break;case 1:return new F(function(){return _5(_uD,new T2(1,new T(function(){if(!E(_uO)._){return E(_uu);}else{if(!E(_uN)){return E(_ut);}else{return E(_ur);}}}),_uv));});break;case 2:return new F(function(){return _5(_uC,new T2(1,new T(function(){if(!E(_uO)._){return E(_uu);}else{if(!E(_uN)){return E(_ut);}else{return E(_ur);}}}),_uv));});break;case 3:return new F(function(){return _5(_uB,new T2(1,new T(function(){if(!E(_uO)._){return E(_uu);}else{if(!E(_uN)){return E(_ut);}else{return E(_ur);}}}),_uv));});break;case 4:return new F(function(){return _5(_uA,new T2(1,new T(function(){if(!E(_uO)._){return E(_uu);}else{if(!E(_uN)){return E(_ut);}else{return E(_ur);}}}),_uv));});break;default:return new F(function(){return _5(_uw,new T2(1,new T(function(){if(!E(_uO)._){return E(_uu);}else{if(!E(_uN)){return E(_ut);}else{return E(_ur);}}}),_uv));});}}}},_uP=new T(function(){return eval("(function(e,p,v){e.setAttribute(p, v);})");}),_uQ=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_uR=function(_uS){return E(E(_uS).b);},_uT=new T(function(){return B(unCStr("header"));}),_uU=new T(function(){return B(unCStr("(( "));}),_uV=new T(function(){return B(unCStr(" ))"));}),_uW=new T(function(){return B(unCStr("<< "));}),_uX=new T(function(){return B(unCStr(" >>"));}),_uY=new T(function(){return B(unCStr("white_piece"));}),_uZ=new T(function(){return B(unCStr("black_piece"));}),_v0=new T(function(){return B(unCStr("id"));}),_v1=new T(function(){return B(unCStr("selected"));}),_v2=function(_v3){return E(E(_v3).g);},_v4=new T(function(){return B(unCStr("maximum"));}),_v5=new T(function(){return B(_cj(_v4));}),_v6=function(_v7,_v8){var _v9=E(_v8);if(!_v9._){return E(_v5);}else{var _va=new T(function(){return B(_v2(_v7));}),_vb=function(_vc,_vd){while(1){var _ve=E(_vc);if(!_ve._){return E(_vd);}else{var _vf=B(A2(_va,E(_vd),_ve.a));_vc=_ve.b;_vd=_vf;continue;}}};return new F(function(){return _vb(_v9.b,_v9.a);});}},_vg=new T(function(){return B(_v6(_tK,_x));}),_vh=8,_vi=new T(function(){return B(unCStr("span"));}),_vj=new T(function(){return toJSStr(E(_vi));}),_vk=3,_vl=new T(function(){return B(unCStr("innerHTML"));}),_vm=new T(function(){return B(unCStr("|"));}),_vn=new T(function(){return B(unCStr("class"));}),_vo=new T(function(){return B(unCStr("background"));}),_vp=new T(function(){return toJSStr(E(_vi));}),_vq=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_vr=function(_vs,_vt){var _vu=function(_){return new F(function(){return __app1(E(_vq),E(_vt));});};return new F(function(){return A2(_uR,_vs,_vu);});},_vv=function(_vw){return new T1(2,_vw);},_vx=new T(function(){return B(unCStr("br"));}),_vy=new T(function(){return toJSStr(E(_vx));}),_vz=function(_vA){return new F(function(){return A3(_ui,B(_tL(B(_tN(B(_tP(_vA)))))),_vv,new T(function(){return B(_vr(_vA,_vy));}));});},_vB=new T(function(){return eval("(function(s){return document.createTextNode(s);})");}),_vC=function(_vD,_vE){var _vF=function(_){return new F(function(){return __app1(E(_vB),E(_vE));});};return new F(function(){return A2(_uR,_vD,_vF);});},_vG=function(_vH){return E(E(_vH).d);},_vI=32,_vJ=new T2(1,_vI,_x),_vK=function(_vL){var _vM=E(_vL);return (_vM==1)?E(_vJ):new T2(1,_vI,new T(function(){return B(_vK(_vM-1|0));}));},_vN=function(_vO,_vP){var _vQ=new T(function(){return B(_vC(_vO,new T(function(){var _vR=E(_vP);if(0>=_vR){return toJSStr(_x);}else{return toJSStr(B(_vK(_vR)));}},1)));});return new F(function(){return A3(_ui,B(_tL(B(_tN(B(_tP(_vO)))))),_vv,_vQ);});},_vS=function(_vT){var _vU=97+E(_vT)|0;if(_vU>>>0>1114111){return new F(function(){return _ug(_vU);});}else{return _vU;}},_vV=function(_vW){var _vX=49+E(_vW)|0;if(_vX>>>0>1114111){return new F(function(){return _ug(_vX);});}else{return _vX;}},_vY=new T(function(){return B(unCStr("n"));}),_vZ=function(_w0,_w1,_w2,_w3,_w4,_w5,_w6){var _w7=function(_w8){var _w9=new T(function(){switch(E(_w3)){case 0:return E(E(_w6).a)+1|0;break;case 1:return E(_vh);break;default:return E(_vh);}}),_wa=new T(function(){var _wb=E(_w9);if(0>=_wb){return E(_u1);}else{return B(_u3(_wb));}}),_wc=new T(function(){var _wd=function(_we){switch(E(_w4)){case 0:var _wf=E(_we);if(!_wf){return new F(function(){return _cd(_vY,0);});}else{return new F(function(){return _cd(B(_tY(_wf)),0);});}break;case 1:return 1;default:return 1;}};switch(E(_w4)){case 0:var _wg=E(E(_w6).a);if(0<=_wg){var _wh=function(_wi){return new T2(1,new T(function(){return B(_wd(_wi));}),new T(function(){if(_wi!=_wg){return B(_wh(_wi+1|0));}else{return __Z;}}));},_wj=E(B(_v6(_tK,B(_wh(0)))));if(_wj==2147483647){return E(_46);}else{return _wj+1|0;}}else{var _wk=E(_vg);if(_wk==2147483647){return E(_46);}else{return _wk+1|0;}}break;case 1:var _wl=function(_wm){return new T2(1,new T(function(){return B(_wd(_wm));}),new T(function(){var _wn=E(_wm);if(_wn==7){return __Z;}else{return B(_wl(_wn+1|0));}}));},_wo=E(B(_v6(_tK,B(_wl(0)))));if(_wo==2147483647){return E(_46);}else{return _wo+1|0;}break;default:var _wp=function(_wq){return new T2(1,new T(function(){return B(_wd(_wq));}),new T(function(){var _wr=E(_wq);if(_wr==7){return __Z;}else{return B(_wp(_wr+1|0));}}));},_ws=E(B(_v6(_tK,B(_wp(0)))));if(_ws==2147483647){return E(_46);}else{return _ws+1|0;}}}),_wt=function(_wu){var _wv=new T(function(){var _ww=B(_tP(_wu)),_wx=new T(function(){return B(_vG(_ww));}),_wy=function(_wz){var _wA=new T(function(){var _wB=new T(function(){var _wC=function(_){var _wD=__app3(E(_uP),E(_wz),toJSStr(E(_vn)),toJSStr(E(_vo)));return new F(function(){return _tv(_);});};return B(A2(_uR,_wu,_wC));});return B(A3(_ub,_ww,_wB,new T(function(){return B(A1(_wx,new T1(2,_wz)));})));}),_wE=new T(function(){var _wF=function(_){var _wG=__app3(E(_uQ),E(_wz),toJSStr(E(_vl)),toJSStr(E(_wa)));return new F(function(){return _tv(_);});};return B(A2(_uR,_wu,_wF));});return new F(function(){return A3(_ub,_ww,_wE,_wA);});};return B(A3(_ud,_ww,new T(function(){return B(_vr(_wu,_vp));}),_wy));});return new T2(1,new T(function(){return B(_vN(_wu,_wc));}),new T2(1,_wv,new T2(1,new T(function(){return B(_vz(_wu));}),_x)));},_wH=B(_tP(_w0)),_wI=new T(function(){var _wJ=function(_wK){if(0<=_wK){var _wL=new T(function(){return B(_vr(_w0,_vj));}),_wM=new T(function(){return B(_vG(_wH));}),_wN=function(_wO){var _wP=new T(function(){return B(_vN(_w0,new T(function(){switch(E(_w3)){case 0:var _wQ=E(_wO);if(!_wQ){return 4-B(_cd(_vY,0))|0;}else{return 4-B(_cd(B(_tY(_wQ)),0))|0;}break;case 1:return E(_vk);break;default:return E(_vk);}},1)));}),_wR=new T(function(){var _wS=new T(function(){var _wT=new T(function(){switch(E(_w3)){case 0:var _wU=E(_wO);if(!_wU){return toJSStr(E(_vY));}else{return toJSStr(B(_tY(_wU)));}break;case 1:return toJSStr(new T2(1,new T(function(){var _wV=97+_wO|0;if(_wV>>>0>1114111){return B(_ug(_wV));}else{return _wV;}}),_x));break;default:return toJSStr(new T2(1,new T(function(){var _wW=49+_wO|0;if(_wW>>>0>1114111){return B(_ug(_wW));}else{return _wW;}}),_x));}},1);return B(_vC(_w0,_wT));}),_wX=function(_wY){var _wZ=new T(function(){var _x0=new T(function(){var _x1=function(_x2){var _x3=function(_){var _x4=__app2(E(_uf),E(_x2),E(_wY));return new F(function(){return _tv(_);});};return new F(function(){return A2(_uR,_w0,_x3);});};return B(A3(_ud,_wH,_wS,_x1));});return B(A3(_ub,_wH,_x0,new T(function(){return B(A1(_wM,new T3(1,_w3,_wO,_wY)));})));}),_x5=new T(function(){var _x6=function(_){var _x7=__app3(E(_uP),E(_wY),toJSStr(E(_vn)),toJSStr(E(_uT)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_x6));});return new F(function(){return A3(_ub,_wH,_x5,_wZ);});};return B(A3(_ud,_wH,_wL,_wX));});return new T2(1,_wR,new T2(1,_wP,new T(function(){if(_wO!=_wK){return B(_wN(_wO+1|0));}else{return __Z;}})));};return new F(function(){return _wN(0);});}else{return __Z;}};switch(E(_w3)){case 0:return B(_wJ(E(E(_w6).a)));break;case 1:return B(_wJ(7));break;default:return B(_wJ(7));}}),_x8=new T(function(){return B(_vN(_w0,new T(function(){return E(_wc)+2|0;},1)));}),_x9=B(_5(new T2(1,_x8,_wI),new T2(1,new T(function(){return B(_vz(_w0));}),new T(function(){return B(_wt(_w0));})))),_xa=B(_tN(_wH)),_xb=new T(function(){return B(_tL(_xa));}),_xc=new T(function(){var _xd=new T(function(){var _xe=new T(function(){var _xf=new T(function(){var _xg=new T(function(){var _xh=E(_w2)+1|0,_xi=function(_xj){var _xk=B(_tP(_w0));if(_xh<=_xj){if(_xh>=0){var _xl=new T(function(){return B(_vG(_xk));}),_xm=function(_xn){var _xo=new T(function(){var _xp=new T(function(){var _xq=function(_){var _xr=__app3(E(_uP),E(_xn),toJSStr(E(_vn)),toJSStr(E(_uT)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_xq));});return B(A3(_ub,_xk,_xp,new T(function(){return B(A1(_xl,new T3(1,_w1,_xh,_xn)));})));}),_xs=new T(function(){var _xt=function(_){var _xu=__app3(E(_uQ),E(_xn),toJSStr(E(_vl)),toJSStr(E(_uX)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_xt));});return new F(function(){return A3(_ub,_xk,_xs,_xo);});};return new F(function(){return A3(_ud,_xk,new T(function(){return B(_vr(_w0,_vp));}),_xm);});}else{var _xv=new T(function(){return B(_vG(_xk));}),_xw=function(_xx){var _xy=new T(function(){var _xz=new T(function(){var _xA=function(_){var _xB=__app3(E(_uP),E(_xx),toJSStr(E(_vn)),toJSStr(E(_uT)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_xA));});return B(A3(_ub,_xk,_xz,new T(function(){return B(A1(_xv,new T1(2,_xx)));})));}),_xC=new T(function(){var _xD=function(_){var _xE=__app3(E(_uQ),E(_xx),toJSStr(E(_vl)),toJSStr(E(_uU)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_xD));});return new F(function(){return A3(_ub,_xk,_xC,_xy);});};return new F(function(){return A3(_ud,_xk,new T(function(){return B(_vr(_w0,_vp));}),_xw);});}}else{var _xF=new T(function(){return B(_vG(_xk));}),_xG=function(_xH){var _xI=new T(function(){var _xJ=new T(function(){var _xK=function(_){var _xL=__app3(E(_uP),E(_xH),toJSStr(E(_vn)),toJSStr(E(_uT)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_xK));});return B(A3(_ub,_xk,_xJ,new T(function(){return B(A1(_xF,new T1(2,_xH)));})));}),_xM=new T(function(){var _xN=function(_){var _xO=__app3(E(_uQ),E(_xH),toJSStr(E(_vl)),toJSStr(E(_uV)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_xN));});return new F(function(){return A3(_ub,_xk,_xM,_xI);});};return new F(function(){return A3(_ud,_xk,new T(function(){return B(_vr(_w0,_vp));}),_xG);});}};switch(E(_w1)){case 0:return B(_xi(E(E(_w6).a)));break;case 1:return B(_xi(7));break;default:return B(_xi(7));}});return B(A3(_ui,_xb,_u6,_xg));});return B(A3(_u9,_xa,_xf,new T(function(){return B(A2(_vG,_wH,_x));})));}),_xP=new T(function(){var _xQ=new T(function(){var _xR=new T(function(){switch(E(_w1)){case 0:var _xS=E(_w2);if(!_xS){return E(_vY);}else{return B(_tY(_xS));}break;case 1:return new T2(1,new T(function(){return B(_vS(_w2));}),_x);break;default:return new T2(1,new T(function(){return B(_vV(_w2));}),_x);}}),_xT=new T(function(){return B(_vG(_wH));}),_xU=function(_xV){var _xW=new T(function(){var _xX=new T(function(){var _xY=function(_){var _xZ=__app3(E(_uP),E(_xV),toJSStr(E(_vn)),toJSStr(E(_uT)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_xY));});return B(A3(_ub,_wH,_xX,new T(function(){return B(A1(_xT,new T1(2,_xV)));})));}),_y0=new T(function(){var _y1=function(_){var _y2=__app3(E(_uQ),E(_xV),toJSStr(E(_vl)),toJSStr(E(_xR)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_y1));});return new F(function(){return A3(_ub,_wH,_y0,_xW);});};return B(A3(_ud,_wH,new T(function(){return B(_vr(_w0,_vp));}),_xU));});return B(A3(_ui,_xb,_u6,_xQ));});return B(A3(_u9,_xa,_xP,_xe));}),_y3=new T(function(){var _y4=new T(function(){var _y5=E(_w2)-1|0,_y6=function(_y7){var _y8=B(_tP(_w0));if(_y5<=_y7){if(_y5>=0){var _y9=new T(function(){return B(_vG(_y8));}),_ya=function(_yb){var _yc=new T(function(){var _yd=new T(function(){var _ye=function(_){var _yf=__app3(E(_uP),E(_yb),toJSStr(E(_vn)),toJSStr(E(_uT)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_ye));});return B(A3(_ub,_y8,_yd,new T(function(){return B(A1(_y9,new T3(1,_w1,_y5,_yb)));})));}),_yg=new T(function(){var _yh=function(_){var _yi=__app3(E(_uQ),E(_yb),toJSStr(E(_vl)),toJSStr(E(_uW)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_yh));});return new F(function(){return A3(_ub,_y8,_yg,_yc);});};return new F(function(){return A3(_ud,_y8,new T(function(){return B(_vr(_w0,_vp));}),_ya);});}else{var _yj=new T(function(){return B(_vG(_y8));}),_yk=function(_yl){var _ym=new T(function(){var _yn=new T(function(){var _yo=function(_){var _yp=__app3(E(_uP),E(_yl),toJSStr(E(_vn)),toJSStr(E(_uT)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_yo));});return B(A3(_ub,_y8,_yn,new T(function(){return B(A1(_yj,new T1(2,_yl)));})));}),_yq=new T(function(){var _yr=function(_){var _ys=__app3(E(_uQ),E(_yl),toJSStr(E(_vl)),toJSStr(E(_uU)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_yr));});return new F(function(){return A3(_ub,_y8,_yq,_ym);});};return new F(function(){return A3(_ud,_y8,new T(function(){return B(_vr(_w0,_vp));}),_yk);});}}else{var _yt=new T(function(){return B(_vG(_y8));}),_yu=function(_yv){var _yw=new T(function(){var _yx=new T(function(){var _yy=function(_){var _yz=__app3(E(_uP),E(_yv),toJSStr(E(_vn)),toJSStr(E(_uT)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_yy));});return B(A3(_ub,_y8,_yx,new T(function(){return B(A1(_yt,new T1(2,_yv)));})));}),_yA=new T(function(){var _yB=function(_){var _yC=__app3(E(_uQ),E(_yv),toJSStr(E(_vl)),toJSStr(E(_uV)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_yB));});return new F(function(){return A3(_ub,_y8,_yA,_yw);});};return new F(function(){return A3(_ud,_y8,new T(function(){return B(_vr(_w0,_vp));}),_yu);});}};switch(E(_w1)){case 0:return B(_y6(E(E(_w6).a)));break;case 1:return B(_y6(7));break;default:return B(_y6(7));}});return B(A3(_ui,_xb,_u6,_y4));});return B(A3(_u9,_xa,_y3,_xd));}),_yD=function(_yE){var _yF=E(_yE);if(!_yF._){return E(_xc);}else{return new F(function(){return A3(_u9,_xa,new T(function(){return B(A3(_ui,_xb,_u6,_yF.a));}),new T(function(){return B(_yD(_yF.b));}));});}};if(0<=_w8){var _yG=new T(function(){return B(A2(_vG,_wH,_0));}),_yH=new T(function(){var _yI=B(_tP(_w0)),_yJ=new T(function(){return B(_vG(_yI));}),_yK=function(_yL){var _yM=new T(function(){var _yN=new T(function(){var _yO=function(_){var _yP=__app3(E(_uP),E(_yL),toJSStr(E(_vn)),toJSStr(E(_vo)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_yO));});return B(A3(_ub,_yI,_yN,new T(function(){return B(A1(_yJ,new T1(2,_yL)));})));}),_yQ=new T(function(){var _yR=function(_){var _yS=__app3(E(_uQ),E(_yL),toJSStr(E(_vl)),toJSStr(E(_vm)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_yR));});return new F(function(){return A3(_ub,_yI,_yQ,_yM);});};return B(A3(_ud,_yI,new T(function(){return B(_vr(_w0,_vp));}),_yK));}),_yT=new T(function(){return B(_vG(_wH));}),_yU=new T(function(){return B(_vr(_w0,_vj));}),_yV=function(_yW,_yX){var _yY=new T(function(){var _yZ=new T(function(){return B(_uI(B(_uo(_yW,_w6))));}),_z0=new T(function(){var _z1=E(_yW),_z2=B(_68(_z1.a,_z1.b,_z1.c,E(_w6).d));if(!_z2._){return __Z;}else{return new T1(1,new T(function(){return B(_p8(_z2.a));}));}}),_z3=new T(function(){var _z4=E(E(_w6).c);if(!_z4._){return false;}else{var _z5=E(_yW),_z6=E(_z4.a);if(E(_z5.a)!=E(_z6.a)){return false;}else{if(E(_z5.b)!=E(_z6.b)){return false;}else{return E(_z5.c)==E(_z6.c);}}}}),_z7=function(_z8){var _z9=new T(function(){var _za=new T(function(){var _zb=new T(function(){if(!E(_z3)){return E(_yG);}else{var _zc=function(_){var _zd=__app3(E(_uQ),E(_z8),toJSStr(E(_v0)),toJSStr(E(_v1)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_zc));}});return B(A3(_ub,_wH,_zb,new T(function(){return B(A1(_yT,new T2(0,_yW,_z8)));})));}),_ze=new T(function(){var _zf=E(_z0);if(!_zf._){return E(_yG);}else{if(!E(_zf.a)){var _zg=function(_){var _zh=__app3(E(_uP),E(_z8),toJSStr(E(_vn)),toJSStr(E(_uY)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_zg));}else{var _zi=function(_){var _zj=__app3(E(_uP),E(_z8),toJSStr(E(_vn)),toJSStr(E(_uZ)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_zi));}}});return B(A3(_ub,_wH,_ze,_za));}),_zk=new T(function(){var _zl=function(_){var _zm=__app3(E(_uQ),E(_z8),toJSStr(E(_vl)),toJSStr(E(_yZ)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_zl));});return new F(function(){return A3(_ub,_wH,_zk,_z9);});};return B(A3(_ud,_wH,_yU,_z7));});return new T2(1,_yH,new T2(1,_yY,_yX));},_zn=new T2(1,_yH,new T2(1,new T(function(){return B(_vz(_w0));}),_x)),_zo=function(_zp,_zq){var _zr=E(_zp);if(!_zr._){return E(_zn);}else{var _zs=_zr.a,_zt=E(_zq);if(_zt==1){return new F(function(){return _yV(_zs,_zn);});}else{return new F(function(){return _yV(_zs,new T(function(){return B(_zo(_zr.b,_zt-1|0));}));});}}},_zu=new T(function(){return B(_wt(_w0));}),_zv=function(_zw,_zx){while(1){var _zy=B((function(_zz,_zA){var _zB=new T(function(){var _zC=new T(function(){return B(_vN(_w0,new T(function(){var _zD=E(_wc);switch(E(_w4)){case 0:var _zE=E(_zz);if(!_zE){return _zD-B(_cd(_vY,0))|0;}else{return _zD-B(_cd(B(_tY(_zE)),0))|0;}break;case 1:return _zD-1|0;break;default:return _zD-1|0;}},1)));}),_zF=new T(function(){var _zG=new T(function(){var _zH=new T(function(){switch(E(_w4)){case 0:var _zI=E(_zz);if(!_zI){return toJSStr(E(_vY));}else{return toJSStr(B(_tY(_zI)));}break;case 1:return toJSStr(new T2(1,new T(function(){var _zJ=97+_zz|0;if(_zJ>>>0>1114111){return B(_ug(_zJ));}else{return _zJ;}}),_x));break;default:return toJSStr(new T2(1,new T(function(){var _zK=49+_zz|0;if(_zK>>>0>1114111){return B(_ug(_zK));}else{return _zK;}}),_x));}},1);return B(_vC(_w0,_zH));}),_zL=function(_zM){var _zN=new T(function(){var _zO=new T(function(){var _zP=function(_zQ){var _zR=function(_){var _zS=__app2(E(_uf),E(_zQ),E(_zM));return new F(function(){return _tv(_);});};return new F(function(){return A2(_uR,_w0,_zR);});};return B(A3(_ud,_wH,_zG,_zP));});return B(A3(_ub,_wH,_zO,new T(function(){return B(A1(_yT,new T3(1,_w4,_zz,_zM)));})));}),_zT=new T(function(){var _zU=function(_){var _zV=__app3(E(_uP),E(_zM),toJSStr(E(_vn)),toJSStr(E(_uT)));return new F(function(){return _tv(_);});};return B(A2(_uR,_w0,_zU));});return new F(function(){return A3(_ub,_wH,_zT,_zN);});};return B(A3(_ud,_wH,_yU,_zL));});return B(_5(new T2(1,_zF,new T2(1,_zC,new T(function(){var _zW=E(_w9);if(0>=_zW){return E(_zn);}else{return B(_zo(B(_ca(_w5,_zz)),_zW));}}))),_zu));},1),_zX=B(_5(_zA,_zB));if(_zz!=_w8){var _zY=_zz+1|0;_zw=_zY;_zx=_zX;return __continue;}else{return E(_zX);}})(_zw,_zx));if(_zy!=__continue){return _zy;}}};return new F(function(){return _yD(B(_zv(0,_x9)));});}else{return new F(function(){return _yD(_x9);});}};switch(E(_w4)){case 0:return new F(function(){return _w7(E(E(_w6).a));});break;case 1:return new F(function(){return _w7(7);});break;default:return new F(function(){return _w7(7);});}},_zZ=0,_A0=function(_A1,_A2,_){while(1){var _A3=B((function(_A4,_A5,_){var _A6=E(_A4);if(!_A6._){return new F(function(){return A1(_A5,_);});}else{_A1=_A6.b;_A2=function(_){return new F(function(){return _3H(_A5,_A6.a,_);});};return __continue;}})(_A1,_A2,_));if(_A3!=__continue){return _A3;}}},_A7=new T(function(){return B(unCStr("foldl1"));}),_A8=new T(function(){return B(_cj(_A7));}),_A9=function(_Aa){var _Ab=E(_Aa);switch(_Ab._){case 0:return E(_Ab.b);case 1:return E(_Ab.c);default:return E(_Ab.a);}},_Ac=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_Ad=function(_Ae,_Af){var _Ag=function(_){var _Ah=__app1(E(_Ac),E(_Af)),_Ai=__eq(_Ah,E(_2P));return (E(_Ai)==0)?new T1(1,_Ah):_2s;};return new F(function(){return A2(_uR,_Ae,_Ag);});},_Aj="board",_Ak=new T(function(){return B(_Ad(_43,_Aj));}),_Al=new T(function(){return B(unCStr("Pattern match failure in do expression at Web.hs:26:9-21"));}),_Am=new T6(0,_2s,_2t,_x,_Al,_2s,_2s),_An=new T(function(){return B(_2q(_Am));}),_Ao=function(_Ap){return E(E(_Ap).a);},_Aq=function(_Ar){return E(E(_Ar).a);},_As=function(_At){return E(E(_At).b);},_Au=function(_Av){return E(E(_Av).a);},_Aw=function(_){return new F(function(){return nMV(_2s);});},_Ax=new T(function(){return B(_2L(_Aw));}),_Ay=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_Az=function(_AA){return E(E(_AA).b);},_AB=function(_AC,_AD,_AE,_AF,_AG,_AH){var _AI=B(_Ao(_AC)),_AJ=B(_tP(_AI)),_AK=new T(function(){return B(_uR(_AI));}),_AL=new T(function(){return B(_vG(_AJ));}),_AM=new T(function(){return B(A2(_Aq,_AD,_AF));}),_AN=new T(function(){return B(A2(_Au,_AE,_AG));}),_AO=function(_AP){return new F(function(){return A1(_AL,new T3(0,_AN,_AM,_AP));});},_AQ=function(_AR){var _AS=new T(function(){var _AT=new T(function(){var _AU=__createJSFunc(2,function(_AV,_){var _AW=B(A2(E(_AR),_AV,_));return _2P;}),_AX=_AU;return function(_){return new F(function(){return __app3(E(_Ay),E(_AM),E(_AN),_AX);});};});return B(A1(_AK,_AT));});return new F(function(){return A3(_ud,_AJ,_AS,_AO);});},_AY=new T(function(){var _AZ=new T(function(){return B(_uR(_AI));}),_B0=function(_B1){var _B2=new T(function(){return B(A1(_AZ,function(_){var _=wMV(E(_Ax),new T1(1,_B1));return new F(function(){return A(_As,[_AE,_AG,_B1,_]);});}));});return new F(function(){return A3(_ud,_AJ,_B2,_AH);});};return B(A2(_Az,_AC,_B0));});return new F(function(){return A3(_ud,_AJ,_AY,_AQ);});},_B3=new T(function(){return eval("(function(e,ch){while(e.firstChild) {e.removeChild(e.firstChild);}for(var i in ch) {e.appendChild(ch[i]);}})");}),_B4=function(_B5){return E(_B5);},_B6=function(_B7,_B8,_B9,_Ba,_Bb){var _Bc=new T(function(){var _Bd=__lst2arr(B(_4j(_B4,B(_4j(new T(function(){return B(_Aq(_B8));}),_Bb))))),_Be=_Bd;return function(_){var _Bf=__app2(E(_B3),B(A2(_Aq,_B7,_Ba)),_Be);return new F(function(){return _tv(_);});};});return new F(function(){return A2(_uR,_B9,_Bc);});},_Bg=function(_Bh,_Bi,_Bj,_Bk,_Bl,_){var _Bm=B(A1(_Ak,_)),_Bn=E(_Bm);if(!_Bn._){return new F(function(){return die(_An);});}else{var _Bo=B(A(_4s,[_Bh,_Bi,_Bj,_Bk,_Bl])),_Bp=E(_Bo.a),_Bq=B(A(_vZ,[_43,_Bp.a,_Bp.b,_Bo.b,_Bo.c,_Bo.d,_Bo.e,_])),_Br=new T(function(){return E(E(_Bl).a);}),_Bs=new T(function(){return E(E(_Bl).b);}),_Bt=new T(function(){return E(E(_Bl).d);}),_Bu=function(_Bv,_){return new F(function(){return _Bg(_Bh,_Bi,_Bj,_Bk,new T4(0,_Br,_Bs,_2s,_Bt),_);});},_Bw=function(_Bx){while(1){var _By=B((function(_Bz){var _BA=E(_Bz);if(!_BA._){return __Z;}else{var _BB=_BA.b,_BC=E(_BA.a);if(_BC._==2){_Bx=_BB;return __continue;}else{var _BD=new T(function(){var _BE=E(_BC);if(!_BE._){var _BF=_BE.a,_BG=_BE.b,_BH=E(_Bl),_BI=_BH.a,_BJ=E(_BH.c);if(!_BJ._){var _BK=new T(function(){var _BL=B(_tm(_BF,_BH));return new T4(0,_BL.a,_BL.b,_BL.c,_BL.d);});return B(_AB(_44,_3l,_3g,_BG,_zZ,function(_BM,_){return new F(function(){return _Bg(_Bh,_Bi,_Bj,_Bk,_BK,_);});}));}else{var _BN=E(_BJ.a),_BO=E(_BF),_BP=function(_BQ){var _BR=new T(function(){return B(_sO(_BO,_BI,_BH.b,_BJ,_BH.d));}),_BS=new T(function(){if(!E(_BR)._){return E(_Bi);}else{switch(E(_Bh)){case 0:var _BT=E(_Bi);if(_BT!=E(_BI)){return E(_BT);}else{var _BU=E(_BT);if(_BU==2147483647){return E(_46);}else{return _BU+1|0;}}break;case 1:return E(_Bi);break;default:return E(_Bi);}}}),_BV=new T(function(){var _BW=E(_BR);if(!_BW._){return E(_BH);}else{return E(_BW.a);}});return new F(function(){return _AB(_44,_3l,_3g,_BG,_zZ,function(_BX,_){return new F(function(){return _Bg(_Bh,_BS,_Bj,_Bk,_BV,_);});});});};if(E(_BN.a)!=E(_BO.a)){return B(_BP(_));}else{if(E(_BN.b)!=E(_BO.b)){return B(_BP(_));}else{if(E(_BN.c)!=E(_BO.c)){return B(_BP(_));}else{return B(_AB(_44,_3l,_3g,_BG,_zZ,_Bu));}}}}}else{var _BY=_BE.a,_BZ=new T(function(){switch(E(_Bj)){case 0:if(!E(_BY)){return E(_Bh);}else{return 0;}break;case 1:if(E(_BY)==1){return E(_Bh);}else{return 1;}break;default:if(E(_BY)==2){return E(_Bh);}else{return 2;}}}),_C0=new T(function(){switch(E(_Bk)){case 0:if(!E(_BY)){return E(_Bh);}else{return 0;}break;case 1:if(E(_BY)==1){return E(_Bh);}else{return 1;}break;default:if(E(_BY)==2){return E(_Bh);}else{return 2;}}});return B(_AB(_44,_3l,_3g,_BE.c,_zZ,function(_C1,_){return new F(function(){return _Bg(_BY,_BE.b,_BZ,_C0,_Bl,_);});}));}});return new T2(1,_BD,new T(function(){return B(_Bw(_BB));}));}}})(_Bx));if(_By!=__continue){return _By;}}},_C2=B(_Bw(_Bq));if(!_C2._){return E(_A8);}else{var _C3=B(_A0(_C2.b,_C2.a,_)),_C4=B(A(_B6,[_3l,_3l,_43,_Bn.a,new T(function(){return B(_4j(_A9,_Bq));},1),_]));return _0;}}},_C5=0,_C6=1,_C7=2,_C8=function(_C9,_Ca,_Cb,_Cc,_){var _Cd=B(A1(_Ak,_)),_Ce=E(_Cd);if(!_Ce._){return new F(function(){return die(_An);});}else{var _Cf=B(A(_4s,[_C5,_C9,_C6,_C7,new T4(0,_Ca,_Cb,_2s,_Cc)])),_Cg=E(_Cf.a),_Ch=B(A(_vZ,[_43,_Cg.a,_Cg.b,_Cf.b,_Cf.c,_Cf.d,_Cf.e,_])),_Ci=function(_Cj){while(1){var _Ck=B((function(_Cl){var _Cm=E(_Cl);if(!_Cm._){return __Z;}else{var _Cn=_Cm.b,_Co=E(_Cm.a);if(_Co._==2){_Cj=_Cn;return __continue;}else{var _Cp=new T(function(){var _Cq=E(_Co);if(!_Cq._){var _Cr=new T(function(){var _Cs=B(_tm(_Cq.a,new T4(0,_Ca,_Cb,_2s,_Cc)));return new T4(0,_Cs.a,_Cs.b,_Cs.c,_Cs.d);});return B(_AB(_44,_3l,_3g,_Cq.b,_zZ,function(_Ct,_){return new F(function(){return _Bg(_C5,_C9,_C6,_C7,_Cr,_);});}));}else{var _Cu=_Cq.a,_Cv=new T(function(){if(E(_Cu)==1){return 0;}else{return 1;}}),_Cw=new T(function(){if(E(_Cu)==2){return 0;}else{return 2;}});return B(_AB(_44,_3l,_3g,_Cq.c,_zZ,function(_Cx,_){return new F(function(){return _Bg(_Cu,_Cq.b,_Cv,_Cw,new T4(0,_Ca,_Cb,_2s,_Cc),_);});}));}});return new T2(1,_Cp,new T(function(){return B(_Ci(_Cn));}));}}})(_Cj));if(_Ck!=__continue){return _Ck;}}},_Cy=B(_Ci(_Ch));if(!_Cy._){return E(_A8);}else{var _Cz=B(_A0(_Cy.b,_Cy.a,_)),_CA=B(A(_B6,[_3l,_3l,_43,_Ce.a,new T(function(){return B(_4j(_A9,_Ch));},1),_]));return _0;}}},_CB=new T0(3),_CC=new T0(2),_CD=new T0(4),_CE=3,_CF=2,_CG=1,_CH=6,_CI=0,_CJ=7,_CK=5,_CL=4,_CM=new T1(5,_dd),_CN=new T1(1,_dd),_CO=function(_CP,_CQ){return new T2(0,new T2(0,new T3(0,_CI,_CI,_CQ),new T5(0,_CP,_CN,_de,_2s,_2s)),new T2(1,new T2(0,new T3(0,_CI,_CG,_CQ),new T5(0,_CP,_CC,_de,_2s,_2s)),new T2(1,new T2(0,new T3(0,_CI,_CF,_CQ),new T5(0,_CP,_CB,_de,_2s,_2s)),new T2(1,new T2(0,new T3(0,_CI,_CE,_CQ),new T5(0,_CP,_CD,_de,_2s,_2s)),new T2(1,new T2(0,new T3(0,_CI,_CL,_CQ),new T5(0,_CP,_CM,_de,_2s,_2s)),new T2(1,new T2(0,new T3(0,_CI,_CK,_CQ),new T5(0,_CP,_CB,_de,_2s,_2s)),new T2(1,new T2(0,new T3(0,_CI,_CH,_CQ),new T5(0,_CP,_CC,_de,_2s,_2s)),new T2(1,new T2(0,new T3(0,_CI,_CJ,_CQ),new T5(0,_CP,_CN,_de,_2s,_2s)),_x))))))));},_CR=new T(function(){return B(_4d(0,7));}),_CS=new T1(0,_dd),_CT=function(_CU,_CV){var _CW=function(_CX,_CY){var _CZ=E(_CX);if(!_CZ._){return __Z;}else{var _D0=E(_CY);return (_D0._==0)?__Z:new T2(1,new T2(0,new T3(0,_CI,_CZ.a,_CV),_D0.a),new T(function(){return B(_CW(_CZ.b,_D0.b));}));}},_D1=new T(function(){var _D2=new T(function(){return new T2(1,new T5(0,_CU,_CS,_de,_2s,_2s),_D2);});return E(_D2);},1);return new F(function(){return _CW(_CR,_D1);});},_D3=new T(function(){return B(_CT(_1,_CG));}),_D4=1,_D5=new T(function(){return B(_CT(_D4,_CH));}),_D6=new T(function(){var _D7=B(_CO(_D4,_CJ));return B(_5(new T2(1,_D7.a,_D7.b),_D5));}),_D8=new T(function(){return B(_5(_D3,_D6));}),_D9=new T(function(){var _Da=B(_CO(_1,_CI));return B(_mX(B(_5(new T2(1,_Da.a,_Da.b),_D8))));}),_Db=function(_){var _Dc=B(_C8(0,0,_1,_D9,_));return _0;},_Dd=function(_){return new F(function(){return _Db(_);});};
var hasteMain = function() {B(A(_Dd, [0]));};window.onload = hasteMain;