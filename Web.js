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

var _0=0,_1=0,_2="deltaZ",_3="deltaY",_4="deltaX",_5=function(_6,_7){var _8=E(_6);return (_8._==0)?E(_7):new T2(1,_8.a,new T(function(){return B(_5(_8.b,_7));}));},_9=function(_a,_b){var _c=jsShowI(_a);return new F(function(){return _5(fromJSStr(_c),_b);});},_d=41,_e=40,_f=function(_g,_h,_i){if(_h>=0){return new F(function(){return _9(_h,_i);});}else{if(_g<=6){return new F(function(){return _9(_h,_i);});}else{return new T2(1,_e,new T(function(){var _j=jsShowI(_h);return B(_5(fromJSStr(_j),new T2(1,_d,_i)));}));}}},_k=new T(function(){return B(unCStr(")"));}),_l=new T(function(){return B(_f(0,2,_k));}),_m=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_l));}),_n=function(_o){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_f(0,_o,_m));}))));});},_p=function(_q,_){return new T(function(){var _r=Number(E(_q)),_s=jsTrunc(_r);if(_s<0){return B(_n(_s));}else{if(_s>2){return B(_n(_s));}else{return _s;}}});},_t=0,_u=new T3(0,_t,_t,_t),_v="button",_w=new T(function(){return eval("jsGetMouseCoords");}),_x=__Z,_y=function(_z,_){var _A=E(_z);if(!_A._){return _x;}else{var _B=B(_y(_A.b,_));return new T2(1,new T(function(){var _C=Number(E(_A.a));return jsTrunc(_C);}),_B);}},_D=function(_E,_){var _F=__arr2lst(0,_E);return new F(function(){return _y(_F,_);});},_G=function(_H,_){return new F(function(){return _D(E(_H),_);});},_I=function(_J,_){return new T(function(){var _K=Number(E(_J));return jsTrunc(_K);});},_L=new T2(0,_I,_G),_M=function(_N,_){var _O=E(_N);if(!_O._){return _x;}else{var _P=B(_M(_O.b,_));return new T2(1,_O.a,_P);}},_Q=new T(function(){return B(unCStr("base"));}),_R=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_S=new T(function(){return B(unCStr("IOException"));}),_T=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Q,_R,_S),_U=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_T,_x,_x),_V=function(_W){return E(_U);},_X=function(_Y){return E(E(_Y).a);},_Z=function(_10,_11,_12){var _13=B(A1(_10,_)),_14=B(A1(_11,_)),_15=hs_eqWord64(_13.a,_14.a);if(!_15){return __Z;}else{var _16=hs_eqWord64(_13.b,_14.b);return (!_16)?__Z:new T1(1,_12);}},_17=function(_18){var _19=E(_18);return new F(function(){return _Z(B(_X(_19.a)),_V,_19.b);});},_1a=new T(function(){return B(unCStr(": "));}),_1b=new T(function(){return B(unCStr(")"));}),_1c=new T(function(){return B(unCStr(" ("));}),_1d=new T(function(){return B(unCStr("interrupted"));}),_1e=new T(function(){return B(unCStr("system error"));}),_1f=new T(function(){return B(unCStr("unsatisified constraints"));}),_1g=new T(function(){return B(unCStr("user error"));}),_1h=new T(function(){return B(unCStr("permission denied"));}),_1i=new T(function(){return B(unCStr("illegal operation"));}),_1j=new T(function(){return B(unCStr("end of file"));}),_1k=new T(function(){return B(unCStr("resource exhausted"));}),_1l=new T(function(){return B(unCStr("resource busy"));}),_1m=new T(function(){return B(unCStr("does not exist"));}),_1n=new T(function(){return B(unCStr("already exists"));}),_1o=new T(function(){return B(unCStr("resource vanished"));}),_1p=new T(function(){return B(unCStr("timeout"));}),_1q=new T(function(){return B(unCStr("unsupported operation"));}),_1r=new T(function(){return B(unCStr("hardware fault"));}),_1s=new T(function(){return B(unCStr("inappropriate type"));}),_1t=new T(function(){return B(unCStr("invalid argument"));}),_1u=new T(function(){return B(unCStr("failed"));}),_1v=new T(function(){return B(unCStr("protocol error"));}),_1w=function(_1x,_1y){switch(E(_1x)){case 0:return new F(function(){return _5(_1n,_1y);});break;case 1:return new F(function(){return _5(_1m,_1y);});break;case 2:return new F(function(){return _5(_1l,_1y);});break;case 3:return new F(function(){return _5(_1k,_1y);});break;case 4:return new F(function(){return _5(_1j,_1y);});break;case 5:return new F(function(){return _5(_1i,_1y);});break;case 6:return new F(function(){return _5(_1h,_1y);});break;case 7:return new F(function(){return _5(_1g,_1y);});break;case 8:return new F(function(){return _5(_1f,_1y);});break;case 9:return new F(function(){return _5(_1e,_1y);});break;case 10:return new F(function(){return _5(_1v,_1y);});break;case 11:return new F(function(){return _5(_1u,_1y);});break;case 12:return new F(function(){return _5(_1t,_1y);});break;case 13:return new F(function(){return _5(_1s,_1y);});break;case 14:return new F(function(){return _5(_1r,_1y);});break;case 15:return new F(function(){return _5(_1q,_1y);});break;case 16:return new F(function(){return _5(_1p,_1y);});break;case 17:return new F(function(){return _5(_1o,_1y);});break;default:return new F(function(){return _5(_1d,_1y);});}},_1z=new T(function(){return B(unCStr("}"));}),_1A=new T(function(){return B(unCStr("{handle: "));}),_1B=function(_1C,_1D,_1E,_1F,_1G,_1H){var _1I=new T(function(){var _1J=new T(function(){var _1K=new T(function(){var _1L=E(_1F);if(!_1L._){return E(_1H);}else{var _1M=new T(function(){return B(_5(_1L,new T(function(){return B(_5(_1b,_1H));},1)));},1);return B(_5(_1c,_1M));}},1);return B(_1w(_1D,_1K));}),_1N=E(_1E);if(!_1N._){return E(_1J);}else{return B(_5(_1N,new T(function(){return B(_5(_1a,_1J));},1)));}}),_1O=E(_1G);if(!_1O._){var _1P=E(_1C);if(!_1P._){return E(_1I);}else{var _1Q=E(_1P.a);if(!_1Q._){var _1R=new T(function(){var _1S=new T(function(){return B(_5(_1z,new T(function(){return B(_5(_1a,_1I));},1)));},1);return B(_5(_1Q.a,_1S));},1);return new F(function(){return _5(_1A,_1R);});}else{var _1T=new T(function(){var _1U=new T(function(){return B(_5(_1z,new T(function(){return B(_5(_1a,_1I));},1)));},1);return B(_5(_1Q.a,_1U));},1);return new F(function(){return _5(_1A,_1T);});}}}else{return new F(function(){return _5(_1O.a,new T(function(){return B(_5(_1a,_1I));},1));});}},_1V=function(_1W){var _1X=E(_1W);return new F(function(){return _1B(_1X.a,_1X.b,_1X.c,_1X.d,_1X.f,_x);});},_1Y=function(_1Z,_20,_21){var _22=E(_20);return new F(function(){return _1B(_22.a,_22.b,_22.c,_22.d,_22.f,_21);});},_23=function(_24,_25){var _26=E(_24);return new F(function(){return _1B(_26.a,_26.b,_26.c,_26.d,_26.f,_25);});},_27=44,_28=93,_29=91,_2a=function(_2b,_2c,_2d){var _2e=E(_2c);if(!_2e._){return new F(function(){return unAppCStr("[]",_2d);});}else{var _2f=new T(function(){var _2g=new T(function(){var _2h=function(_2i){var _2j=E(_2i);if(!_2j._){return E(new T2(1,_28,_2d));}else{var _2k=new T(function(){return B(A2(_2b,_2j.a,new T(function(){return B(_2h(_2j.b));})));});return new T2(1,_27,_2k);}};return B(_2h(_2e.b));});return B(A2(_2b,_2e.a,_2g));});return new T2(1,_29,_2f);}},_2l=function(_2m,_2n){return new F(function(){return _2a(_23,_2m,_2n);});},_2o=new T3(0,_1Y,_1V,_2l),_2p=new T(function(){return new T5(0,_V,_2o,_2q,_17,_1V);}),_2q=function(_2r){return new T2(0,_2p,_2r);},_2s=__Z,_2t=7,_2u=new T(function(){return B(unCStr("Pattern match failure in do expression at src\\Haste\\Prim\\Any.hs:272:5-9"));}),_2v=new T6(0,_2s,_2t,_x,_2u,_2s,_2s),_2w=new T(function(){return B(_2q(_2v));}),_2x=function(_){return new F(function(){return die(_2w);});},_2y=function(_2z){return E(E(_2z).a);},_2A=function(_2B,_2C,_2D,_){var _2E=__arr2lst(0,_2D),_2F=B(_M(_2E,_)),_2G=E(_2F);if(!_2G._){return new F(function(){return _2x(_);});}else{var _2H=E(_2G.b);if(!_2H._){return new F(function(){return _2x(_);});}else{if(!E(_2H.b)._){var _2I=B(A3(_2y,_2B,_2G.a,_)),_2J=B(A3(_2y,_2C,_2H.a,_));return new T2(0,_2I,_2J);}else{return new F(function(){return _2x(_);});}}}},_2K=function(_){return new F(function(){return __jsNull();});},_2L=function(_2M){var _2N=B(A1(_2M,_));return E(_2N);},_2O=new T(function(){return B(_2L(_2K));}),_2P=new T(function(){return E(_2O);}),_2Q=function(_2R,_2S,_){if(E(_2R)==7){var _2T=__app1(E(_w),_2S),_2U=B(_2A(_L,_L,_2T,_)),_2V=__get(_2S,E(_4)),_2W=__get(_2S,E(_3)),_2X=__get(_2S,E(_2));return new T(function(){return new T3(0,E(_2U),E(_2s),E(new T3(0,_2V,_2W,_2X)));});}else{var _2Y=__app1(E(_w),_2S),_2Z=B(_2A(_L,_L,_2Y,_)),_30=__get(_2S,E(_v)),_31=__eq(_30,E(_2P));if(!E(_31)){var _32=B(_p(_30,_));return new T(function(){return new T3(0,E(_2Z),E(new T1(1,_32)),E(_u));});}else{return new T(function(){return new T3(0,E(_2Z),E(_2s),E(_u));});}}},_33=function(_34,_35,_){return new F(function(){return _2Q(_34,E(_35),_);});},_36="mouseout",_37="mouseover",_38="mousemove",_39="mouseup",_3a="mousedown",_3b="dblclick",_3c="click",_3d="wheel",_3e=function(_3f){switch(E(_3f)){case 0:return E(_3c);case 1:return E(_3b);case 2:return E(_3a);case 3:return E(_39);case 4:return E(_38);case 5:return E(_37);case 6:return E(_36);default:return E(_3d);}},_3g=new T2(0,_3e,_33),_3h=function(_3i,_){return new T1(1,_3i);},_3j=function(_3k){return E(_3k);},_3l=new T2(0,_3j,_3h),_3m=function(_3n,_3o,_){var _3p=B(A1(_3n,_)),_3q=B(A1(_3o,_));return _3p;},_3r=function(_3s,_3t,_){var _3u=B(A1(_3s,_)),_3v=B(A1(_3t,_));return new T(function(){return B(A1(_3u,_3v));});},_3w=function(_3x,_3y,_){var _3z=B(A1(_3y,_));return _3x;},_3A=function(_3B,_3C,_){var _3D=B(A1(_3C,_));return new T(function(){return B(A1(_3B,_3D));});},_3E=new T2(0,_3A,_3w),_3F=function(_3G,_){return _3G;},_3H=function(_3I,_3J,_){var _3K=B(A1(_3I,_));return new F(function(){return A1(_3J,_);});},_3L=new T5(0,_3E,_3F,_3r,_3H,_3m),_3M=new T(function(){return E(_2p);}),_3N=function(_3O){return E(E(_3O).c);},_3P=function(_3Q){return new T6(0,_2s,_2t,_x,_3Q,_2s,_2s);},_3R=function(_3S,_){var _3T=new T(function(){return B(A2(_3N,_3M,new T(function(){return B(A1(_3P,_3S));})));});return new F(function(){return die(_3T);});},_3U=function(_3V,_){return new F(function(){return _3R(_3V,_);});},_3W=function(_3X){return new F(function(){return A1(_3U,_3X);});},_3Y=function(_3Z,_40,_){var _41=B(A1(_3Z,_));return new F(function(){return A2(_40,_41,_);});},_42=new T5(0,_3L,_3Y,_3H,_3F,_3W),_43=new T2(0,_42,_3j),_44=new T2(0,_43,_3F),_45=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_46=new T(function(){return B(err(_45));}),_47=function(_48,_49,_4a,_4b,_4c){return new T5(0,_48,_49,_4a,_4b,_4c);},_4d=function(_4e,_4f){if(_4e<=_4f){var _4g=function(_4h){return new T2(1,_4h,new T(function(){if(_4h!=_4f){return B(_4g(_4h+1|0));}else{return __Z;}}));};return new F(function(){return _4g(_4e);});}else{return __Z;}},_4i=new T(function(){return B(_4d(0,2147483647));}),_4j=function(_4k,_4l){var _4m=E(_4l);return (_4m._==0)?__Z:new T2(1,new T(function(){return B(A1(_4k,_4m.a));}),new T(function(){return B(_4j(_4k,_4m.b));}));},_4n=function(_4o,_4p,_4q,_4r){switch(E(_4r)){case 0:return E(_4o);case 1:return E(_4p);default:return E(_4q);}},_4s=function(_4t,_4u,_4v,_4w){var _4x=new T(function(){var _4y=function(_4z){var _4A=function(_4B){return new T3(0,new T(function(){return B(_4n(_4u,_4B,_4z,_4t));}),new T(function(){return B(_4n(_4u,_4B,_4z,_4v));}),new T(function(){return B(_4n(_4u,_4B,_4z,_4w));}));};return new F(function(){return _4j(_4A,_4i);});};return B(_4j(_4y,_4i));});return function(_4C){return new F(function(){return _47(new T2(0,_4t,_4u),_4v,_4w,_4x,_4C);});};},_4D=function(_4E,_4F,_4G,_4H){while(1){var _4I=E(_4H);if(!_4I._){var _4J=_4I.d,_4K=_4I.e,_4L=E(_4I.b),_4M=E(_4L.a);if(_4E>=_4M){if(_4E!=_4M){_4H=_4K;continue;}else{var _4N=E(_4L.b);if(_4F>=_4N){if(_4F!=_4N){_4H=_4K;continue;}else{var _4O=E(_4L.c);if(_4G>=_4O){if(_4G!=_4O){_4H=_4K;continue;}else{return new T1(1,_4I.c);}}else{_4H=_4J;continue;}}}else{_4H=_4J;continue;}}}else{_4H=_4J;continue;}}else{return __Z;}}},_4P=function(_4Q,_4R,_4S,_4T){while(1){var _4U=E(_4T);if(!_4U._){var _4V=_4U.d,_4W=_4U.e,_4X=E(_4U.b),_4Y=E(_4X.a);if(_4Q>=_4Y){if(_4Q!=_4Y){_4T=_4W;continue;}else{var _4Z=E(_4X.b);if(_4R>=_4Z){if(_4R!=_4Z){_4T=_4W;continue;}else{var _50=E(_4S),_51=E(_4X.c);if(_50>=_51){if(_50!=_51){return new F(function(){return _4D(_4Q,_4R,_50,_4W);});}else{return new T1(1,_4U.c);}}else{return new F(function(){return _4D(_4Q,_4R,_50,_4V);});}}}else{_4T=_4V;continue;}}}else{_4T=_4V;continue;}}else{return __Z;}}},_52=function(_53,_54,_55,_56){while(1){var _57=E(_56);if(!_57._){var _58=_57.d,_59=_57.e,_5a=E(_57.b),_5b=E(_5a.a);if(_53>=_5b){if(_53!=_5b){_56=_59;continue;}else{var _5c=E(_54),_5d=E(_5a.b);if(_5c>=_5d){if(_5c!=_5d){return new F(function(){return _4P(_53,_5c,_55,_59);});}else{var _5e=E(_55),_5f=E(_5a.c);if(_5e>=_5f){if(_5e!=_5f){return new F(function(){return _4D(_53,_5c,_5e,_59);});}else{return new T1(1,_57.c);}}else{return new F(function(){return _4D(_53,_5c,_5e,_58);});}}}else{return new F(function(){return _4P(_53,_5c,_55,_58);});}}}else{_56=_58;continue;}}else{return __Z;}}},_5g=function(_5h,_5i,_5j,_5k){var _5l=E(_5k);if(!_5l._){var _5m=_5l.d,_5n=_5l.e,_5o=E(_5l.b),_5p=E(_5h),_5q=E(_5o.a);if(_5p>=_5q){if(_5p!=_5q){return new F(function(){return _52(_5p,_5i,_5j,_5n);});}else{var _5r=E(_5i),_5s=E(_5o.b);if(_5r>=_5s){if(_5r!=_5s){return new F(function(){return _4P(_5p,_5r,_5j,_5n);});}else{var _5t=E(_5j),_5u=E(_5o.c);if(_5t>=_5u){if(_5t!=_5u){return new F(function(){return _4D(_5p,_5r,_5t,_5n);});}else{return new T1(1,_5l.c);}}else{return new F(function(){return _4D(_5p,_5r,_5t,_5m);});}}}else{return new F(function(){return _4P(_5p,_5r,_5j,_5m);});}}}else{return new F(function(){return _52(_5p,_5i,_5j,_5m);});}}else{return __Z;}},_5v=function(_5w){return false;},_5x=new T0(1),_5y=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_5z=function(_5A){return new F(function(){return err(_5y);});},_5B=new T(function(){return B(_5z(_));}),_5C=function(_5D,_5E,_5F,_5G){var _5H=E(_5G);if(!_5H._){var _5I=_5H.a,_5J=E(_5F);if(!_5J._){var _5K=_5J.a,_5L=_5J.b,_5M=_5J.c;if(_5K<=(imul(3,_5I)|0)){return new T5(0,(1+_5K|0)+_5I|0,E(_5D),_5E,E(_5J),E(_5H));}else{var _5N=E(_5J.d);if(!_5N._){var _5O=_5N.a,_5P=E(_5J.e);if(!_5P._){var _5Q=_5P.a,_5R=_5P.b,_5S=_5P.c,_5T=_5P.d;if(_5Q>=(imul(2,_5O)|0)){var _5U=function(_5V){var _5W=E(_5P.e);return (_5W._==0)?new T5(0,(1+_5K|0)+_5I|0,E(_5R),_5S,E(new T5(0,(1+_5O|0)+_5V|0,E(_5L),_5M,E(_5N),E(_5T))),E(new T5(0,(1+_5I|0)+_5W.a|0,E(_5D),_5E,E(_5W),E(_5H)))):new T5(0,(1+_5K|0)+_5I|0,E(_5R),_5S,E(new T5(0,(1+_5O|0)+_5V|0,E(_5L),_5M,E(_5N),E(_5T))),E(new T5(0,1+_5I|0,E(_5D),_5E,E(_5x),E(_5H))));},_5X=E(_5T);if(!_5X._){return new F(function(){return _5U(_5X.a);});}else{return new F(function(){return _5U(0);});}}else{return new T5(0,(1+_5K|0)+_5I|0,E(_5L),_5M,E(_5N),E(new T5(0,(1+_5I|0)+_5Q|0,E(_5D),_5E,E(_5P),E(_5H))));}}else{return E(_5B);}}else{return E(_5B);}}}else{return new T5(0,1+_5I|0,E(_5D),_5E,E(_5x),E(_5H));}}else{var _5Y=E(_5F);if(!_5Y._){var _5Z=_5Y.a,_60=_5Y.b,_61=_5Y.c,_62=_5Y.e,_63=E(_5Y.d);if(!_63._){var _64=_63.a,_65=E(_62);if(!_65._){var _66=_65.a,_67=_65.b,_68=_65.c,_69=_65.d;if(_66>=(imul(2,_64)|0)){var _6a=function(_6b){var _6c=E(_65.e);return (_6c._==0)?new T5(0,1+_5Z|0,E(_67),_68,E(new T5(0,(1+_64|0)+_6b|0,E(_60),_61,E(_63),E(_69))),E(new T5(0,1+_6c.a|0,E(_5D),_5E,E(_6c),E(_5x)))):new T5(0,1+_5Z|0,E(_67),_68,E(new T5(0,(1+_64|0)+_6b|0,E(_60),_61,E(_63),E(_69))),E(new T5(0,1,E(_5D),_5E,E(_5x),E(_5x))));},_6d=E(_69);if(!_6d._){return new F(function(){return _6a(_6d.a);});}else{return new F(function(){return _6a(0);});}}else{return new T5(0,1+_5Z|0,E(_60),_61,E(_63),E(new T5(0,1+_66|0,E(_5D),_5E,E(_65),E(_5x))));}}else{return new T5(0,3,E(_60),_61,E(_63),E(new T5(0,1,E(_5D),_5E,E(_5x),E(_5x))));}}else{var _6e=E(_62);return (_6e._==0)?new T5(0,3,E(_6e.b),_6e.c,E(new T5(0,1,E(_60),_61,E(_5x),E(_5x))),E(new T5(0,1,E(_5D),_5E,E(_5x),E(_5x)))):new T5(0,2,E(_5D),_5E,E(_5Y),E(_5x));}}else{return new T5(0,1,E(_5D),_5E,E(_5x),E(_5x));}}},_6f=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_6g=function(_6h){return new F(function(){return err(_6f);});},_6i=new T(function(){return B(_6g(_));}),_6j=function(_6k,_6l,_6m,_6n){var _6o=E(_6m);if(!_6o._){var _6p=_6o.a,_6q=E(_6n);if(!_6q._){var _6r=_6q.a,_6s=_6q.b,_6t=_6q.c;if(_6r<=(imul(3,_6p)|0)){return new T5(0,(1+_6p|0)+_6r|0,E(_6k),_6l,E(_6o),E(_6q));}else{var _6u=E(_6q.d);if(!_6u._){var _6v=_6u.a,_6w=_6u.b,_6x=_6u.c,_6y=_6u.d,_6z=E(_6q.e);if(!_6z._){var _6A=_6z.a;if(_6v>=(imul(2,_6A)|0)){var _6B=function(_6C){var _6D=E(_6k),_6E=E(_6u.e);return (_6E._==0)?new T5(0,(1+_6p|0)+_6r|0,E(_6w),_6x,E(new T5(0,(1+_6p|0)+_6C|0,E(_6D),_6l,E(_6o),E(_6y))),E(new T5(0,(1+_6A|0)+_6E.a|0,E(_6s),_6t,E(_6E),E(_6z)))):new T5(0,(1+_6p|0)+_6r|0,E(_6w),_6x,E(new T5(0,(1+_6p|0)+_6C|0,E(_6D),_6l,E(_6o),E(_6y))),E(new T5(0,1+_6A|0,E(_6s),_6t,E(_5x),E(_6z))));},_6F=E(_6y);if(!_6F._){return new F(function(){return _6B(_6F.a);});}else{return new F(function(){return _6B(0);});}}else{return new T5(0,(1+_6p|0)+_6r|0,E(_6s),_6t,E(new T5(0,(1+_6p|0)+_6v|0,E(_6k),_6l,E(_6o),E(_6u))),E(_6z));}}else{return E(_6i);}}else{return E(_6i);}}}else{return new T5(0,1+_6p|0,E(_6k),_6l,E(_6o),E(_5x));}}else{var _6G=E(_6n);if(!_6G._){var _6H=_6G.a,_6I=_6G.b,_6J=_6G.c,_6K=_6G.e,_6L=E(_6G.d);if(!_6L._){var _6M=_6L.a,_6N=_6L.b,_6O=_6L.c,_6P=_6L.d,_6Q=E(_6K);if(!_6Q._){var _6R=_6Q.a;if(_6M>=(imul(2,_6R)|0)){var _6S=function(_6T){var _6U=E(_6k),_6V=E(_6L.e);return (_6V._==0)?new T5(0,1+_6H|0,E(_6N),_6O,E(new T5(0,1+_6T|0,E(_6U),_6l,E(_5x),E(_6P))),E(new T5(0,(1+_6R|0)+_6V.a|0,E(_6I),_6J,E(_6V),E(_6Q)))):new T5(0,1+_6H|0,E(_6N),_6O,E(new T5(0,1+_6T|0,E(_6U),_6l,E(_5x),E(_6P))),E(new T5(0,1+_6R|0,E(_6I),_6J,E(_5x),E(_6Q))));},_6W=E(_6P);if(!_6W._){return new F(function(){return _6S(_6W.a);});}else{return new F(function(){return _6S(0);});}}else{return new T5(0,1+_6H|0,E(_6I),_6J,E(new T5(0,1+_6M|0,E(_6k),_6l,E(_5x),E(_6L))),E(_6Q));}}else{return new T5(0,3,E(_6N),_6O,E(new T5(0,1,E(_6k),_6l,E(_5x),E(_5x))),E(new T5(0,1,E(_6I),_6J,E(_5x),E(_5x))));}}else{var _6X=E(_6K);return (_6X._==0)?new T5(0,3,E(_6I),_6J,E(new T5(0,1,E(_6k),_6l,E(_5x),E(_5x))),E(_6X)):new T5(0,2,E(_6k),_6l,E(_5x),E(_6G));}}else{return new T5(0,1,E(_6k),_6l,E(_5x),E(_5x));}}},_6Y=function(_6Z,_70,_71,_72,_73){var _74=E(_73);if(!_74._){var _75=new T(function(){var _76=B(_6Y(_74.a,_74.b,_74.c,_74.d,_74.e));return new T2(0,_76.a,_76.b);});return new T2(0,new T(function(){return E(E(_75).a);}),new T(function(){return B(_5C(_70,_71,_72,E(_75).b));}));}else{return new T2(0,new T2(0,_70,_71),_72);}},_77=function(_78,_79,_7a,_7b,_7c){var _7d=E(_7b);if(!_7d._){var _7e=new T(function(){var _7f=B(_77(_7d.a,_7d.b,_7d.c,_7d.d,_7d.e));return new T2(0,_7f.a,_7f.b);});return new T2(0,new T(function(){return E(E(_7e).a);}),new T(function(){return B(_6j(_79,_7a,E(_7e).b,_7c));}));}else{return new T2(0,new T2(0,_79,_7a),_7c);}},_7g=function(_7h,_7i){var _7j=E(_7h);if(!_7j._){var _7k=_7j.a,_7l=E(_7i);if(!_7l._){var _7m=_7l.a;if(_7k<=_7m){var _7n=B(_77(_7m,_7l.b,_7l.c,_7l.d,_7l.e)),_7o=E(_7n.a);return new F(function(){return _5C(_7o.a,_7o.b,_7j,_7n.b);});}else{var _7p=B(_6Y(_7k,_7j.b,_7j.c,_7j.d,_7j.e)),_7q=E(_7p.a);return new F(function(){return _6j(_7q.a,_7q.b,_7p.b,_7l);});}}else{return E(_7j);}}else{return E(_7i);}},_7r=function(_7s,_7t,_7u,_7v){var _7w=E(_7v);if(!_7w._){var _7x=_7w.c,_7y=_7w.d,_7z=_7w.e,_7A=E(_7w.b),_7B=E(_7A.a);if(_7s>=_7B){if(_7s!=_7B){return new F(function(){return _5C(_7A,_7x,_7y,B(_7r(_7s,_7t,_7u,_7z)));});}else{var _7C=E(_7A.b);if(_7t>=_7C){if(_7t!=_7C){return new F(function(){return _5C(_7A,_7x,_7y,B(_7r(_7s,_7t,_7u,_7z)));});}else{var _7D=E(_7A.c);if(_7u>=_7D){if(_7u!=_7D){return new F(function(){return _5C(_7A,_7x,_7y,B(_7r(_7s,_7t,_7u,_7z)));});}else{return new F(function(){return _7g(_7y,_7z);});}}else{return new F(function(){return _6j(_7A,_7x,B(_7r(_7s,_7t,_7u,_7y)),_7z);});}}}else{return new F(function(){return _6j(_7A,_7x,B(_7r(_7s,_7t,_7u,_7y)),_7z);});}}}else{return new F(function(){return _6j(_7A,_7x,B(_7r(_7s,_7t,_7u,_7y)),_7z);});}}else{return new T0(1);}},_7E=function(_7F,_7G,_7H,_7I){var _7J=E(_7I);if(!_7J._){var _7K=_7J.c,_7L=_7J.d,_7M=_7J.e,_7N=E(_7J.b),_7O=E(_7N.a);if(_7F>=_7O){if(_7F!=_7O){return new F(function(){return _5C(_7N,_7K,_7L,B(_7E(_7F,_7G,_7H,_7M)));});}else{var _7P=E(_7N.b);if(_7G>=_7P){if(_7G!=_7P){return new F(function(){return _5C(_7N,_7K,_7L,B(_7E(_7F,_7G,_7H,_7M)));});}else{var _7Q=E(_7H),_7R=E(_7N.c);if(_7Q>=_7R){if(_7Q!=_7R){return new F(function(){return _5C(_7N,_7K,_7L,B(_7r(_7F,_7G,_7Q,_7M)));});}else{return new F(function(){return _7g(_7L,_7M);});}}else{return new F(function(){return _6j(_7N,_7K,B(_7r(_7F,_7G,_7Q,_7L)),_7M);});}}}else{return new F(function(){return _6j(_7N,_7K,B(_7E(_7F,_7G,_7H,_7L)),_7M);});}}}else{return new F(function(){return _6j(_7N,_7K,B(_7E(_7F,_7G,_7H,_7L)),_7M);});}}else{return new T0(1);}},_7S=function(_7T,_7U,_7V,_7W){var _7X=E(_7W);if(!_7X._){var _7Y=_7X.c,_7Z=_7X.d,_80=_7X.e,_81=E(_7X.b),_82=E(_81.a);if(_7T>=_82){if(_7T!=_82){return new F(function(){return _5C(_81,_7Y,_7Z,B(_7S(_7T,_7U,_7V,_80)));});}else{var _83=E(_7U),_84=E(_81.b);if(_83>=_84){if(_83!=_84){return new F(function(){return _5C(_81,_7Y,_7Z,B(_7E(_7T,_83,_7V,_80)));});}else{var _85=E(_7V),_86=E(_81.c);if(_85>=_86){if(_85!=_86){return new F(function(){return _5C(_81,_7Y,_7Z,B(_7r(_7T,_83,_85,_80)));});}else{return new F(function(){return _7g(_7Z,_80);});}}else{return new F(function(){return _6j(_81,_7Y,B(_7r(_7T,_83,_85,_7Z)),_80);});}}}else{return new F(function(){return _6j(_81,_7Y,B(_7E(_7T,_83,_7V,_7Z)),_80);});}}}else{return new F(function(){return _6j(_81,_7Y,B(_7S(_7T,_7U,_7V,_7Z)),_80);});}}else{return new T0(1);}},_87=function(_88,_89,_8a,_8b){var _8c=E(_8b);if(!_8c._){var _8d=_8c.c,_8e=_8c.d,_8f=_8c.e,_8g=E(_8c.b),_8h=E(_88),_8i=E(_8g.a);if(_8h>=_8i){if(_8h!=_8i){return new F(function(){return _5C(_8g,_8d,_8e,B(_7S(_8h,_89,_8a,_8f)));});}else{var _8j=E(_89),_8k=E(_8g.b);if(_8j>=_8k){if(_8j!=_8k){return new F(function(){return _5C(_8g,_8d,_8e,B(_7E(_8h,_8j,_8a,_8f)));});}else{var _8l=E(_8a),_8m=E(_8g.c);if(_8l>=_8m){if(_8l!=_8m){return new F(function(){return _5C(_8g,_8d,_8e,B(_7r(_8h,_8j,_8l,_8f)));});}else{return new F(function(){return _7g(_8e,_8f);});}}else{return new F(function(){return _6j(_8g,_8d,B(_7r(_8h,_8j,_8l,_8e)),_8f);});}}}else{return new F(function(){return _6j(_8g,_8d,B(_7E(_8h,_8j,_8a,_8e)),_8f);});}}}else{return new F(function(){return _6j(_8g,_8d,B(_7S(_8h,_89,_8a,_8e)),_8f);});}}else{return new T0(1);}},_8n=function(_8o,_8p,_8q){while(1){var _8r=E(_8p);if(!_8r._){return E(_8q);}else{var _8s=E(_8r.a),_8t=_8s.a,_8u=_8s.b,_8v=_8s.c,_8w=B(_5g(_8t,_8u,_8v,_8q));if(!_8w._){return new F(function(){return _87(_8t,_8u,_8v,_8q);});}else{var _8x=B(A1(_8o,_8w.a)),_8y=B(_87(_8t,_8u,_8v,_8q));_8p=_8x;_8q=_8y;continue;}}}},_8z=function(_8A,_8B,_8C,_8D,_8E){var _8F=B(_5g(_8B,_8C,_8D,_8E));if(!_8F._){return new F(function(){return _87(_8B,_8C,_8D,_8E);});}else{return new F(function(){return _8n(_8A,B(A1(_8A,_8F.a)),B(_87(_8B,_8C,_8D,_8E)));});}},_8G=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_8H=new T(function(){return B(err(_8G));}),_8I=function(_8J){var _8K=E(_8J);return (_8K._==0)?E(_8H):E(_8K.a);},_8L=function(_8M,_8N,_8O,_8P){while(1){var _8Q=B((function(_8R,_8S,_8T,_8U){var _8V=E(_8T);if(!_8V._){return E(_8U);}else{var _8W=_8V.a,_8X=new T(function(){var _8Y=E(_8W);return B(_5g(_8Y.a,_8Y.b,_8Y.c,_8U));});if(!B(A1(_8S,new T(function(){return B(_8I(_8X));})))){var _8Z=E(_8X);if(!_8Z._){var _90=E(_8W);return new F(function(){return _87(_90.a,_90.b,_90.c,_8U);});}else{var _91=E(_8W),_92=_8R,_93=_8S,_94=B(A1(_8R,_8Z.a)),_95=B(_87(_91.a,_91.b,_91.c,_8U));_8M=_92;_8N=_93;_8O=_94;_8P=_95;return __continue;}}else{return E(_8U);}}})(_8M,_8N,_8O,_8P));if(_8Q!=__continue){return _8Q;}}},_96=function(_97){return E(E(_97).c);},_98=function(_99){return E(E(_99).d);},_9a=function(_9b){return E(E(_9b).e);},_9c=function(_9d,_9e,_9f,_9g){var _9h=B(_5g(_9d,_9e,_9f,_9g));if(!_9h._){return new F(function(){return _8z(_98,_9d,_9e,_9f,_9g);});}else{return new F(function(){return _8z(_98,_9d,_9e,_9f,B(_8L(_9a,new T(function(){var _9i=B(_5g(_9d,_9e,_9f,_9g));if(!_9i._){return E(_5v);}else{if(!E(E(_9i.a).c)){return E(_5v);}else{return E(_96);}}}),E(_9h.a).e,_9g)));});}},_9j=function(_9k,_9l,_9m,_9n,_9o){var _9p=E(_9o);if(!_9p._){var _9q=_9p.c,_9r=_9p.d,_9s=_9p.e,_9t=E(_9p.b),_9u=E(_9t.a);if(_9k>=_9u){if(_9k!=_9u){return new F(function(){return _6j(_9t,_9q,_9r,B(_9j(_9k,_9l,_9m,_9n,_9s)));});}else{var _9v=E(_9t.b);if(_9l>=_9v){if(_9l!=_9v){return new F(function(){return _6j(_9t,_9q,_9r,B(_9j(_9k,_9l,_9m,_9n,_9s)));});}else{var _9w=E(_9t.c);if(_9m>=_9w){if(_9m!=_9w){return new F(function(){return _6j(_9t,_9q,_9r,B(_9j(_9k,_9l,_9m,_9n,_9s)));});}else{return new T5(0,_9p.a,E(new T3(0,_9k,_9l,_9m)),_9n,E(_9r),E(_9s));}}else{return new F(function(){return _5C(_9t,_9q,B(_9j(_9k,_9l,_9m,_9n,_9r)),_9s);});}}}else{return new F(function(){return _5C(_9t,_9q,B(_9j(_9k,_9l,_9m,_9n,_9r)),_9s);});}}}else{return new F(function(){return _5C(_9t,_9q,B(_9j(_9k,_9l,_9m,_9n,_9r)),_9s);});}}else{return new T5(0,1,E(new T3(0,_9k,_9l,_9m)),_9n,E(_5x),E(_5x));}},_9x=function(_9y,_9z,_9A,_9B,_9C){var _9D=E(_9C);if(!_9D._){var _9E=_9D.c,_9F=_9D.d,_9G=_9D.e,_9H=E(_9D.b),_9I=E(_9H.a);if(_9y>=_9I){if(_9y!=_9I){return new F(function(){return _6j(_9H,_9E,_9F,B(_9x(_9y,_9z,_9A,_9B,_9G)));});}else{var _9J=E(_9H.b);if(_9z>=_9J){if(_9z!=_9J){return new F(function(){return _6j(_9H,_9E,_9F,B(_9x(_9y,_9z,_9A,_9B,_9G)));});}else{var _9K=E(_9A),_9L=E(_9H.c);if(_9K>=_9L){if(_9K!=_9L){return new F(function(){return _6j(_9H,_9E,_9F,B(_9j(_9y,_9z,_9K,_9B,_9G)));});}else{return new T5(0,_9D.a,E(new T3(0,_9y,_9z,_9K)),_9B,E(_9F),E(_9G));}}else{return new F(function(){return _5C(_9H,_9E,B(_9j(_9y,_9z,_9K,_9B,_9F)),_9G);});}}}else{return new F(function(){return _5C(_9H,_9E,B(_9x(_9y,_9z,_9A,_9B,_9F)),_9G);});}}}else{return new F(function(){return _5C(_9H,_9E,B(_9x(_9y,_9z,_9A,_9B,_9F)),_9G);});}}else{return new T5(0,1,E(new T3(0,_9y,_9z,_9A)),_9B,E(_5x),E(_5x));}},_9M=function(_9N,_9O,_9P,_9Q,_9R){var _9S=E(_9R);if(!_9S._){var _9T=_9S.c,_9U=_9S.d,_9V=_9S.e,_9W=E(_9S.b),_9X=E(_9W.a);if(_9N>=_9X){if(_9N!=_9X){return new F(function(){return _6j(_9W,_9T,_9U,B(_9M(_9N,_9O,_9P,_9Q,_9V)));});}else{var _9Y=E(_9O),_9Z=E(_9W.b);if(_9Y>=_9Z){if(_9Y!=_9Z){return new F(function(){return _6j(_9W,_9T,_9U,B(_9x(_9N,_9Y,_9P,_9Q,_9V)));});}else{var _a0=E(_9P),_a1=E(_9W.c);if(_a0>=_a1){if(_a0!=_a1){return new F(function(){return _6j(_9W,_9T,_9U,B(_9j(_9N,_9Y,_a0,_9Q,_9V)));});}else{return new T5(0,_9S.a,E(new T3(0,_9N,_9Y,_a0)),_9Q,E(_9U),E(_9V));}}else{return new F(function(){return _5C(_9W,_9T,B(_9j(_9N,_9Y,_a0,_9Q,_9U)),_9V);});}}}else{return new F(function(){return _5C(_9W,_9T,B(_9x(_9N,_9Y,_9P,_9Q,_9U)),_9V);});}}}else{return new F(function(){return _5C(_9W,_9T,B(_9M(_9N,_9O,_9P,_9Q,_9U)),_9V);});}}else{return new T5(0,1,E(new T3(0,_9N,_9O,_9P)),_9Q,E(_5x),E(_5x));}},_a2=function(_a3,_a4,_a5,_a6,_a7){var _a8=E(_a7);if(!_a8._){var _a9=_a8.c,_aa=_a8.d,_ab=_a8.e,_ac=E(_a8.b),_ad=E(_a3),_ae=E(_ac.a);if(_ad>=_ae){if(_ad!=_ae){return new F(function(){return _6j(_ac,_a9,_aa,B(_9M(_ad,_a4,_a5,_a6,_ab)));});}else{var _af=E(_a4),_ag=E(_ac.b);if(_af>=_ag){if(_af!=_ag){return new F(function(){return _6j(_ac,_a9,_aa,B(_9x(_ad,_af,_a5,_a6,_ab)));});}else{var _ah=E(_a5),_ai=E(_ac.c);if(_ah>=_ai){if(_ah!=_ai){return new F(function(){return _6j(_ac,_a9,_aa,B(_9j(_ad,_af,_ah,_a6,_ab)));});}else{return new T5(0,_a8.a,E(new T3(0,_ad,_af,_ah)),_a6,E(_aa),E(_ab));}}else{return new F(function(){return _5C(_ac,_a9,B(_9j(_ad,_af,_ah,_a6,_aa)),_ab);});}}}else{return new F(function(){return _5C(_ac,_a9,B(_9x(_ad,_af,_a5,_a6,_aa)),_ab);});}}}else{return new F(function(){return _5C(_ac,_a9,B(_9M(_ad,_a4,_a5,_a6,_aa)),_ab);});}}else{return new T5(0,1,E(new T3(0,_a3,_a4,_a5)),_a6,E(_5x),E(_5x));}},_aj=function(_ak,_al,_am,_an){while(1){var _ao=E(_an);if(!_ao._){var _ap=_ao.d,_aq=_ao.e,_ar=E(_ao.b),_as=E(_ar.a);if(_ak>=_as){if(_ak!=_as){_an=_aq;continue;}else{var _at=E(_ar.b);if(_al>=_at){if(_al!=_at){_an=_aq;continue;}else{var _au=E(_ar.c);if(_am>=_au){if(_am!=_au){_an=_aq;continue;}else{return new T1(1,_ao.c);}}else{_an=_ap;continue;}}}else{_an=_ap;continue;}}}else{_an=_ap;continue;}}else{return __Z;}}},_av=function(_aw,_ax,_ay,_az){while(1){var _aA=E(_az);if(!_aA._){var _aB=_aA.d,_aC=_aA.e,_aD=E(_aA.b),_aE=E(_aD.a);if(_aw>=_aE){if(_aw!=_aE){_az=_aC;continue;}else{var _aF=E(_aD.b);if(_ax>=_aF){if(_ax!=_aF){_az=_aC;continue;}else{var _aG=E(_ay),_aH=E(_aD.c);if(_aG>=_aH){if(_aG!=_aH){return new F(function(){return _aj(_aw,_ax,_aG,_aC);});}else{return new T1(1,_aA.c);}}else{return new F(function(){return _aj(_aw,_ax,_aG,_aB);});}}}else{_az=_aB;continue;}}}else{_az=_aB;continue;}}else{return __Z;}}},_aI=function(_aJ,_aK,_aL,_aM){while(1){var _aN=E(_aM);if(!_aN._){var _aO=_aN.d,_aP=_aN.e,_aQ=E(_aN.b),_aR=E(_aQ.a);if(_aJ>=_aR){if(_aJ!=_aR){_aM=_aP;continue;}else{var _aS=E(_aK),_aT=E(_aQ.b);if(_aS>=_aT){if(_aS!=_aT){return new F(function(){return _av(_aJ,_aS,_aL,_aP);});}else{var _aU=E(_aL),_aV=E(_aQ.c);if(_aU>=_aV){if(_aU!=_aV){return new F(function(){return _aj(_aJ,_aS,_aU,_aP);});}else{return new T1(1,_aN.c);}}else{return new F(function(){return _aj(_aJ,_aS,_aU,_aO);});}}}else{return new F(function(){return _av(_aJ,_aS,_aL,_aO);});}}}else{_aM=_aO;continue;}}else{return __Z;}}},_aW=function(_aX,_aY,_aZ,_b0){var _b1=E(_b0);if(!_b1._){var _b2=_b1.d,_b3=_b1.e,_b4=E(_b1.b),_b5=E(_aX),_b6=E(_b4.a);if(_b5>=_b6){if(_b5!=_b6){return new F(function(){return _aI(_b5,_aY,_aZ,_b3);});}else{var _b7=E(_aY),_b8=E(_b4.b);if(_b7>=_b8){if(_b7!=_b8){return new F(function(){return _av(_b5,_b7,_aZ,_b3);});}else{var _b9=E(_aZ),_ba=E(_b4.c);if(_b9>=_ba){if(_b9!=_ba){return new F(function(){return _aj(_b5,_b7,_b9,_b3);});}else{return new T1(1,_b1.c);}}else{return new F(function(){return _aj(_b5,_b7,_b9,_b2);});}}}else{return new F(function(){return _av(_b5,_b7,_aZ,_b2);});}}}else{return new F(function(){return _aI(_b5,_aY,_aZ,_b2);});}}else{return __Z;}},_bb=function(_bc){while(1){var _bd=E(_bc);if(!_bd._){return __Z;}else{_bc=_bd.b;continue;}}},_be=function(_bf,_bg){while(1){var _bh=E(_bf);if(!_bh._){return new T1(1,_bg);}else{var _bi=_bh.b;if(E(_bh.a)!=_bg){return new F(function(){return _bb(_bi);});}else{_bf=_bi;continue;}}}},_bj=new T(function(){return B(unCStr("!!: negative index"));}),_bk=new T(function(){return B(unCStr("Prelude."));}),_bl=new T(function(){return B(_5(_bk,_bj));}),_bm=new T(function(){return B(err(_bl));}),_bn=new T(function(){return B(unCStr("!!: index too large"));}),_bo=new T(function(){return B(_5(_bk,_bn));}),_bp=new T(function(){return B(err(_bo));}),_bq=function(_br,_bs){while(1){var _bt=E(_br);if(!_bt._){return E(_bp);}else{var _bu=E(_bs);if(!_bu){return E(_bt.a);}else{_br=_bt.b;_bs=_bu-1|0;continue;}}}},_bv=function(_bw,_bx){if(_bx>=0){return new F(function(){return _bq(_bw,_bx);});}else{return E(_bm);}},_by=function(_bz,_bA){while(1){var _bB=E(_bz);if(!_bB._){return E(_bA);}else{var _bC=_bA+1|0;_bz=_bB.b;_bA=_bC;continue;}}},_bD=new T(function(){return B(unCStr(": empty list"));}),_bE=function(_bF){return new F(function(){return err(B(_5(_bk,new T(function(){return B(_5(_bF,_bD));},1))));});},_bG=new T(function(){return B(unCStr("head"));}),_bH=new T(function(){return B(_bE(_bG));}),_bI=function(_bJ){while(1){var _bK=B((function(_bL){var _bM=E(_bL);if(!_bM._){return __Z;}else{var _bN=_bM.b,_bO=E(_bM.a),_bP=E(_bO);if(!_bP){_bJ=_bN;return __continue;}else{return new T2(1,new T(function(){if(_bP<0){return  -_bP;}else{return E(_bO);}}),new T(function(){return B(_bI(_bN));}));}}})(_bJ));if(_bK!=__continue){return _bK;}}},_bQ=function(_bR){return E(E(_bR).c);},_bS=new T2(1,_bQ,_x),_bT=function(_bU){return E(E(_bU).b);},_bV=new T2(1,_bT,_bS),_bW=function(_bX){return E(E(_bX).a);},_bY=new T2(1,_bW,_bV),_bZ=0,_c0=new T1(1,_bZ),_c1=-1,_c2=new T1(1,_c1),_c3=1,_c4=new T1(1,_c3),_c5=function(_c6,_c7,_c8,_c9,_ca){var _cb=B(_4j(function(_cc){return B(A1(_cc,_ca))-B(A1(_cc,_c9))|0;},_bY)),_cd=B(_bI(_cb)),_ce=E(_cd);if(!_ce._){var _cf=new T1(1,_bH);}else{var _cf=B(_be(_ce.b,E(_ce.a)));}var _cg=function(_ch){var _ci=function(_cj){var _ck=E(_c9),_cl=E(_ca),_cm=function(_cn){var _co=function(_cp){var _cq=B(_bv(_cb,_cp));return (_cq<=0)?(_cq>=0)?E(_c0):E(_c2):E(_c4);},_cr=B(_co(0));if(!_cr._){return __Z;}else{var _cs=B(_co(1));if(!_cs._){return __Z;}else{var _ct=B(_co(2));if(!_ct._){return __Z;}else{var _cu=E(_cf);return (_cu._==0)?__Z:new T1(1,new T5(0,_cr.a,_cs.a,_ct.a,_cu.a,_ck));}}}};if(E(_ck.a)!=E(_cl.a)){return new F(function(){return _cm(_);});}else{if(E(_ck.b)!=E(_cl.b)){return new F(function(){return _cm(_);});}else{if(E(_ck.c)!=E(_cl.c)){return new F(function(){return _cm(_);});}else{return new T1(1,new T5(0,_bZ,_bZ,_bZ,_bZ,_ck));}}}};if(!E(_c6)){if(!E(_c7)){return __Z;}else{if(B(_by(_cd,0))==2){return new F(function(){return _ci(_);});}else{return __Z;}}}else{var _cv=B(_by(_cd,0));if(_cv==1){return new F(function(){return _ci(_);});}else{if(!E(_c7)){return __Z;}else{if(E(_cv)==2){return new F(function(){return _ci(_);});}else{return __Z;}}}}},_cw=E(_cf);if(!_cw._){return new F(function(){return _cg(_);});}else{var _cx=E(_c8);if(!_cx._){return new F(function(){return _cg(_);});}else{if(E(_cw.a)<=E(_cx.a)){return new F(function(){return _cg(_);});}else{return __Z;}}}},_cy=false,_cz=true,_cA=function(_cB,_cC,_cD,_cE,_cF,_cG,_cH){var _cI=E(_cE);if(!_cI){return __Z;}else{var _cJ=new T(function(){return E(_cD)+E(_cH)|0;}),_cK=new T(function(){return E(_cC)+E(_cG)|0;}),_cL=new T(function(){return E(_cB)+E(_cF)|0;});return new T2(1,new T3(0,_cL,_cK,_cJ),new T(function(){return B(_cA(_cB,_cC,_cD,_cI-1|0,_cL,_cK,_cJ));}));}},_cM=function(_cN,_cO,_cP,_cQ,_cR){var _cS=E(_cQ);if(!_cS){return __Z;}else{var _cT=new T(function(){return E(_cP)+E(E(_cR).c)|0;}),_cU=new T(function(){return E(_cO)+E(E(_cR).b)|0;}),_cV=new T(function(){return E(_cN)+E(E(_cR).a)|0;});return new T2(1,new T3(0,_cV,_cU,_cT),new T(function(){return B(_cA(_cN,_cO,_cP,_cS-1|0,_cV,_cU,_cT));}));}},_cW=function(_cX){var _cY=E(_cX);return new F(function(){return _cM(_cY.a,_cY.b,_cY.c,E(_cY.d),_cY.e);});},_cZ=function(_d0,_d1,_d2,_d3,_d4){while(1){var _d5=B((function(_d6,_d7,_d8,_d9,_da){var _db=E(_d9);if(!_db._){return E(_da);}else{var _dc=_db.b,_dd=E(_db.a),_de=new T(function(){if(!B(_by(_dc,0))){return __Z;}else{return new T1(1,new T(function(){var _df=E(_dc);if(!_df._){return E(_bH);}else{return E(_df.a);}}));}}),_dg=_d6,_dh=_d7,_di=B(_a2(_dd.a,_dd.b,_dd.c,new T5(0,_d6,_d7,_cy,_de,_d8),_da));_d0=_dg;_d1=_dh;_d2=new T1(1,_dd);_d3=_dc;_d4=_di;return __continue;}})(_d0,_d1,_d2,_d3,_d4));if(_d5!=__continue){return _d5;}}},_dj=function(_dk,_dl,_dm,_dn,_do,_dp,_dq){var _dr=B(_c5(_dk,_dl,_dm,_do,_dp));if(!_dr._){return __Z;}else{var _ds=B(_cW(_dr.a)),_dt=function(_du,_dv){while(1){var _dw=B((function(_dx,_dy){var _dz=E(_dx);if(!_dz._){return E(_dy);}else{_du=_dz.b;_dv=new T(function(){var _dA=E(_dz.a);if(!B(_aW(_dA.a,_dA.b,_dA.c,_dq))._){return E(_dy);}else{return true;}},1);return __continue;}})(_du,_dv));if(_dw!=__continue){return _dw;}}};if(!B(_dt(_ds,_cy))){var _dB=E(_do),_dC=_dB.a,_dD=_dB.b,_dE=_dB.c,_dF=B(_aW(_dC,_dD,_dE,_dq));if(!_dF._){return __Z;}else{var _dG=_dF.a,_dH=E(_dn);if(!_dH._){return __Z;}else{var _dI=_dH.a,_dJ=new T(function(){return B(_a2(_dC,_dD,_dE,new T5(0,new T(function(){return E(E(_dG).a);}),new T(function(){return E(E(_dG).b);}),_cz,new T1(1,new T(function(){var _dK=E(_ds);if(!_dK._){return E(_bH);}else{return E(_dK.a);}})),new T(function(){return E(E(_dG).e);})),B(_cZ(new T(function(){return E(E(_dI).a);}),new T(function(){return E(E(_dI).b);}),new T1(1,_dB),_ds,_dq))));});return new T1(1,_dJ);}}}else{return __Z;}}},_dL=function(_dM,_dN,_dO,_dP){while(1){var _dQ=E(_dP);if(!_dQ._){var _dR=_dQ.d,_dS=_dQ.e,_dT=E(_dQ.b),_dU=E(_dT.a);if(_dM>=_dU){if(_dM!=_dU){_dP=_dS;continue;}else{var _dV=E(_dT.b);if(_dN>=_dV){if(_dN!=_dV){_dP=_dS;continue;}else{var _dW=E(_dT.c);if(_dO>=_dW){if(_dO!=_dW){_dP=_dS;continue;}else{return new T1(1,_dQ.c);}}else{_dP=_dR;continue;}}}else{_dP=_dR;continue;}}}else{_dP=_dR;continue;}}else{return __Z;}}},_dX=function(_dY,_dZ,_e0,_e1){while(1){var _e2=E(_e1);if(!_e2._){var _e3=_e2.d,_e4=_e2.e,_e5=E(_e2.b),_e6=E(_e5.a);if(_dY>=_e6){if(_dY!=_e6){_e1=_e4;continue;}else{var _e7=E(_e5.b);if(_dZ>=_e7){if(_dZ!=_e7){_e1=_e4;continue;}else{var _e8=E(_e0),_e9=E(_e5.c);if(_e8>=_e9){if(_e8!=_e9){return new F(function(){return _dL(_dY,_dZ,_e8,_e4);});}else{return new T1(1,_e2.c);}}else{return new F(function(){return _dL(_dY,_dZ,_e8,_e3);});}}}else{_e1=_e3;continue;}}}else{_e1=_e3;continue;}}else{return __Z;}}},_ea=function(_eb,_ec,_ed,_ee){while(1){var _ef=E(_ee);if(!_ef._){var _eg=_ef.d,_eh=_ef.e,_ei=E(_ef.b),_ej=E(_ei.a);if(_eb>=_ej){if(_eb!=_ej){_ee=_eh;continue;}else{var _ek=E(_ec),_el=E(_ei.b);if(_ek>=_el){if(_ek!=_el){return new F(function(){return _dX(_eb,_ek,_ed,_eh);});}else{var _em=E(_ed),_en=E(_ei.c);if(_em>=_en){if(_em!=_en){return new F(function(){return _dL(_eb,_ek,_em,_eh);});}else{return new T1(1,_ef.c);}}else{return new F(function(){return _dL(_eb,_ek,_em,_eg);});}}}else{return new F(function(){return _dX(_eb,_ek,_ed,_eg);});}}}else{_ee=_eg;continue;}}else{return __Z;}}},_eo=function(_ep,_eq,_er,_es){var _et=E(_es);if(!_et._){var _eu=_et.d,_ev=_et.e,_ew=E(_et.b),_ex=E(_ep),_ey=E(_ew.a);if(_ex>=_ey){if(_ex!=_ey){return new F(function(){return _ea(_ex,_eq,_er,_ev);});}else{var _ez=E(_eq),_eA=E(_ew.b);if(_ez>=_eA){if(_ez!=_eA){return new F(function(){return _dX(_ex,_ez,_er,_ev);});}else{var _eB=E(_er),_eC=E(_ew.c);if(_eB>=_eC){if(_eB!=_eC){return new F(function(){return _dL(_ex,_ez,_eB,_ev);});}else{return new T1(1,_et.c);}}else{return new F(function(){return _dL(_ex,_ez,_eB,_eu);});}}}else{return new F(function(){return _dX(_ex,_ez,_er,_eu);});}}}else{return new F(function(){return _ea(_ex,_eq,_er,_eu);});}}else{return __Z;}},_eD=function(_eE,_eF,_eG,_eH){while(1){var _eI=E(_eH);if(!_eI._){var _eJ=_eI.d,_eK=_eI.e,_eL=E(_eI.b),_eM=E(_eL.a);if(_eE>=_eM){if(_eE!=_eM){_eH=_eK;continue;}else{var _eN=E(_eL.b);if(_eF>=_eN){if(_eF!=_eN){_eH=_eK;continue;}else{var _eO=E(_eL.c);if(_eG>=_eO){if(_eG!=_eO){_eH=_eK;continue;}else{return new T1(1,_eI.c);}}else{_eH=_eJ;continue;}}}else{_eH=_eJ;continue;}}}else{_eH=_eJ;continue;}}else{return __Z;}}},_eP=function(_eQ,_eR,_eS,_eT){while(1){var _eU=E(_eT);if(!_eU._){var _eV=_eU.d,_eW=_eU.e,_eX=E(_eU.b),_eY=E(_eX.a);if(_eQ>=_eY){if(_eQ!=_eY){_eT=_eW;continue;}else{var _eZ=E(_eX.b);if(_eR>=_eZ){if(_eR!=_eZ){_eT=_eW;continue;}else{var _f0=E(_eS),_f1=E(_eX.c);if(_f0>=_f1){if(_f0!=_f1){return new F(function(){return _eD(_eQ,_eR,_f0,_eW);});}else{return new T1(1,_eU.c);}}else{return new F(function(){return _eD(_eQ,_eR,_f0,_eV);});}}}else{_eT=_eV;continue;}}}else{_eT=_eV;continue;}}else{return __Z;}}},_f2=function(_f3,_f4,_f5,_f6){while(1){var _f7=E(_f6);if(!_f7._){var _f8=_f7.d,_f9=_f7.e,_fa=E(_f7.b),_fb=E(_fa.a);if(_f3>=_fb){if(_f3!=_fb){_f6=_f9;continue;}else{var _fc=E(_f4),_fd=E(_fa.b);if(_fc>=_fd){if(_fc!=_fd){return new F(function(){return _eP(_f3,_fc,_f5,_f9);});}else{var _fe=E(_f5),_ff=E(_fa.c);if(_fe>=_ff){if(_fe!=_ff){return new F(function(){return _eD(_f3,_fc,_fe,_f9);});}else{return new T1(1,_f7.c);}}else{return new F(function(){return _eD(_f3,_fc,_fe,_f8);});}}}else{return new F(function(){return _eP(_f3,_fc,_f5,_f8);});}}}else{_f6=_f8;continue;}}else{return __Z;}}},_fg=function(_fh,_fi,_fj,_fk){var _fl=E(_fk);if(!_fl._){var _fm=_fl.d,_fn=_fl.e,_fo=E(_fl.b),_fp=E(_fh),_fq=E(_fo.a);if(_fp>=_fq){if(_fp!=_fq){return new F(function(){return _f2(_fp,_fi,_fj,_fn);});}else{var _fr=E(_fi),_fs=E(_fo.b);if(_fr>=_fs){if(_fr!=_fs){return new F(function(){return _eP(_fp,_fr,_fj,_fn);});}else{var _ft=E(_fj),_fu=E(_fo.c);if(_ft>=_fu){if(_ft!=_fu){return new F(function(){return _eD(_fp,_fr,_ft,_fn);});}else{return new T1(1,_fl.c);}}else{return new F(function(){return _eD(_fp,_fr,_ft,_fm);});}}}else{return new F(function(){return _eP(_fp,_fr,_fj,_fm);});}}}else{return new F(function(){return _f2(_fp,_fi,_fj,_fm);});}}else{return __Z;}},_fv=function(_fw,_fx){var _fy=E(_fw),_fz=E(_fx);return (E(_fy.a)!=E(_fz.a))?true:(E(_fy.b)!=E(_fz.b))?true:(E(_fy.c)!=E(_fz.c))?true:false;},_fA=function(_fB,_fC){return E(_fB)==E(_fC);},_fD=function(_fE,_fF,_fG,_fH,_fI,_fJ){if(_fE!=_fH){return false;}else{if(E(_fF)!=E(_fI)){return false;}else{return new F(function(){return _fA(_fG,_fJ);});}}},_fK=function(_fL,_fM){var _fN=E(_fL),_fO=E(_fM);return new F(function(){return _fD(E(_fN.a),_fN.b,_fN.c,E(_fO.a),_fO.b,_fO.c);});},_fP=new T2(0,_fK,_fv),_fQ=function(_fR,_fS){return E(_fR)<E(_fS);},_fT=function(_fU,_fV,_fW,_fX,_fY,_fZ){if(_fU>=_fX){if(_fU!=_fX){return false;}else{var _g0=E(_fV),_g1=E(_fY);if(_g0>=_g1){if(_g0!=_g1){return false;}else{return new F(function(){return _fQ(_fW,_fZ);});}}else{return true;}}}else{return true;}},_g2=function(_g3,_g4){var _g5=E(_g3),_g6=E(_g4);return new F(function(){return _fT(E(_g5.a),_g5.b,_g5.c,E(_g6.a),_g6.b,_g6.c);});},_g7=function(_g8,_g9){return E(_g8)<=E(_g9);},_ga=function(_gb,_gc,_gd,_ge,_gf,_gg){if(_gb>=_ge){if(_gb!=_ge){return false;}else{var _gh=E(_gc),_gi=E(_gf);if(_gh>=_gi){if(_gh!=_gi){return false;}else{return new F(function(){return _g7(_gd,_gg);});}}else{return true;}}}else{return true;}},_gj=function(_gk,_gl){var _gm=E(_gk),_gn=E(_gl);return new F(function(){return _ga(E(_gm.a),_gm.b,_gm.c,E(_gn.a),_gn.b,_gn.c);});},_go=function(_gp,_gq){return E(_gp)>E(_gq);},_gr=function(_gs,_gt,_gu,_gv,_gw,_gx){if(_gs>=_gv){if(_gs!=_gv){return true;}else{var _gy=E(_gt),_gz=E(_gw);if(_gy>=_gz){if(_gy!=_gz){return true;}else{return new F(function(){return _go(_gu,_gx);});}}else{return false;}}}else{return false;}},_gA=function(_gB,_gC){var _gD=E(_gB),_gE=E(_gC);return new F(function(){return _gr(E(_gD.a),_gD.b,_gD.c,E(_gE.a),_gE.b,_gE.c);});},_gF=function(_gG,_gH){return E(_gG)>=E(_gH);},_gI=function(_gJ,_gK,_gL,_gM,_gN,_gO){if(_gJ>=_gM){if(_gJ!=_gM){return true;}else{var _gP=E(_gK),_gQ=E(_gN);if(_gP>=_gQ){if(_gP!=_gQ){return true;}else{return new F(function(){return _gF(_gL,_gO);});}}else{return false;}}}else{return false;}},_gR=function(_gS,_gT){var _gU=E(_gS),_gV=E(_gT);return new F(function(){return _gI(E(_gU.a),_gU.b,_gU.c,E(_gV.a),_gV.b,_gV.c);});},_gW=function(_gX,_gY){return (_gX>=_gY)?(_gX!=_gY)?2:1:0;},_gZ=function(_h0,_h1){return new F(function(){return _gW(E(_h0),E(_h1));});},_h2=function(_h3,_h4,_h5,_h6,_h7,_h8){if(_h3>=_h6){if(_h3!=_h6){return 2;}else{var _h9=E(_h4),_ha=E(_h7);if(_h9>=_ha){if(_h9!=_ha){return 2;}else{return new F(function(){return _gZ(_h5,_h8);});}}else{return 0;}}}else{return 0;}},_hb=function(_hc,_hd){var _he=E(_hc),_hf=E(_hd);return new F(function(){return _h2(E(_he.a),_he.b,_he.c,E(_hf.a),_hf.b,_hf.c);});},_hg=function(_hh,_hi){var _hj=E(_hh),_hk=E(_hj.a),_hl=E(_hi),_hm=E(_hl.a);if(_hk>=_hm){if(_hk!=_hm){return E(_hj);}else{var _hn=E(_hj.b),_ho=E(_hl.b);return (_hn>=_ho)?(_hn!=_ho)?E(_hj):(E(_hj.c)>E(_hl.c))?E(_hj):E(_hl):E(_hl);}}else{return E(_hl);}},_hp=function(_hq,_hr){var _hs=E(_hq),_ht=E(_hs.a),_hu=E(_hr),_hv=E(_hu.a);if(_ht>=_hv){if(_ht!=_hv){return E(_hu);}else{var _hw=E(_hs.b),_hx=E(_hu.b);return (_hw>=_hx)?(_hw!=_hx)?E(_hu):(E(_hs.c)>E(_hu.c))?E(_hu):E(_hs):E(_hs);}}else{return E(_hs);}},_hy={_:0,a:_fP,b:_hb,c:_g2,d:_gj,e:_gA,f:_gR,g:_hg,h:_hp},_hz=function(_hA,_hB){return new T5(0,1,E(_hA),_hB,E(_5x),E(_5x));},_hC=function(_hD,_hE,_hF){var _hG=E(_hF);if(!_hG._){return new F(function(){return _6j(_hG.b,_hG.c,_hG.d,B(_hC(_hD,_hE,_hG.e)));});}else{return new F(function(){return _hz(_hD,_hE);});}},_hH=function(_hI,_hJ,_hK){var _hL=E(_hK);if(!_hL._){return new F(function(){return _5C(_hL.b,_hL.c,B(_hH(_hI,_hJ,_hL.d)),_hL.e);});}else{return new F(function(){return _hz(_hI,_hJ);});}},_hM=function(_hN,_hO,_hP,_hQ,_hR,_hS,_hT){return new F(function(){return _5C(_hQ,_hR,B(_hH(_hN,_hO,_hS)),_hT);});},_hU=function(_hV,_hW,_hX,_hY,_hZ,_i0,_i1,_i2){var _i3=E(_hX);if(!_i3._){var _i4=_i3.a,_i5=_i3.b,_i6=_i3.c,_i7=_i3.d,_i8=_i3.e;if((imul(3,_i4)|0)>=_hY){if((imul(3,_hY)|0)>=_i4){return new T5(0,(_i4+_hY|0)+1|0,E(_hV),_hW,E(_i3),E(new T5(0,_hY,E(_hZ),_i0,E(_i1),E(_i2))));}else{return new F(function(){return _6j(_i5,_i6,_i7,B(_hU(_hV,_hW,_i8,_hY,_hZ,_i0,_i1,_i2)));});}}else{return new F(function(){return _5C(_hZ,_i0,B(_i9(_hV,_hW,_i4,_i5,_i6,_i7,_i8,_i1)),_i2);});}}else{return new F(function(){return _hM(_hV,_hW,_hY,_hZ,_i0,_i1,_i2);});}},_i9=function(_ia,_ib,_ic,_id,_ie,_if,_ig,_ih){var _ii=E(_ih);if(!_ii._){var _ij=_ii.a,_ik=_ii.b,_il=_ii.c,_im=_ii.d,_in=_ii.e;if((imul(3,_ic)|0)>=_ij){if((imul(3,_ij)|0)>=_ic){return new T5(0,(_ic+_ij|0)+1|0,E(_ia),_ib,E(new T5(0,_ic,E(_id),_ie,E(_if),E(_ig))),E(_ii));}else{return new F(function(){return _6j(_id,_ie,_if,B(_hU(_ia,_ib,_ig,_ij,_ik,_il,_im,_in)));});}}else{return new F(function(){return _5C(_ik,_il,B(_i9(_ia,_ib,_ic,_id,_ie,_if,_ig,_im)),_in);});}}else{return new F(function(){return _hC(_ia,_ib,new T5(0,_ic,E(_id),_ie,E(_if),E(_ig)));});}},_io=function(_ip,_iq,_ir,_is){var _it=E(_ir);if(!_it._){var _iu=_it.a,_iv=_it.b,_iw=_it.c,_ix=_it.d,_iy=_it.e,_iz=E(_is);if(!_iz._){var _iA=_iz.a,_iB=_iz.b,_iC=_iz.c,_iD=_iz.d,_iE=_iz.e;if((imul(3,_iu)|0)>=_iA){if((imul(3,_iA)|0)>=_iu){return new T5(0,(_iu+_iA|0)+1|0,E(_ip),_iq,E(_it),E(_iz));}else{return new F(function(){return _6j(_iv,_iw,_ix,B(_hU(_ip,_iq,_iy,_iA,_iB,_iC,_iD,_iE)));});}}else{return new F(function(){return _5C(_iB,_iC,B(_i9(_ip,_iq,_iu,_iv,_iw,_ix,_iy,_iD)),_iE);});}}else{return new F(function(){return _hC(_ip,_iq,_it);});}}else{return new F(function(){return _hH(_ip,_iq,_is);});}},_iF=function(_iG,_iH,_iI,_iJ,_iK,_iL){var _iM=E(_iG);if(_iM==1){var _iN=E(_iL);if(!_iN._){return new T3(0,new T5(0,1,E(new T3(0,_iH,_iI,_iJ)),_iK,E(_5x),E(_5x)),_x,_x);}else{var _iO=E(E(_iN.a).a),_iP=E(_iO.a);if(_iH>=_iP){if(_iH!=_iP){return new T3(0,new T5(0,1,E(new T3(0,_iH,_iI,_iJ)),_iK,E(_5x),E(_5x)),_x,_iN);}else{var _iQ=E(_iO.b);return (_iI>=_iQ)?(_iI!=_iQ)?new T3(0,new T5(0,1,E(new T3(0,_iH,_iI,_iJ)),_iK,E(_5x),E(_5x)),_x,_iN):(_iJ<E(_iO.c))?new T3(0,new T5(0,1,E(new T3(0,_iH,_iI,_iJ)),_iK,E(_5x),E(_5x)),_iN,_x):new T3(0,new T5(0,1,E(new T3(0,_iH,_iI,_iJ)),_iK,E(_5x),E(_5x)),_x,_iN):new T3(0,new T5(0,1,E(new T3(0,_iH,_iI,_iJ)),_iK,E(_5x),E(_5x)),_iN,_x);}}else{return new T3(0,new T5(0,1,E(new T3(0,_iH,_iI,_iJ)),_iK,E(_5x),E(_5x)),_iN,_x);}}}else{var _iR=B(_iF(_iM>>1,_iH,_iI,_iJ,_iK,_iL)),_iS=_iR.a,_iT=_iR.c,_iU=E(_iR.b);if(!_iU._){return new T3(0,_iS,_x,_iT);}else{var _iV=E(_iU.a),_iW=_iV.a,_iX=_iV.b,_iY=E(_iU.b);if(!_iY._){return new T3(0,new T(function(){return B(_hC(_iW,_iX,_iS));}),_x,_iT);}else{var _iZ=_iY.b,_j0=E(_iY.a),_j1=_j0.b,_j2=E(_iW),_j3=E(_j2.a),_j4=E(_j0.a),_j5=_j4.b,_j6=_j4.c,_j7=E(_j4.a);if(_j3>=_j7){if(_j3!=_j7){return new T3(0,_iS,_x,_iU);}else{var _j8=E(_j2.b),_j9=E(_j5);if(_j8>=_j9){if(_j8!=_j9){return new T3(0,_iS,_x,_iU);}else{var _ja=E(_j6);if(E(_j2.c)<_ja){var _jb=B(_iF(_iM>>1,_j7,_j9,_ja,_j1,_iZ));return new T3(0,new T(function(){return B(_io(_j2,_iX,_iS,_jb.a));}),_jb.b,_jb.c);}else{return new T3(0,_iS,_x,_iU);}}}else{var _jc=B(_jd(_iM>>1,_j7,_j9,_j6,_j1,_iZ));return new T3(0,new T(function(){return B(_io(_j2,_iX,_iS,_jc.a));}),_jc.b,_jc.c);}}}else{var _je=B(_jf(_iM>>1,_j7,_j5,_j6,_j1,_iZ));return new T3(0,new T(function(){return B(_io(_j2,_iX,_iS,_je.a));}),_je.b,_je.c);}}}}},_jd=function(_jg,_jh,_ji,_jj,_jk,_jl){var _jm=E(_jg);if(_jm==1){var _jn=E(_jl);if(!_jn._){return new T3(0,new T5(0,1,E(new T3(0,_jh,_ji,_jj)),_jk,E(_5x),E(_5x)),_x,_x);}else{var _jo=E(E(_jn.a).a),_jp=E(_jo.a);if(_jh>=_jp){if(_jh!=_jp){return new T3(0,new T5(0,1,E(new T3(0,_jh,_ji,_jj)),_jk,E(_5x),E(_5x)),_x,_jn);}else{var _jq=E(_jo.b);if(_ji>=_jq){if(_ji!=_jq){return new T3(0,new T5(0,1,E(new T3(0,_jh,_ji,_jj)),_jk,E(_5x),E(_5x)),_x,_jn);}else{var _jr=E(_jj);return (_jr<E(_jo.c))?new T3(0,new T5(0,1,E(new T3(0,_jh,_ji,_jr)),_jk,E(_5x),E(_5x)),_jn,_x):new T3(0,new T5(0,1,E(new T3(0,_jh,_ji,_jr)),_jk,E(_5x),E(_5x)),_x,_jn);}}else{return new T3(0,new T5(0,1,E(new T3(0,_jh,_ji,_jj)),_jk,E(_5x),E(_5x)),_jn,_x);}}}else{return new T3(0,new T5(0,1,E(new T3(0,_jh,_ji,_jj)),_jk,E(_5x),E(_5x)),_jn,_x);}}}else{var _js=B(_jd(_jm>>1,_jh,_ji,_jj,_jk,_jl)),_jt=_js.a,_ju=_js.c,_jv=E(_js.b);if(!_jv._){return new T3(0,_jt,_x,_ju);}else{var _jw=E(_jv.a),_jx=_jw.a,_jy=_jw.b,_jz=E(_jv.b);if(!_jz._){return new T3(0,new T(function(){return B(_hC(_jx,_jy,_jt));}),_x,_ju);}else{var _jA=_jz.b,_jB=E(_jz.a),_jC=_jB.b,_jD=E(_jx),_jE=E(_jD.a),_jF=E(_jB.a),_jG=_jF.b,_jH=_jF.c,_jI=E(_jF.a);if(_jE>=_jI){if(_jE!=_jI){return new T3(0,_jt,_x,_jv);}else{var _jJ=E(_jD.b),_jK=E(_jG);if(_jJ>=_jK){if(_jJ!=_jK){return new T3(0,_jt,_x,_jv);}else{var _jL=E(_jH);if(E(_jD.c)<_jL){var _jM=B(_iF(_jm>>1,_jI,_jK,_jL,_jC,_jA));return new T3(0,new T(function(){return B(_io(_jD,_jy,_jt,_jM.a));}),_jM.b,_jM.c);}else{return new T3(0,_jt,_x,_jv);}}}else{var _jN=B(_jd(_jm>>1,_jI,_jK,_jH,_jC,_jA));return new T3(0,new T(function(){return B(_io(_jD,_jy,_jt,_jN.a));}),_jN.b,_jN.c);}}}else{var _jO=B(_jf(_jm>>1,_jI,_jG,_jH,_jC,_jA));return new T3(0,new T(function(){return B(_io(_jD,_jy,_jt,_jO.a));}),_jO.b,_jO.c);}}}}},_jf=function(_jP,_jQ,_jR,_jS,_jT,_jU){var _jV=E(_jP);if(_jV==1){var _jW=E(_jU);if(!_jW._){return new T3(0,new T5(0,1,E(new T3(0,_jQ,_jR,_jS)),_jT,E(_5x),E(_5x)),_x,_x);}else{var _jX=E(E(_jW.a).a),_jY=E(_jX.a);if(_jQ>=_jY){if(_jQ!=_jY){return new T3(0,new T5(0,1,E(new T3(0,_jQ,_jR,_jS)),_jT,E(_5x),E(_5x)),_x,_jW);}else{var _jZ=E(_jR),_k0=E(_jX.b);if(_jZ>=_k0){if(_jZ!=_k0){return new T3(0,new T5(0,1,E(new T3(0,_jQ,_jZ,_jS)),_jT,E(_5x),E(_5x)),_x,_jW);}else{var _k1=E(_jS);return (_k1<E(_jX.c))?new T3(0,new T5(0,1,E(new T3(0,_jQ,_jZ,_k1)),_jT,E(_5x),E(_5x)),_jW,_x):new T3(0,new T5(0,1,E(new T3(0,_jQ,_jZ,_k1)),_jT,E(_5x),E(_5x)),_x,_jW);}}else{return new T3(0,new T5(0,1,E(new T3(0,_jQ,_jZ,_jS)),_jT,E(_5x),E(_5x)),_jW,_x);}}}else{return new T3(0,new T5(0,1,E(new T3(0,_jQ,_jR,_jS)),_jT,E(_5x),E(_5x)),_jW,_x);}}}else{var _k2=B(_jf(_jV>>1,_jQ,_jR,_jS,_jT,_jU)),_k3=_k2.a,_k4=_k2.c,_k5=E(_k2.b);if(!_k5._){return new T3(0,_k3,_x,_k4);}else{var _k6=E(_k5.a),_k7=_k6.a,_k8=_k6.b,_k9=E(_k5.b);if(!_k9._){return new T3(0,new T(function(){return B(_hC(_k7,_k8,_k3));}),_x,_k4);}else{var _ka=_k9.b,_kb=E(_k9.a),_kc=_kb.b,_kd=E(_k7),_ke=E(_kd.a),_kf=E(_kb.a),_kg=_kf.b,_kh=_kf.c,_ki=E(_kf.a);if(_ke>=_ki){if(_ke!=_ki){return new T3(0,_k3,_x,_k5);}else{var _kj=E(_kd.b),_kk=E(_kg);if(_kj>=_kk){if(_kj!=_kk){return new T3(0,_k3,_x,_k5);}else{var _kl=E(_kh);if(E(_kd.c)<_kl){var _km=B(_iF(_jV>>1,_ki,_kk,_kl,_kc,_ka));return new T3(0,new T(function(){return B(_io(_kd,_k8,_k3,_km.a));}),_km.b,_km.c);}else{return new T3(0,_k3,_x,_k5);}}}else{var _kn=B(_jd(_jV>>1,_ki,_kk,_kh,_kc,_ka));return new T3(0,new T(function(){return B(_io(_kd,_k8,_k3,_kn.a));}),_kn.b,_kn.c);}}}else{var _ko=B(_jf(_jV>>1,_ki,_kg,_kh,_kc,_ka));return new T3(0,new T(function(){return B(_io(_kd,_k8,_k3,_ko.a));}),_ko.b,_ko.c);}}}}},_kp=function(_kq,_kr,_ks,_kt,_ku){var _kv=E(_ku);if(!_kv._){var _kw=_kv.c,_kx=_kv.d,_ky=_kv.e,_kz=E(_kv.b),_kA=E(_kz.a);if(_kq>=_kA){if(_kq!=_kA){return new F(function(){return _6j(_kz,_kw,_kx,B(_kp(_kq,_kr,_ks,_kt,_ky)));});}else{var _kB=E(_kz.b);if(_kr>=_kB){if(_kr!=_kB){return new F(function(){return _6j(_kz,_kw,_kx,B(_kp(_kq,_kr,_ks,_kt,_ky)));});}else{var _kC=E(_kz.c);if(_ks>=_kC){if(_ks!=_kC){return new F(function(){return _6j(_kz,_kw,_kx,B(_kp(_kq,_kr,_ks,_kt,_ky)));});}else{return new T5(0,_kv.a,E(new T3(0,_kq,_kr,_ks)),_kt,E(_kx),E(_ky));}}else{return new F(function(){return _5C(_kz,_kw,B(_kp(_kq,_kr,_ks,_kt,_kx)),_ky);});}}}else{return new F(function(){return _5C(_kz,_kw,B(_kp(_kq,_kr,_ks,_kt,_kx)),_ky);});}}}else{return new F(function(){return _5C(_kz,_kw,B(_kp(_kq,_kr,_ks,_kt,_kx)),_ky);});}}else{return new T5(0,1,E(new T3(0,_kq,_kr,_ks)),_kt,E(_5x),E(_5x));}},_kD=function(_kE,_kF,_kG,_kH,_kI){var _kJ=E(_kI);if(!_kJ._){var _kK=_kJ.c,_kL=_kJ.d,_kM=_kJ.e,_kN=E(_kJ.b),_kO=E(_kN.a);if(_kE>=_kO){if(_kE!=_kO){return new F(function(){return _6j(_kN,_kK,_kL,B(_kD(_kE,_kF,_kG,_kH,_kM)));});}else{var _kP=E(_kN.b);if(_kF>=_kP){if(_kF!=_kP){return new F(function(){return _6j(_kN,_kK,_kL,B(_kD(_kE,_kF,_kG,_kH,_kM)));});}else{var _kQ=E(_kG),_kR=E(_kN.c);if(_kQ>=_kR){if(_kQ!=_kR){return new F(function(){return _6j(_kN,_kK,_kL,B(_kp(_kE,_kF,_kQ,_kH,_kM)));});}else{return new T5(0,_kJ.a,E(new T3(0,_kE,_kF,_kQ)),_kH,E(_kL),E(_kM));}}else{return new F(function(){return _5C(_kN,_kK,B(_kp(_kE,_kF,_kQ,_kH,_kL)),_kM);});}}}else{return new F(function(){return _5C(_kN,_kK,B(_kD(_kE,_kF,_kG,_kH,_kL)),_kM);});}}}else{return new F(function(){return _5C(_kN,_kK,B(_kD(_kE,_kF,_kG,_kH,_kL)),_kM);});}}else{return new T5(0,1,E(new T3(0,_kE,_kF,_kG)),_kH,E(_5x),E(_5x));}},_kS=function(_kT,_kU,_kV,_kW,_kX){var _kY=E(_kX);if(!_kY._){var _kZ=_kY.c,_l0=_kY.d,_l1=_kY.e,_l2=E(_kY.b),_l3=E(_l2.a);if(_kT>=_l3){if(_kT!=_l3){return new F(function(){return _6j(_l2,_kZ,_l0,B(_kS(_kT,_kU,_kV,_kW,_l1)));});}else{var _l4=E(_kU),_l5=E(_l2.b);if(_l4>=_l5){if(_l4!=_l5){return new F(function(){return _6j(_l2,_kZ,_l0,B(_kD(_kT,_l4,_kV,_kW,_l1)));});}else{var _l6=E(_kV),_l7=E(_l2.c);if(_l6>=_l7){if(_l6!=_l7){return new F(function(){return _6j(_l2,_kZ,_l0,B(_kp(_kT,_l4,_l6,_kW,_l1)));});}else{return new T5(0,_kY.a,E(new T3(0,_kT,_l4,_l6)),_kW,E(_l0),E(_l1));}}else{return new F(function(){return _5C(_l2,_kZ,B(_kp(_kT,_l4,_l6,_kW,_l0)),_l1);});}}}else{return new F(function(){return _5C(_l2,_kZ,B(_kD(_kT,_l4,_kV,_kW,_l0)),_l1);});}}}else{return new F(function(){return _5C(_l2,_kZ,B(_kS(_kT,_kU,_kV,_kW,_l0)),_l1);});}}else{return new T5(0,1,E(new T3(0,_kT,_kU,_kV)),_kW,E(_5x),E(_5x));}},_l8=function(_l9,_la,_lb,_lc,_ld){var _le=E(_ld);if(!_le._){var _lf=_le.c,_lg=_le.d,_lh=_le.e,_li=E(_le.b),_lj=E(_l9),_lk=E(_li.a);if(_lj>=_lk){if(_lj!=_lk){return new F(function(){return _6j(_li,_lf,_lg,B(_kS(_lj,_la,_lb,_lc,_lh)));});}else{var _ll=E(_la),_lm=E(_li.b);if(_ll>=_lm){if(_ll!=_lm){return new F(function(){return _6j(_li,_lf,_lg,B(_kD(_lj,_ll,_lb,_lc,_lh)));});}else{var _ln=E(_lb),_lo=E(_li.c);if(_ln>=_lo){if(_ln!=_lo){return new F(function(){return _6j(_li,_lf,_lg,B(_kp(_lj,_ll,_ln,_lc,_lh)));});}else{return new T5(0,_le.a,E(new T3(0,_lj,_ll,_ln)),_lc,E(_lg),E(_lh));}}else{return new F(function(){return _5C(_li,_lf,B(_kp(_lj,_ll,_ln,_lc,_lg)),_lh);});}}}else{return new F(function(){return _5C(_li,_lf,B(_kD(_lj,_ll,_lb,_lc,_lg)),_lh);});}}}else{return new F(function(){return _5C(_li,_lf,B(_kS(_lj,_la,_lb,_lc,_lg)),_lh);});}}else{return new T5(0,1,E(new T3(0,_l9,_la,_lb)),_lc,E(_5x),E(_5x));}},_lp=function(_lq,_lr){while(1){var _ls=E(_lr);if(!_ls._){return E(_lq);}else{var _lt=E(_ls.a),_lu=E(_lt.a),_lv=B(_l8(_lu.a,_lu.b,_lu.c,_lt.b,_lq));_lq=_lv;_lr=_ls.b;continue;}}},_lw=function(_lx,_ly,_lz,_lA,_lB,_lC){return new F(function(){return _lp(B(_l8(_ly,_lz,_lA,_lB,_lx)),_lC);});},_lD=function(_lE,_lF,_lG){var _lH=E(_lF),_lI=E(_lH.a);return new F(function(){return _lp(B(_l8(_lI.a,_lI.b,_lI.c,_lH.b,_lE)),_lG);});},_lJ=function(_lK,_lL,_lM){var _lN=E(_lM);if(!_lN._){return E(_lL);}else{var _lO=E(_lN.a),_lP=_lO.a,_lQ=_lO.b,_lR=E(_lN.b);if(!_lR._){return new F(function(){return _hC(_lP,_lQ,_lL);});}else{var _lS=E(_lR.a),_lT=E(_lP),_lU=_lT.b,_lV=_lT.c,_lW=E(_lT.a),_lX=E(_lS.a),_lY=_lX.b,_lZ=_lX.c,_m0=E(_lX.a),_m1=function(_m2){var _m3=B(_jf(_lK,_m0,_lY,_lZ,_lS.b,_lR.b)),_m4=_m3.a,_m5=E(_m3.c);if(!_m5._){return new F(function(){return _lJ(_lK<<1,B(_io(_lT,_lQ,_lL,_m4)),_m3.b);});}else{return new F(function(){return _lD(B(_io(_lT,_lQ,_lL,_m4)),_m5.a,_m5.b);});}};if(_lW>=_m0){if(_lW!=_m0){return new F(function(){return _lw(_lL,_lW,_lU,_lV,_lQ,_lR);});}else{var _m6=E(_lU),_m7=E(_lY);if(_m6>=_m7){if(_m6!=_m7){return new F(function(){return _lw(_lL,_lW,_m6,_lV,_lQ,_lR);});}else{var _m8=E(_lV);if(_m8<E(_lZ)){return new F(function(){return _m1(_);});}else{return new F(function(){return _lw(_lL,_lW,_m6,_m8,_lQ,_lR);});}}}else{return new F(function(){return _m1(_);});}}}else{return new F(function(){return _m1(_);});}}}},_m9=function(_ma,_mb,_mc,_md,_me,_mf,_mg){var _mh=E(_mg);if(!_mh._){return new F(function(){return _hC(new T3(0,_mc,_md,_me),_mf,_mb);});}else{var _mi=E(_mh.a),_mj=E(_mi.a),_mk=_mj.b,_ml=_mj.c,_mm=E(_mj.a),_mn=function(_mo){var _mp=B(_jf(_ma,_mm,_mk,_ml,_mi.b,_mh.b)),_mq=_mp.a,_mr=E(_mp.c);if(!_mr._){return new F(function(){return _lJ(_ma<<1,B(_io(new T3(0,_mc,_md,_me),_mf,_mb,_mq)),_mp.b);});}else{return new F(function(){return _lD(B(_io(new T3(0,_mc,_md,_me),_mf,_mb,_mq)),_mr.a,_mr.b);});}};if(_mc>=_mm){if(_mc!=_mm){return new F(function(){return _lw(_mb,_mc,_md,_me,_mf,_mh);});}else{var _ms=E(_mk);if(_md>=_ms){if(_md!=_ms){return new F(function(){return _lw(_mb,_mc,_md,_me,_mf,_mh);});}else{var _mt=E(_me);if(_mt<E(_ml)){return new F(function(){return _mn(_);});}else{return new F(function(){return _lw(_mb,_mc,_md,_mt,_mf,_mh);});}}}else{return new F(function(){return _mn(_);});}}}else{return new F(function(){return _mn(_);});}}},_mu=function(_mv,_mw,_mx,_my,_mz,_mA,_mB){var _mC=E(_mB);if(!_mC._){return new F(function(){return _hC(new T3(0,_mx,_my,_mz),_mA,_mw);});}else{var _mD=E(_mC.a),_mE=E(_mD.a),_mF=_mE.b,_mG=_mE.c,_mH=E(_mE.a),_mI=function(_mJ){var _mK=B(_jf(_mv,_mH,_mF,_mG,_mD.b,_mC.b)),_mL=_mK.a,_mM=E(_mK.c);if(!_mM._){return new F(function(){return _lJ(_mv<<1,B(_io(new T3(0,_mx,_my,_mz),_mA,_mw,_mL)),_mK.b);});}else{return new F(function(){return _lD(B(_io(new T3(0,_mx,_my,_mz),_mA,_mw,_mL)),_mM.a,_mM.b);});}};if(_mx>=_mH){if(_mx!=_mH){return new F(function(){return _lw(_mw,_mx,_my,_mz,_mA,_mC);});}else{var _mN=E(_my),_mO=E(_mF);if(_mN>=_mO){if(_mN!=_mO){return new F(function(){return _lw(_mw,_mx,_mN,_mz,_mA,_mC);});}else{var _mP=E(_mz);if(_mP<E(_mG)){return new F(function(){return _mI(_);});}else{return new F(function(){return _lw(_mw,_mx,_mN,_mP,_mA,_mC);});}}}else{return new F(function(){return _mI(_);});}}}else{return new F(function(){return _mI(_);});}}},_mQ=function(_mR,_mS,_mT,_mU,_mV,_mW,_mX){var _mY=E(_mX);if(!_mY._){return new F(function(){return _hC(new T3(0,_mT,_mU,_mV),_mW,_mS);});}else{var _mZ=E(_mY.a),_n0=E(_mZ.a),_n1=_n0.b,_n2=_n0.c,_n3=E(_n0.a),_n4=function(_n5){var _n6=B(_jf(_mR,_n3,_n1,_n2,_mZ.b,_mY.b)),_n7=_n6.a,_n8=E(_n6.c);if(!_n8._){return new F(function(){return _lJ(_mR<<1,B(_io(new T3(0,_mT,_mU,_mV),_mW,_mS,_n7)),_n6.b);});}else{return new F(function(){return _lD(B(_io(new T3(0,_mT,_mU,_mV),_mW,_mS,_n7)),_n8.a,_n8.b);});}};if(_mT>=_n3){if(_mT!=_n3){return new F(function(){return _lw(_mS,_mT,_mU,_mV,_mW,_mY);});}else{var _n9=E(_n1);if(_mU>=_n9){if(_mU!=_n9){return new F(function(){return _lw(_mS,_mT,_mU,_mV,_mW,_mY);});}else{if(_mV<E(_n2)){return new F(function(){return _n4(_);});}else{return new F(function(){return _lw(_mS,_mT,_mU,_mV,_mW,_mY);});}}}else{return new F(function(){return _n4(_);});}}}else{return new F(function(){return _n4(_);});}}},_na=function(_nb){var _nc=E(_nb);if(!_nc._){return new T0(1);}else{var _nd=E(_nc.a),_ne=_nd.a,_nf=_nd.b,_ng=E(_nc.b);if(!_ng._){return new T5(0,1,E(_ne),_nf,E(_5x),E(_5x));}else{var _nh=_ng.b,_ni=E(_ng.a),_nj=_ni.b,_nk=E(_ne),_nl=E(_nk.a),_nm=E(_ni.a),_nn=_nm.b,_no=_nm.c,_np=E(_nm.a);if(_nl>=_np){if(_nl!=_np){return new F(function(){return _lw(new T5(0,1,E(_nk),_nf,E(_5x),E(_5x)),_np,_nn,_no,_nj,_nh);});}else{var _nq=E(_nk.b),_nr=E(_nn);if(_nq>=_nr){if(_nq!=_nr){return new F(function(){return _lw(new T5(0,1,E(_nk),_nf,E(_5x),E(_5x)),_np,_nr,_no,_nj,_nh);});}else{var _ns=E(_no);if(E(_nk.c)<_ns){return new F(function(){return _mQ(1,new T5(0,1,E(_nk),_nf,E(_5x),E(_5x)),_np,_nr,_ns,_nj,_nh);});}else{return new F(function(){return _lw(new T5(0,1,E(_nk),_nf,E(_5x),E(_5x)),_np,_nr,_ns,_nj,_nh);});}}}else{return new F(function(){return _m9(1,new T5(0,1,E(_nk),_nf,E(_5x),E(_5x)),_np,_nr,_no,_nj,_nh);});}}}else{return new F(function(){return _mu(1,new T5(0,1,E(_nk),_nf,E(_5x),E(_5x)),_np,_nn,_no,_nj,_nh);});}}}},_nt=function(_nu,_nv){var _nw=function(_nx,_ny){while(1){var _nz=B((function(_nA,_nB){var _nC=E(_nB);if(!_nC._){_nx=new T2(1,new T2(0,new T(function(){return B(A1(_nu,_nC.b));}),_nC.c),new T(function(){return B(_nw(_nA,_nC.e));}));_ny=_nC.d;return __continue;}else{return E(_nA);}})(_nx,_ny));if(_nz!=__continue){return _nz;}}};return new F(function(){return _na(B(_nw(_x,_nv)));});},_nD=__Z,_nE=function(_nF){return new T3(0,new T(function(){return E(E(_nF).a)+1|0;}),new T(function(){return B(_bT(_nF));}),new T(function(){return B(_bQ(_nF));}));},_nG=function(_nH,_nI,_nJ,_nK,_nL,_nM){var _nN=E(_nH);if(!_nN._){var _nO=_nN.a,_nP=_nN.b,_nQ=_nN.c,_nR=_nN.d,_nS=_nN.e;if((imul(3,_nO)|0)>=_nI){if((imul(3,_nI)|0)>=_nO){return new F(function(){return _7g(_nN,new T5(0,_nI,E(_nJ),_nK,E(_nL),E(_nM)));});}else{return new F(function(){return _6j(_nP,_nQ,_nR,B(_nG(_nS,_nI,_nJ,_nK,_nL,_nM)));});}}else{return new F(function(){return _5C(_nJ,_nK,B(_nT(_nO,_nP,_nQ,_nR,_nS,_nL)),_nM);});}}else{return new T5(0,_nI,E(_nJ),_nK,E(_nL),E(_nM));}},_nT=function(_nU,_nV,_nW,_nX,_nY,_nZ){var _o0=E(_nZ);if(!_o0._){var _o1=_o0.a,_o2=_o0.b,_o3=_o0.c,_o4=_o0.d,_o5=_o0.e;if((imul(3,_nU)|0)>=_o1){if((imul(3,_o1)|0)>=_nU){return new F(function(){return _7g(new T5(0,_nU,E(_nV),_nW,E(_nX),E(_nY)),_o0);});}else{return new F(function(){return _6j(_nV,_nW,_nX,B(_nG(_nY,_o1,_o2,_o3,_o4,_o5)));});}}else{return new F(function(){return _5C(_o2,_o3,B(_nT(_nU,_nV,_nW,_nX,_nY,_o4)),_o5);});}}else{return new T5(0,_nU,E(_nV),_nW,E(_nX),E(_nY));}},_o6=function(_o7,_o8){var _o9=E(_o7);if(!_o9._){var _oa=_o9.a,_ob=_o9.b,_oc=_o9.c,_od=_o9.d,_oe=_o9.e,_of=E(_o8);if(!_of._){var _og=_of.a,_oh=_of.b,_oi=_of.c,_oj=_of.d,_ok=_of.e;if((imul(3,_oa)|0)>=_og){if((imul(3,_og)|0)>=_oa){return new F(function(){return _7g(_o9,_of);});}else{return new F(function(){return _6j(_ob,_oc,_od,B(_nG(_oe,_og,_oh,_oi,_oj,_ok)));});}}else{return new F(function(){return _5C(_oh,_oi,B(_nT(_oa,_ob,_oc,_od,_oe,_oj)),_ok);});}}else{return E(_o9);}}else{return E(_o8);}},_ol=function(_om,_on){var _oo=E(_on);if(!_oo._){var _op=_oo.b,_oq=_oo.c,_or=_oo.d,_os=_oo.e;if(!B(A2(_om,_op,_oq))){return new F(function(){return _o6(B(_ol(_om,_or)),B(_ol(_om,_os)));});}else{return new F(function(){return _io(_op,_oq,B(_ol(_om,_or)),B(_ol(_om,_os)));});}}else{return new T0(1);}},_ot=function(_ou){return E(E(_ou).a);},_ov=function(_ow){return E(E(_ow).b);},_ox=function(_oy,_oz){return new T5(0,new T(function(){return B(_ot(_oz));}),new T(function(){return B(_ov(_oz));}),_cz,_2s,new T1(1,_oy));},_oA=function(_oB,_oC){return new T5(0,new T(function(){return B(_ot(_oC));}),new T(function(){return B(_ov(_oC));}),_cz,new T1(1,new T(function(){return B(_nE(_oB));})),new T(function(){return B(_9a(_oC));}));},_oD=function(_oE,_oF){return (E(E(_oF).d)._==0)?true:false;},_oG=function(_oH,_oI){var _oJ=E(_oI);if(!_oJ._){var _oK=_oJ.b;return new T5(0,_oJ.a,E(_oK),new T(function(){return B(A2(_oH,_oK,_oJ.c));}),E(B(_oG(_oH,_oJ.d))),E(B(_oG(_oH,_oJ.e))));}else{return new T0(1);}},_oL=function(_oM){return E(E(_oM).b);},_oN=function(_oO,_oP,_oQ){var _oR=E(_oP);if(!_oR._){return E(_oQ);}else{var _oS=function(_oT,_oU){while(1){var _oV=E(_oU);if(!_oV._){var _oW=_oV.b,_oX=_oV.e;switch(B(A3(_oL,_oO,_oT,_oW))){case 0:return new F(function(){return _io(_oW,_oV.c,B(_oS(_oT,_oV.d)),_oX);});break;case 1:return E(_oX);default:_oU=_oX;continue;}}else{return new T0(1);}}};return new F(function(){return _oS(_oR.a,_oQ);});}},_oY=function(_oZ,_p0,_p1){var _p2=E(_p0);if(!_p2._){return E(_p1);}else{var _p3=function(_p4,_p5){while(1){var _p6=E(_p5);if(!_p6._){var _p7=_p6.b,_p8=_p6.d;switch(B(A3(_oL,_oZ,_p7,_p4))){case 0:return new F(function(){return _io(_p7,_p6.c,_p8,B(_p3(_p4,_p6.e)));});break;case 1:return E(_p8);default:_p5=_p8;continue;}}else{return new T0(1);}}};return new F(function(){return _p3(_p2.a,_p1);});}},_p9=function(_pa,_pb,_pc,_pd){var _pe=E(_pb),_pf=E(_pd);if(!_pf._){var _pg=_pf.b,_ph=_pf.c,_pi=_pf.d,_pj=_pf.e;switch(B(A3(_oL,_pa,_pe,_pg))){case 0:return new F(function(){return _5C(_pg,_ph,B(_p9(_pa,_pe,_pc,_pi)),_pj);});break;case 1:return E(_pf);default:return new F(function(){return _6j(_pg,_ph,_pi,B(_p9(_pa,_pe,_pc,_pj)));});}}else{return new T5(0,1,E(_pe),_pc,E(_5x),E(_5x));}},_pk=function(_pl,_pm,_pn,_po){return new F(function(){return _p9(_pl,_pm,_pn,_po);});},_pp=function(_pq){return E(E(_pq).d);},_pr=function(_ps){return E(E(_ps).f);},_pt=function(_pu,_pv,_pw,_px){var _py=E(_pv);if(!_py._){var _pz=E(_pw);if(!_pz._){return E(_px);}else{var _pA=function(_pB,_pC){while(1){var _pD=E(_pC);if(!_pD._){if(!B(A3(_pr,_pu,_pD.b,_pB))){return E(_pD);}else{_pC=_pD.d;continue;}}else{return new T0(1);}}};return new F(function(){return _pA(_pz.a,_px);});}}else{var _pE=_py.a,_pF=E(_pw);if(!_pF._){var _pG=function(_pH,_pI){while(1){var _pJ=E(_pI);if(!_pJ._){if(!B(A3(_pp,_pu,_pJ.b,_pH))){return E(_pJ);}else{_pI=_pJ.e;continue;}}else{return new T0(1);}}};return new F(function(){return _pG(_pE,_px);});}else{var _pK=function(_pL,_pM,_pN){while(1){var _pO=E(_pN);if(!_pO._){var _pP=_pO.b;if(!B(A3(_pp,_pu,_pP,_pL))){if(!B(A3(_pr,_pu,_pP,_pM))){return E(_pO);}else{_pN=_pO.d;continue;}}else{_pN=_pO.e;continue;}}else{return new T0(1);}}};return new F(function(){return _pK(_pE,_pF.a,_px);});}}},_pQ=function(_pR,_pS,_pT,_pU,_pV){var _pW=E(_pV);if(!_pW._){var _pX=_pW.b,_pY=_pW.c,_pZ=_pW.d,_q0=_pW.e,_q1=E(_pU);if(!_q1._){var _q2=_q1.b,_q3=function(_q4){var _q5=new T1(1,E(_q2));return new F(function(){return _io(_q2,_q1.c,B(_pQ(_pR,_pS,_q5,_q1.d,B(_pt(_pR,_pS,_q5,_pW)))),B(_pQ(_pR,_q5,_pT,_q1.e,B(_pt(_pR,_q5,_pT,_pW)))));});};if(!E(_pZ)._){return new F(function(){return _q3(_);});}else{if(!E(_q0)._){return new F(function(){return _q3(_);});}else{return new F(function(){return _pk(_pR,_pX,_pY,_q1);});}}}else{return new F(function(){return _io(_pX,_pY,B(_oN(_pR,_pS,_pZ)),B(_oY(_pR,_pT,_q0)));});}}else{return E(_pU);}},_q6=function(_q7,_q8,_q9,_qa,_qb,_qc,_qd,_qe,_qf,_qg,_qh,_qi,_qj){var _qk=function(_ql){var _qm=new T1(1,E(_qb));return new F(function(){return _io(_qb,_qc,B(_pQ(_q7,_q8,_qm,_qd,B(_pt(_q7,_q8,_qm,new T5(0,_qf,E(_qg),_qh,E(_qi),E(_qj)))))),B(_pQ(_q7,_qm,_q9,_qe,B(_pt(_q7,_qm,_q9,new T5(0,_qf,E(_qg),_qh,E(_qi),E(_qj)))))));});};if(!E(_qi)._){return new F(function(){return _qk(_);});}else{if(!E(_qj)._){return new F(function(){return _qk(_);});}else{return new F(function(){return _pk(_q7,_qg,_qh,new T5(0,_qa,E(_qb),_qc,E(_qd),E(_qe)));});}}},_qn=function(_qo){var _qp=B(_ol(_oD,_qo)),_qq=function(_qr,_qs,_qt,_qu,_qv,_qw){var _qx=E(_qo);if(!_qx._){return new F(function(){return _q6(_hy,_nD,_nD,_qr,_qs,_qt,_qu,_qv,_qx.a,_qx.b,_qx.c,_qx.d,_qx.e);});}else{return E(_qw);}},_qy=B(_nt(_nE,B(_oG(_ox,_qp))));if(!_qy._){var _qz=_qy.a,_qA=_qy.b,_qB=_qy.c,_qC=_qy.d,_qD=_qy.e,_qE=B(_oG(_oA,_qp));if(!_qE._){var _qF=B(_q6(_hy,_nD,_nD,_qz,_qA,_qB,_qC,_qD,_qE.a,_qE.b,_qE.c,_qE.d,_qE.e));if(!_qF._){return new F(function(){return _qq(_qF.a,_qF.b,_qF.c,_qF.d,_qF.e,_qF);});}else{return E(_qo);}}else{return new F(function(){return _qq(_qz,_qA,_qB,_qC,_qD,_qy);});}}else{var _qG=B(_oG(_oA,_qp));if(!_qG._){return new F(function(){return _qq(_qG.a,_qG.b,_qG.c,_qG.d,_qG.e,_qG);});}else{return E(_qo);}}},_qH=function(_qI,_qJ){while(1){var _qK=E(_qI);if(!_qK._){return (E(_qJ)._==0)?true:false;}else{var _qL=E(_qJ);if(!_qL._){return false;}else{if(E(_qK.a)!=E(_qL.a)){return false;}else{_qI=_qK.b;_qJ=_qL.b;continue;}}}}},_qM=new T2(1,_bQ,_x),_qN=new T2(1,_bT,_qM),_qO=new T2(1,_bW,_qN),_qP=new T2(1,_x,_x),_qQ=function(_qR,_qS){var _qT=function(_qU,_qV){var _qW=E(_qU);if(!_qW._){return E(_qV);}else{var _qX=_qW.a,_qY=E(_qV);if(!_qY._){return E(_qW);}else{var _qZ=_qY.a;return (B(A2(_qR,_qX,_qZ))==2)?new T2(1,_qZ,new T(function(){return B(_qT(_qW,_qY.b));})):new T2(1,_qX,new T(function(){return B(_qT(_qW.b,_qY));}));}}},_r0=function(_r1){var _r2=E(_r1);if(!_r2._){return __Z;}else{var _r3=E(_r2.b);return (_r3._==0)?E(_r2):new T2(1,new T(function(){return B(_qT(_r2.a,_r3.a));}),new T(function(){return B(_r0(_r3.b));}));}},_r4=new T(function(){return B(_r5(B(_r0(_x))));}),_r5=function(_r6){while(1){var _r7=E(_r6);if(!_r7._){return E(_r4);}else{if(!E(_r7.b)._){return E(_r7.a);}else{_r6=B(_r0(_r7));continue;}}}},_r8=new T(function(){return B(_r9(_x));}),_ra=function(_rb,_rc,_rd){while(1){var _re=B((function(_rf,_rg,_rh){var _ri=E(_rh);if(!_ri._){return new T2(1,new T2(1,_rf,_rg),_r8);}else{var _rj=_ri.a;if(B(A2(_qR,_rf,_rj))==2){var _rk=new T2(1,_rf,_rg);_rb=_rj;_rc=_rk;_rd=_ri.b;return __continue;}else{return new T2(1,new T2(1,_rf,_rg),new T(function(){return B(_r9(_ri));}));}}})(_rb,_rc,_rd));if(_re!=__continue){return _re;}}},_rl=function(_rm,_rn,_ro){while(1){var _rp=B((function(_rq,_rr,_rs){var _rt=E(_rs);if(!_rt._){return new T2(1,new T(function(){return B(A1(_rr,new T2(1,_rq,_x)));}),_r8);}else{var _ru=_rt.a,_rv=_rt.b;switch(B(A2(_qR,_rq,_ru))){case 0:_rm=_ru;_rn=function(_rw){return new F(function(){return A1(_rr,new T2(1,_rq,_rw));});};_ro=_rv;return __continue;case 1:_rm=_ru;_rn=function(_rx){return new F(function(){return A1(_rr,new T2(1,_rq,_rx));});};_ro=_rv;return __continue;default:return new T2(1,new T(function(){return B(A1(_rr,new T2(1,_rq,_x)));}),new T(function(){return B(_r9(_rt));}));}}})(_rm,_rn,_ro));if(_rp!=__continue){return _rp;}}},_r9=function(_ry){var _rz=E(_ry);if(!_rz._){return E(_qP);}else{var _rA=_rz.a,_rB=E(_rz.b);if(!_rB._){return new T2(1,_rz,_x);}else{var _rC=_rB.a,_rD=_rB.b;if(B(A2(_qR,_rA,_rC))==2){return new F(function(){return _ra(_rC,new T2(1,_rA,_x),_rD);});}else{return new F(function(){return _rl(_rC,function(_rE){return new T2(1,_rA,_rE);},_rD);});}}}};return new F(function(){return _r5(B(_r9(_qS)));});},_rF=function(_rG,_rH,_rI,_rJ,_rK){if(!B(_qH(B(_qQ(_gZ,B(_4j(function(_rL){var _rM=B(A1(_rL,_rJ))-B(A1(_rL,_rI))|0;return (_rM<0)? -_rM:_rM;},_qO)))),_rG))){return __Z;}else{var _rN=E(_rH);if(!_rN._){return __Z;}else{var _rO=_rN.a,_rP=new T(function(){var _rQ=E(_rI),_rR=E(_rJ),_rS=new T(function(){return E(E(_rO).a);}),_rT=new T(function(){return E(E(_rO).b);});return B(_a2(_rQ.a,_rQ.b,_rQ.c,new T5(0,_rS,_rT,_cz,new T1(1,_rR),new T(function(){return E(E(_rO).e);})),B(_a2(_rR.a,_rR.b,_rR.c,new T5(0,_rS,_rT,_cz,_2s,new T1(1,_rQ)),_rK))));});return new T1(1,_rP);}}},_rU=function(_rV){return (E(_rV)==0)?1:0;},_rW=1,_rX=new T1(1,_rW),_rY=2,_rZ=new T2(1,_rY,_x),_s0=new T2(1,_rW,_rZ),_s1=0,_s2=new T2(1,_s1,_s0),_s3=new T1(0,_cz),_s4=function(_s5,_s6,_s7,_s8,_s9){var _sa=E(_s8);if(!_sa._){return __Z;}else{var _sb=E(_s5),_sc=_sb.a,_sd=_sb.b,_se=_sb.c,_sf=B(_fg(_sc,_sd,_se,_s9));if(!_sf._){var _sg=false;}else{var _sg=E(E(_sf.a).c);}var _sh=function(_si){var _sj=E(_sa.a),_sk=B(_fg(_sj.a,_sj.b,_sj.c,_s9));if(!_sk._){return __Z;}else{var _sl=E(_sk.a),_sm=function(_sn){return new T1(1,new T4(0,new T(function(){return E(_s6)+1|0;}),new T(function(){return B(_rU(_s7));}),_2s,new T(function(){return B(_qn(_sn));})));},_so=E(_sl.b);switch(_so._){case 0:var _sp=B(_dj(new T(function(){if(!E(_sg)){return true;}else{return false;}},1),_sg,new T1(1,new T(function(){if(!E(_so.a)){if(!E(_sg)){return E(_rY);}else{return E(_rW);}}else{return E(_rW);}})),new T1(1,new T5(0,_sl.a,_s3,_cy,_2s,_2s)),_sj,_sb,new T(function(){return B(_9c(_sc,_sd,_se,_s9));})));if(!_sp._){return __Z;}else{return new F(function(){return _sm(_sp.a);});}break;case 1:var _sq=B(_dj(_cz,_cy,_2s,_sk,_sj,_sb,new T(function(){return B(_9c(_sc,_sd,_se,_s9));})));if(!_sq._){return __Z;}else{return new F(function(){return _sm(_sq.a);});}break;case 2:var _sr=B(_rF(_s2,_sk,_sj,_sb,new T(function(){return B(_9c(_sc,_sd,_se,_s9));},1)));if(!_sr._){return __Z;}else{return new F(function(){return _sm(_sr.a);});}break;case 3:var _ss=B(_dj(_cy,_cz,_2s,_sk,_sj,_sb,new T(function(){return B(_9c(_sc,_sd,_se,_s9));})));if(!_ss._){return __Z;}else{return new F(function(){return _sm(_ss.a);});}break;case 4:var _st=B(_dj(_cz,_cz,_2s,_sk,_sj,_sb,new T(function(){return B(_9c(_sc,_sd,_se,_s9));})));if(!_st._){return __Z;}else{return new F(function(){return _sm(_st.a);});}break;default:var _su=B(_dj(_cz,_cz,_rX,_sk,_sj,_sb,new T(function(){return B(_9c(_sc,_sd,_se,_s9));})));if(!_su._){return __Z;}else{return new F(function(){return _sm(_su.a);});}}}};if(!E(_sg)){return new F(function(){return _sh(_);});}else{var _sv=B(_eo(_sc,_sd,_se,_s9));if(!_sv._){return new F(function(){return _sh(_);});}else{if(!E(E(_sv.a).a)){if(!E(_s7)){return __Z;}else{return new F(function(){return _sh(_);});}}else{if(!E(_s7)){return new F(function(){return _sh(_);});}else{return __Z;}}}}}},_sw=function(_sx){return E(E(_sx).d);},_sy=function(_sz){return E(E(_sz).b);},_sA=function(_sB){return E(E(_sB).a);},_sC=function(_sD,_sE){return new T4(0,new T(function(){return B(_sA(_sE));}),new T(function(){return B(_sy(_sE));}),new T(function(){var _sF=E(_sE),_sG=_sF.b,_sH=E(_sD),_sI=B(_eo(_sH.a,_sH.b,_sH.c,_sF.d));if(!_sI._){return __Z;}else{if(!E(E(_sI.a).a)){if(!E(_sG)){return new T1(1,_sH);}else{return __Z;}}else{if(!E(_sG)){return __Z;}else{return new T1(1,_sH);}}}}),new T(function(){return B(_sw(_sE));}));},_sJ=function(_){return _0;},_sK=function(_sL,_sM){return E(_sL)!=E(_sM);},_sN=new T2(0,_fA,_sK),_sO=function(_sP,_sQ){var _sR=E(_sP),_sS=E(_sQ);return (_sR>_sS)?E(_sR):E(_sS);},_sT=function(_sU,_sV){var _sW=E(_sU),_sX=E(_sV);return (_sW>_sX)?E(_sX):E(_sW);},_sY={_:0,a:_sN,b:_gZ,c:_fQ,d:_g7,e:_go,f:_gF,g:_sO,h:_sT},_sZ=function(_t0){return E(E(_t0).a);},_t1=function(_t2){return E(E(_t2).a);},_t3=function(_t4){return E(E(_t4).a);},_t5=109,_t6=100,_t7=99,_t8=108,_t9=120,_ta=118,_tb=105,_tc=function(_td){if(_td<1000){if(_td<900){if(_td<500){if(_td<400){if(_td<100){if(_td<90){if(_td<50){if(_td<40){if(_td<10){if(_td<9){if(_td<5){if(_td<4){return (_td<1)?__Z:new T2(1,_tb,new T(function(){return B(_tc(_td-1|0));}));}else{return new F(function(){return unAppCStr("iv",new T(function(){return B(_tc(_td-4|0));}));});}}else{return new T2(1,_ta,new T(function(){return B(_tc(_td-5|0));}));}}else{return new F(function(){return unAppCStr("ix",new T(function(){return B(_tc(_td-9|0));}));});}}else{return new T2(1,_t9,new T(function(){return B(_tc(_td-10|0));}));}}else{return new F(function(){return unAppCStr("xl",new T(function(){return B(_tc(_td-40|0));}));});}}else{return new T2(1,_t8,new T(function(){return B(_tc(_td-50|0));}));}}else{return new F(function(){return unAppCStr("xc",new T(function(){return B(_tc(_td-90|0));}));});}}else{return new T2(1,_t7,new T(function(){return B(_tc(_td-100|0));}));}}else{return new F(function(){return unAppCStr("cd",new T(function(){return B(_tc(_td-400|0));}));});}}else{return new T2(1,_t6,new T(function(){return B(_tc(_td-500|0));}));}}else{return new F(function(){return unAppCStr("cm",new T(function(){return B(_tc(_td-900|0));}));});}}else{return new T2(1,_t5,new T(function(){return B(_tc(_td-1000|0));}));}},_te=new T(function(){return B(unCStr("+"));}),_tf=new T(function(){return B(unCStr("+ - "));}),_tg=new T(function(){return B(_5(_tf,_te));}),_th=function(_ti){var _tj=E(_ti);if(_tj==1){return E(_tg);}else{return new F(function(){return _5(_tf,new T(function(){return B(_th(_tj-1|0));},1));});}},_tk=function(_tl,_tm){return new T2(1,_tl,_tm);},_tn=function(_to){return E(E(_to).c);},_tp=function(_tq){return E(E(_tq).c);},_tr=function(_ts){return E(E(_ts).b);},_tt=function(_tu){return new T1(2,_tu);},_tv=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_tw=35,_tx=87,_ty=new T(function(){return B(unCStr("   "));}),_tz=42,_tA=32,_tB=75,_tC=81,_tD=78,_tE=82,_tF=80,_tG=66,_tH=function(_tI){var _tJ=E(_tI);if(!_tJ._){return E(_ty);}else{var _tK=E(_tJ.a);return new T2(1,new T(function(){if(!E(_tK.a)){return E(_tx);}else{return E(_tG);}}),new T2(1,new T(function(){switch(E(_tK.b)._){case 0:return E(_tF);break;case 1:return E(_tE);break;case 2:return E(_tD);break;case 3:return E(_tG);break;case 4:return E(_tC);break;default:return E(_tB);}}),new T2(1,new T(function(){if(!E(_tK.d)._){return E(_tA);}else{if(!E(_tK.c)){return E(_tz);}else{return E(_tw);}}}),_x)));}},_tL=function(_tM){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_f(9,_tM,_x));}))));});},_tN=function(_tO){return E(E(_tO).a);},_tP=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_tQ=function(_tR){return E(E(_tR).b);},_tS=new T(function(){return B(unCStr("selected"));}),_tT=3,_tU=function(_tV){return E(E(_tV).g);},_tW=new T(function(){return B(unCStr("maximum"));}),_tX=new T(function(){return B(_bE(_tW));}),_tY=function(_tZ,_u0){var _u1=E(_u0);if(!_u1._){return E(_tX);}else{var _u2=new T(function(){return B(_tU(_tZ));}),_u3=function(_u4,_u5){while(1){var _u6=E(_u4);if(!_u6._){return E(_u5);}else{var _u7=B(A2(_u2,E(_u5),_u6.a));_u4=_u6.b;_u5=_u7;continue;}}};return new F(function(){return _u3(_u1.b,_u1.a);});}},_u8=new T(function(){return B(_tY(_sY,_x));}),_u9=8,_ua=new T(function(){return B(unCStr("span"));}),_ub=new T(function(){return toJSStr(E(_ua));}),_uc=new T(function(){return B(unCStr("|"));}),_ud=new T(function(){return toJSStr(E(_uc));}),_ue=new T(function(){return B(unCStr("id"));}),_uf=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_ug=function(_uh,_ui){var _uj=function(_){return new F(function(){return __app1(E(_uf),E(_ui));});};return new F(function(){return A2(_tQ,_uh,_uj);});},_uk=new T(function(){return B(unCStr("br"));}),_ul=new T(function(){return toJSStr(E(_uk));}),_um=function(_un){return new F(function(){return A3(_tN,B(_sZ(B(_t1(B(_t3(_un)))))),_tt,new T(function(){return B(_ug(_un,_ul));}));});},_uo=new T(function(){return eval("(function(s){return document.createTextNode(s);})");}),_up=function(_uq,_ur){var _us=function(_){return new F(function(){return __app1(E(_uo),E(_ur));});};return new F(function(){return A2(_tQ,_uq,_us);});},_ut=function(_uu){return E(E(_uu).d);},_uv=32,_uw=new T2(1,_uv,_x),_ux=function(_uy){var _uz=E(_uy);return (_uz==1)?E(_uw):new T2(1,_uv,new T(function(){return B(_ux(_uz-1|0));}));},_uA=function(_uB,_uC){var _uD=new T(function(){return B(_up(_uB,new T(function(){var _uE=E(_uC);if(0>=_uE){return toJSStr(_x);}else{return toJSStr(B(_ux(_uE)));}},1)));});return new F(function(){return A3(_tN,B(_sZ(B(_t1(B(_t3(_uB)))))),_tt,_uD);});},_uF=new T(function(){return B(unCStr("n"));}),_uG=function(_uH,_uI,_uJ,_uK,_uL,_uM){var _uN=function(_uO){var _uP=new T(function(){switch(E(_uJ)){case 0:return E(E(_uM).a)+1|0;break;case 1:return E(_u9);break;default:return E(_u9);}}),_uQ=new T(function(){var _uR=E(_uP);if(0>=_uR){return toJSStr(E(_te));}else{return toJSStr(B(_th(_uR)));}}),_uS=new T(function(){var _uT=function(_uU){switch(E(_uK)){case 0:var _uV=E(_uU);if(!_uV){return new F(function(){return _by(_uF,0);});}else{return new F(function(){return _by(B(_tc(_uV)),0);});}break;case 1:return 1;default:return 1;}};switch(E(_uK)){case 0:var _uW=E(E(_uM).a);if(0<=_uW){var _uX=function(_uY){return new T2(1,new T(function(){return B(_uT(_uY));}),new T(function(){if(_uY!=_uW){return B(_uX(_uY+1|0));}else{return __Z;}}));},_uZ=E(B(_tY(_sY,B(_uX(0)))));if(_uZ==2147483647){return E(_46);}else{return _uZ+1|0;}}else{var _v0=E(_u8);if(_v0==2147483647){return E(_46);}else{return _v0+1|0;}}break;case 1:var _v1=function(_v2){return new T2(1,new T(function(){return B(_uT(_v2));}),new T(function(){var _v3=E(_v2);if(_v3==7){return __Z;}else{return B(_v1(_v3+1|0));}}));},_v4=E(B(_tY(_sY,B(_v1(0)))));if(_v4==2147483647){return E(_46);}else{return _v4+1|0;}break;default:var _v5=function(_v6){return new T2(1,new T(function(){return B(_uT(_v6));}),new T(function(){var _v7=E(_v6);if(_v7==7){return __Z;}else{return B(_v5(_v7+1|0));}}));},_v8=E(B(_tY(_sY,B(_v5(0)))));if(_v8==2147483647){return E(_46);}else{return _v8+1|0;}}}),_v9=function(_va){var _vb=new T(function(){return B(A3(_tN,B(_sZ(B(_t1(B(_t3(_va)))))),_tt,new T(function(){return B(_up(_va,_uQ));})));});return new T2(1,new T(function(){return B(_uA(_va,_uS));}),new T2(1,_vb,new T2(1,new T(function(){return B(_um(_va));}),_x)));},_vc=B(_t3(_uH)),_vd=new T(function(){var _ve=function(_vf){if(0<=_vf){var _vg=new T(function(){return B(_ug(_uH,_ub));}),_vh=new T(function(){return B(_ut(_vc));}),_vi=new T(function(){return B(_uA(_uH,_tT));}),_vj=function(_vk){var _vl=new T(function(){var _vm=new T(function(){var _vn=new T(function(){switch(E(_uJ)){case 0:var _vo=E(_vk);if(!_vo){return toJSStr(E(_uF));}else{return toJSStr(B(_tc(_vo)));}break;case 1:return toJSStr(new T2(1,new T(function(){var _vp=97+_vk|0;if(_vp>>>0>1114111){return B(_tL(_vp));}else{return _vp;}}),_x));break;default:return toJSStr(new T2(1,new T(function(){var _vq=49+_vk|0;if(_vq>>>0>1114111){return B(_tL(_vq));}else{return _vq;}}),_x));}},1);return B(_up(_uH,_vn));}),_vr=function(_vs){var _vt=new T(function(){var _vu=function(_vv){var _vw=function(_){var _vx=__app2(E(_tv),E(_vv),E(_vs));return new F(function(){return _sJ(_);});};return new F(function(){return A2(_tQ,_uH,_vw);});};return B(A3(_tr,_vc,_vm,_vu));});return new F(function(){return A3(_tp,_vc,_vt,new T(function(){return B(A1(_vh,new T3(1,_uJ,_vk,_vs)));}));});};return B(A3(_tr,_vc,_vg,_vr));});return new T2(1,_vl,new T2(1,_vi,new T(function(){if(_vk!=_vf){return B(_vj(_vk+1|0));}else{return __Z;}})));};return new F(function(){return _vj(0);});}else{return __Z;}};switch(E(_uJ)){case 0:return B(_ve(E(E(_uM).a)));break;case 1:return B(_ve(7));break;default:return B(_ve(7));}}),_vy=new T(function(){return B(_uA(_uH,new T(function(){return E(_uS)+2|0;},1)));}),_vz=B(_5(new T2(1,_vy,_vd),new T2(1,new T(function(){return B(_um(_uH));}),new T(function(){return B(_v9(_uH));})))),_vA=new T(function(){return B(_t1(_vc));}),_vB=new T(function(){return B(_sZ(_vA));}),_vC=new T(function(){return B(A2(_ut,_vc,_x));}),_vD=function(_vE){var _vF=E(_vE);if(!_vF._){return E(_vC);}else{return new F(function(){return A3(_tn,_vA,new T(function(){return B(A3(_tN,_vB,_tk,_vF.a));}),new T(function(){return B(_vD(_vF.b));}));});}};if(0<=_uO){var _vG=new T(function(){return B(A3(_tN,B(_sZ(B(_t1(B(_t3(_uH)))))),_tt,new T(function(){return B(_up(_uH,_ud));})));}),_vH=new T(function(){return B(_ut(_vc));}),_vI=new T(function(){return B(_ug(_uH,_ub));}),_vJ=new T(function(){return B(A2(_ut,_vc,_0));}),_vK=function(_vL,_vM){var _vN=new T(function(){var _vO=new T(function(){return B(_up(_uH,new T(function(){var _vP=E(_vL);return toJSStr(B(_tH(B(_eo(_vP.a,_vP.b,_vP.c,E(_uM).d)))));},1)));}),_vQ=new T(function(){var _vR=E(E(_uM).c);if(!_vR._){return false;}else{var _vS=E(_vL),_vT=E(_vR.a);if(E(_vS.a)!=E(_vT.a)){return false;}else{if(E(_vS.b)!=E(_vT.b)){return false;}else{return E(_vS.c)==E(_vT.c);}}}}),_vU=function(_vV){var _vW=new T(function(){var _vX=new T(function(){if(!E(_vQ)){return E(_vJ);}else{var _vY=function(_){var _vZ=__app3(E(_tP),E(_vV),toJSStr(E(_ue)),toJSStr(E(_tS)));return new F(function(){return _sJ(_);});};return B(A2(_tQ,_uH,_vY));}});return B(A3(_tp,_vc,_vX,new T(function(){return B(A1(_vH,new T2(0,_vL,_vV)));})));}),_w0=new T(function(){var _w1=function(_w2){var _w3=function(_){var _w4=__app2(E(_tv),E(_w2),E(_vV));return new F(function(){return _sJ(_);});};return new F(function(){return A2(_tQ,_uH,_w3);});};return B(A3(_tr,_vc,_vO,_w1));});return new F(function(){return A3(_tp,_vc,_w0,_vW);});};return B(A3(_tr,_vc,_vI,_vU));});return new T2(1,_vG,new T2(1,_vN,_vM));},_w5=new T2(1,_vG,new T2(1,new T(function(){return B(_um(_uH));}),_x)),_w6=function(_w7,_w8){var _w9=E(_w7);if(!_w9._){return E(_w5);}else{var _wa=_w9.a,_wb=E(_w8);if(_wb==1){return new F(function(){return _vK(_wa,_w5);});}else{return new F(function(){return _vK(_wa,new T(function(){return B(_w6(_w9.b,_wb-1|0));}));});}}},_wc=new T(function(){return B(_v9(_uH));}),_wd=function(_we,_wf){while(1){var _wg=B((function(_wh,_wi){var _wj=new T(function(){var _wk=new T(function(){return B(_uA(_uH,new T(function(){var _wl=E(_uS);switch(E(_uK)){case 0:var _wm=E(_wh);if(!_wm){return _wl-B(_by(_uF,0))|0;}else{return _wl-B(_by(B(_tc(_wm)),0))|0;}break;case 1:return _wl-1|0;break;default:return _wl-1|0;}},1)));}),_wn=new T(function(){var _wo=new T(function(){var _wp=new T(function(){switch(E(_uK)){case 0:var _wq=E(_wh);if(!_wq){return toJSStr(E(_uF));}else{return toJSStr(B(_tc(_wq)));}break;case 1:return toJSStr(new T2(1,new T(function(){var _wr=97+_wh|0;if(_wr>>>0>1114111){return B(_tL(_wr));}else{return _wr;}}),_x));break;default:return toJSStr(new T2(1,new T(function(){var _ws=49+_wh|0;if(_ws>>>0>1114111){return B(_tL(_ws));}else{return _ws;}}),_x));}},1);return B(_up(_uH,_wp));}),_wt=function(_wu){var _wv=new T(function(){var _ww=function(_wx){var _wy=function(_){var _wz=__app2(E(_tv),E(_wx),E(_wu));return new F(function(){return _sJ(_);});};return new F(function(){return A2(_tQ,_uH,_wy);});};return B(A3(_tr,_vc,_wo,_ww));});return new F(function(){return A3(_tp,_vc,_wv,new T(function(){return B(A1(_vH,new T3(1,_uK,_wh,_wu)));}));});};return B(A3(_tr,_vc,_vI,_wt));});return B(_5(new T2(1,_wn,new T2(1,_wk,new T(function(){var _wA=E(_uP);if(0>=_wA){return E(_w5);}else{return B(_w6(B(_bv(_uL,_wh)),_wA));}}))),_wc));},1),_wB=B(_5(_wi,_wj));if(_wh!=_uO){var _wC=_wh+1|0;_we=_wC;_wf=_wB;return __continue;}else{return E(_wB);}})(_we,_wf));if(_wg!=__continue){return _wg;}}};return new F(function(){return _vD(B(_wd(0,_vz)));});}else{return new F(function(){return _vD(_vz);});}};switch(E(_uK)){case 0:return new F(function(){return _uN(E(E(_uM).a));});break;case 1:return new F(function(){return _uN(7);});break;default:return new F(function(){return _uN(7);});}},_wD=0,_wE=function(_wF,_wG,_){while(1){var _wH=B((function(_wI,_wJ,_){var _wK=E(_wI);if(!_wK._){return new F(function(){return A1(_wJ,_);});}else{_wF=_wK.b;_wG=function(_){return new F(function(){return _3H(_wJ,_wK.a,_);});};return __continue;}})(_wF,_wG,_));if(_wH!=__continue){return _wH;}}},_wL=new T(function(){return B(unCStr("foldl1"));}),_wM=new T(function(){return B(_bE(_wL));}),_wN=function(_wO){var _wP=E(_wO);switch(_wP._){case 0:return E(_wP.b);case 1:return E(_wP.c);default:return E(_wP.a);}},_wQ=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_wR=function(_wS,_wT){var _wU=function(_){var _wV=__app1(E(_wQ),E(_wT)),_wW=__eq(_wV,E(_2P));return (E(_wW)==0)?new T1(1,_wV):_2s;};return new F(function(){return A2(_tQ,_wS,_wU);});},_wX="board",_wY=new T(function(){return B(_wR(_43,_wX));}),_wZ=new T(function(){return B(unCStr("Pattern match failure in do expression at Web.hs:26:9-21"));}),_x0=new T6(0,_2s,_2t,_x,_wZ,_2s,_2s),_x1=new T(function(){return B(_2q(_x0));}),_x2=function(_x3){return E(E(_x3).a);},_x4=function(_x5){return E(E(_x5).a);},_x6=function(_x7){return E(E(_x7).b);},_x8=function(_x9){return E(E(_x9).a);},_xa=function(_){return new F(function(){return nMV(_2s);});},_xb=new T(function(){return B(_2L(_xa));}),_xc=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_xd=function(_xe){return E(E(_xe).b);},_xf=function(_xg,_xh,_xi,_xj,_xk,_xl){var _xm=B(_x2(_xg)),_xn=B(_t3(_xm)),_xo=new T(function(){return B(_tQ(_xm));}),_xp=new T(function(){return B(_ut(_xn));}),_xq=new T(function(){return B(A2(_x4,_xh,_xj));}),_xr=new T(function(){return B(A2(_x8,_xi,_xk));}),_xs=function(_xt){return new F(function(){return A1(_xp,new T3(0,_xr,_xq,_xt));});},_xu=function(_xv){var _xw=new T(function(){var _xx=new T(function(){var _xy=__createJSFunc(2,function(_xz,_){var _xA=B(A2(E(_xv),_xz,_));return _2P;}),_xB=_xy;return function(_){return new F(function(){return __app3(E(_xc),E(_xq),E(_xr),_xB);});};});return B(A1(_xo,_xx));});return new F(function(){return A3(_tr,_xn,_xw,_xs);});},_xC=new T(function(){var _xD=new T(function(){return B(_tQ(_xm));}),_xE=function(_xF){var _xG=new T(function(){return B(A1(_xD,function(_){var _=wMV(E(_xb),new T1(1,_xF));return new F(function(){return A(_x6,[_xi,_xk,_xF,_]);});}));});return new F(function(){return A3(_tr,_xn,_xG,_xl);});};return B(A2(_xd,_xg,_xE));});return new F(function(){return A3(_tr,_xn,_xC,_xu);});},_xH=new T(function(){return eval("(function(e,ch){while(e.firstChild) {e.removeChild(e.firstChild);}for(var i in ch) {e.appendChild(ch[i]);}})");}),_xI=function(_xJ){return E(_xJ);},_xK=function(_xL,_xM,_xN,_xO,_xP){var _xQ=new T(function(){var _xR=__lst2arr(B(_4j(_xI,B(_4j(new T(function(){return B(_x4(_xM));}),_xP))))),_xS=_xR;return function(_){var _xT=__app2(E(_xH),B(A2(_x4,_xL,_xO)),_xS);return new F(function(){return _sJ(_);});};});return new F(function(){return A2(_tQ,_xN,_xQ);});},_xU=function(_xV,_xW,_xX,_xY,_xZ,_){var _y0=B(A1(_wY,_)),_y1=E(_y0);if(!_y1._){return new F(function(){return die(_x1);});}else{var _y2=B(A(_4s,[_xV,_xW,_xX,_xY,_xZ])),_y3=B(A(_uG,[_43,_y2.a,_y2.b,_y2.c,_y2.d,_y2.e,_])),_y4=new T(function(){return E(E(_xZ).a);}),_y5=new T(function(){return E(E(_xZ).b);}),_y6=new T(function(){return E(E(_xZ).d);}),_y7=function(_y8,_){return new F(function(){return _xU(_xV,_xW,_xX,_xY,new T4(0,_y4,_y5,_2s,_y6),_);});},_y9=function(_ya){while(1){var _yb=B((function(_yc){var _yd=E(_yc);if(!_yd._){return __Z;}else{var _ye=_yd.b,_yf=E(_yd.a);if(_yf._==2){_ya=_ye;return __continue;}else{var _yg=new T(function(){var _yh=E(_yf);if(!_yh._){var _yi=_yh.a,_yj=_yh.b,_yk=E(_xZ),_yl=_yk.a,_ym=E(_yk.c);if(!_ym._){var _yn=new T(function(){var _yo=B(_sC(_yi,_yk));return new T4(0,_yo.a,_yo.b,_yo.c,_yo.d);});return B(_xf(_44,_3l,_3g,_yj,_wD,function(_yp,_){return new F(function(){return _xU(_xV,_xW,_xX,_xY,_yn,_);});}));}else{var _yq=E(_ym.a),_yr=E(_yi),_ys=function(_yt){var _yu=new T(function(){return B(_s4(_yr,_yl,_yk.b,_ym,_yk.d));}),_yv=new T(function(){if(!E(_yu)._){return E(_xW);}else{switch(E(_xV)){case 0:var _yw=E(_xW);if(_yw!=E(_yl)){return E(_yw);}else{var _yx=E(_yw);if(_yx==2147483647){return E(_46);}else{return _yx+1|0;}}break;case 1:return E(_xW);break;default:return E(_xW);}}}),_yy=new T(function(){var _yz=E(_yu);if(!_yz._){return E(_yk);}else{return E(_yz.a);}});return new F(function(){return _xf(_44,_3l,_3g,_yj,_wD,function(_yA,_){return new F(function(){return _xU(_xV,_yv,_xX,_xY,_yy,_);});});});};if(E(_yq.a)!=E(_yr.a)){return B(_ys(_));}else{if(E(_yq.b)!=E(_yr.b)){return B(_ys(_));}else{if(E(_yq.c)!=E(_yr.c)){return B(_ys(_));}else{return B(_xf(_44,_3l,_3g,_yj,_wD,_y7));}}}}}else{var _yB=_yh.a,_yC=new T(function(){switch(E(_xX)){case 0:if(!E(_yB)){return E(_xV);}else{return 0;}break;case 1:if(E(_yB)==1){return E(_xV);}else{return 1;}break;default:if(E(_yB)==2){return E(_xV);}else{return 2;}}}),_yD=new T(function(){switch(E(_xY)){case 0:if(!E(_yB)){return E(_xV);}else{return 0;}break;case 1:if(E(_yB)==1){return E(_xV);}else{return 1;}break;default:if(E(_yB)==2){return E(_xV);}else{return 2;}}});return B(_xf(_44,_3l,_3g,_yh.c,_wD,function(_yE,_){return new F(function(){return _xU(_yB,_yh.b,_yC,_yD,_xZ,_);});}));}});return new T2(1,_yg,new T(function(){return B(_y9(_ye));}));}}})(_ya));if(_yb!=__continue){return _yb;}}},_yF=B(_y9(_y3));if(!_yF._){return E(_wM);}else{var _yG=B(_wE(_yF.b,_yF.a,_)),_yH=B(A(_xK,[_3l,_3l,_43,_y1.a,new T(function(){return B(_4j(_wN,_y3));},1),_]));return _0;}}},_yI=0,_yJ=1,_yK=2,_yL=function(_yM,_yN,_yO,_yP,_){var _yQ=B(A1(_wY,_)),_yR=E(_yQ);if(!_yR._){return new F(function(){return die(_x1);});}else{var _yS=B(A(_4s,[_yI,_yM,_yJ,_yK,new T4(0,_yN,_yO,_2s,_yP)])),_yT=B(A(_uG,[_43,_yS.a,_yS.b,_yS.c,_yS.d,_yS.e,_])),_yU=function(_yV){while(1){var _yW=B((function(_yX){var _yY=E(_yX);if(!_yY._){return __Z;}else{var _yZ=_yY.b,_z0=E(_yY.a);if(_z0._==2){_yV=_yZ;return __continue;}else{var _z1=new T(function(){var _z2=E(_z0);if(!_z2._){var _z3=new T(function(){var _z4=B(_sC(_z2.a,new T4(0,_yN,_yO,_2s,_yP)));return new T4(0,_z4.a,_z4.b,_z4.c,_z4.d);});return B(_xf(_44,_3l,_3g,_z2.b,_wD,function(_z5,_){return new F(function(){return _xU(_yI,_yM,_yJ,_yK,_z3,_);});}));}else{var _z6=_z2.a,_z7=new T(function(){if(E(_z6)==1){return 0;}else{return 1;}}),_z8=new T(function(){if(E(_z6)==2){return 0;}else{return 2;}});return B(_xf(_44,_3l,_3g,_z2.c,_wD,function(_z9,_){return new F(function(){return _xU(_z6,_z2.b,_z7,_z8,new T4(0,_yN,_yO,_2s,_yP),_);});}));}});return new T2(1,_z1,new T(function(){return B(_yU(_yZ));}));}}})(_yV));if(_yW!=__continue){return _yW;}}},_za=B(_yU(_yT));if(!_za._){return E(_wM);}else{var _zb=B(_wE(_za.b,_za.a,_)),_zc=B(A(_xK,[_3l,_3l,_43,_yR.a,new T(function(){return B(_4j(_wN,_yT));},1),_]));return _0;}}},_zd=new T0(3),_ze=new T0(2),_zf=new T0(4),_zg=3,_zh=2,_zi=1,_zj=6,_zk=0,_zl=7,_zm=5,_zn=4,_zo=new T1(5,_cy),_zp=new T1(1,_cy),_zq=function(_zr,_zs){return new T2(0,new T2(0,new T3(0,_zk,_zk,_zs),new T5(0,_zr,_zp,_cz,_2s,_2s)),new T2(1,new T2(0,new T3(0,_zk,_zi,_zs),new T5(0,_zr,_ze,_cz,_2s,_2s)),new T2(1,new T2(0,new T3(0,_zk,_zh,_zs),new T5(0,_zr,_zd,_cz,_2s,_2s)),new T2(1,new T2(0,new T3(0,_zk,_zg,_zs),new T5(0,_zr,_zf,_cz,_2s,_2s)),new T2(1,new T2(0,new T3(0,_zk,_zn,_zs),new T5(0,_zr,_zo,_cz,_2s,_2s)),new T2(1,new T2(0,new T3(0,_zk,_zm,_zs),new T5(0,_zr,_zd,_cz,_2s,_2s)),new T2(1,new T2(0,new T3(0,_zk,_zj,_zs),new T5(0,_zr,_ze,_cz,_2s,_2s)),new T2(1,new T2(0,new T3(0,_zk,_zl,_zs),new T5(0,_zr,_zp,_cz,_2s,_2s)),_x))))))));},_zt=new T(function(){return B(_4d(0,7));}),_zu=new T1(0,_cy),_zv=function(_zw,_zx){var _zy=function(_zz,_zA){var _zB=E(_zz);if(!_zB._){return __Z;}else{var _zC=E(_zA);return (_zC._==0)?__Z:new T2(1,new T2(0,new T3(0,_zk,_zB.a,_zx),_zC.a),new T(function(){return B(_zy(_zB.b,_zC.b));}));}},_zD=new T(function(){var _zE=new T(function(){return new T2(1,new T5(0,_zw,_zu,_cz,_2s,_2s),_zE);});return E(_zE);},1);return new F(function(){return _zy(_zt,_zD);});},_zF=new T(function(){return B(_zv(_1,_zi));}),_zG=1,_zH=new T(function(){return B(_zv(_zG,_zj));}),_zI=new T(function(){var _zJ=B(_zq(_zG,_zl));return B(_5(new T2(1,_zJ.a,_zJ.b),_zH));}),_zK=new T(function(){return B(_5(_zF,_zI));}),_zL=new T(function(){var _zM=B(_zq(_1,_zk));return B(_na(B(_5(new T2(1,_zM.a,_zM.b),_zK))));}),_zN=function(_){var _zO=B(_yL(0,0,_1,_zL,_));return _0;},_zP=function(_){return new F(function(){return _zN(_);});};
var hasteMain = function() {B(A(_zP, [0]));};window.onload = hasteMain;