//----------------------------------------------------------------------------
// DynASM ARM64 module.
//
// Copyright (C) 2005-2020 Mike Pall. All rights reserved.
// See dynasm.lua for full copyright notice.
//----------------------------------------------------------------------------

// Module information:
var _info = {
  arch =	"arm",
  description =	"DynASM ARM64 module",
  version =	"1.4.0",
  vernum =	 10400,
  release =	"2015-10-18",
  author =	"Mike Pall",
  license =	"MIT",
};

// Exported glue functions for the arch-specific module.
var _M = { _info = _info };

// Cache library functions.
var type, tonumber, pairs, ipairs = type, tonumber, pairs, ipairs;
var assert, setmetatable, rawget = assert, setmetatable, rawget;
var _s = string;
var sub, format, byte, char = _s.sub, _s.format, _s.byte, _s.char;
var match, gmatch, gsub = _s.match, _s.gmatch, _s.gsub;
var concat, sort, insert = table.concat, table.sort, table.insert;
var bit = bit || require("bit");
var band, shl, shr, sar = bit.band, bit.lshift, bit.rshift, bit.arshift;
var ror, tohex = bit.ror, bit.tohex;

// Inherited tables and callbacks.
var g_opt, g_arch;
var wline, werror, wfatal, wwarn;

// Action name list.
// CHECK: Keep this in sync with the C code!
var action_names = {
  "STOP", "SECTION", "ESC", "REL_EXT",
  "ALIGN", "REL_LG", "LABEL_LG",
  "REL_PC", "LABEL_PC", "IMM", "IMM6", "IMM12", "IMM13W", "IMM13X", "IMML",
};

// Maximum number of section buffer positions for dasm_put().
// CHECK: Keep this in sync with the C code!
var maxsecpos = 25; // Keep this low, to avoid excessively long C lines.

// Action name -> action number.
var map_action = {};
for( n,name in ipairs(action_names) ) {
  map_action[name] = n-1;
}

// Action list buffer.
var actlist = {};

// Argument list for next dasm_put(). Start with offset 0 into action list.
var actargs = { 0 };

// Current number of section buffer positions for dasm_put().
var secpos = 1;

//----------------------------------------------------------------------------

// Dump action names and numbers.
var function dumpactions(out) {
  out->write("DynASM encoding engine action codes:\n");
  for( n,name in ipairs(action_names) ) {
    var num = map_action[name];
    out->write(format("  %-10s %02X  %d\n", name, num, num));
  }
  out->write("\n");
}

// Write action list buffer as a huge static C array.
var function writeactions(out, name) {
  var nn = #actlist;
  if( nn == 0 ) { nn = 1; actlist[0] = map_action.STOP; }
  out->write("static const unsigned int ", name, "[", nn, "] = {\n");
  for( i = 1,nn-1 ) {
    assert(out->write("0x", tohex(actlist[i]), ",\n"));
  }
  assert(out->write("0x", tohex(actlist[nn]), "\n};\n\n"));
}

//----------------------------------------------------------------------------

// Add word to action list.
var function wputxw(n) {
  assert(n >= 0 && n <= 0xffffffff && n % 1 == 0, "word out of range");
  actlist[#actlist+1] = n;
}

// Add action to list with optional arg. Advance buffer pos, too.
var function waction(action, val, a, num) {
  var w = assert(map_action[action], "bad action name `"..action.."'");
  wputxw(w * 0x10000 + (val || 0));
  if( a ) { actargs[#actargs+1] = a; }
  if( a || num ) { secpos +=   (num || 1); }
}

// Flush action list (intervening C code or buffer pos overflow).
var function wflush(term) {
  if( #actlist == actargs[1] ) { return; } // Nothing to flush.
  if( ! term ) { waction("STOP"); } // Terminate action list.
  wline(format("dasm_put(Dst, %s);", concat(actargs, ", ")), true);
  actargs = { #actlist }; // Actionlist offset is 1st arg to next dasm_put().
  secpos = 1; // The actionlist offset occupies a buffer position, too.
}

// Put escaped word.
var function wputw(n) {
  if( n <= 0x000fffff ) { waction("ESC"); }
  wputxw(n);
}

// Reserve position for word.
var function wpos() {
  var pos = #actlist+1;
  actlist[pos] = "";
  return pos;
}

// Store word to reserved position.
var function wputpos(pos, n) {
  assert(n >= 0 && n <= 0xffffffff && n % 1 == 0, "word out of range");
  if( n <= 0x000fffff ) {
    insert(actlist, pos+1, n);
    n = map_action.ESC * 0x10000;
  }
  actlist[pos] = n;
}

//----------------------------------------------------------------------------

// Global label name -> global label number. With auto assignment on 1st use.
var next_global = 20;
var map_global = setmetatable({}, { __index = function(t, name) {
  if( ! match(name, "^[%a_][%w_]*$") ) { werror("bad global label"); }
  var n = next_global;
  if( n > 2047 ) { werror("too many global labels"); }
  next_global = n + 1;
  t[name] = n;
  return n;
}});

// Dump global labels.
var function dumpglobals(out, lvl) {
  var t = {};
  for( name, n in pairs(map_global) ) { t[n] = name; }
  out->write("Global labels:\n");
  for( i=20,next_global-1 ) {
    out->write(format("  %s\n", t[i]));
  }
  out->write("\n");
}

// Write global label enum.
var function writeglobals(out, prefix) {
  var t = {};
  for( name, n in pairs(map_global) ) { t[n] = name; }
  out->write("enum {\n");
  for( i=20,next_global-1 ) {
    out->write("  ", prefix, t[i], ",\n");
  }
  out->write("  ", prefix, "_MAX\n};\n");
}

// Write global label names.
var function writeglobalnames(out, name) {
  var t = {};
  for( xname, n in pairs(map_global) ) { t[n] = xname; }
  out->write("static const char *const ", name, "[] = {\n");
  for( i=20,next_global-1 ) {
    out->write("  \"", t[i], "\",\n");
  }
  out->write("  (const char *)0\n};\n");
}

//----------------------------------------------------------------------------

// Extern label name -> extern label number. With auto assignment on 1st use.
var next_extern = 0;
var map_extern_ = {};
var map_extern = setmetatable({}, { __index = function(t, name) {
  // No restrictions on the name for now.
  var n = next_extern;
  if( n > 2047 ) { werror("too many extern labels"); }
  next_extern = n + 1;
  t[name] = n;
  map_extern_[n] = name;
  return n;
}});

// Dump extern labels.
var function dumpexterns(out, lvl) {
  out->write("Extern labels:\n");
  for( i=0,next_extern-1 ) {
    out->write(format("  %s\n", map_extern_[i]));
  }
  out->write("\n");
}

// Write extern label names.
var function writeexternnames(out, name) {
  out->write("static const char *const ", name, "[] = {\n");
  for( i=0,next_extern-1 ) {
    out->write("  \"", map_extern_[i], "\",\n");
  }
  out->write("  (const char *)0\n};\n");
}

//----------------------------------------------------------------------------

// Arch-specific maps.

// Ext. register name -> int. name.
var map_archdef = { xzr = "@x31", wzr = "@w31", lr = "x30", };

// Int. register name -> ext. name.
var map_reg_rev = { ["@x31"] = "xzr", ["@w31"] = "wzr", x30 = "lr", };

var map_type = {};		// Type name -> { ctype, reg }
var ctypenum = 0;		// Type number (for Dt... macros).

// Reverse defines for registers.
function _M.revdef(s) {
  return map_reg_rev[s] || s;
}

var map_shift = { lsl = 0, lsr = 1, asr = 2, };

var map_extend = {
  uxtb = 0, uxth = 1, uxtw = 2, uxtx = 3,
  sxtb = 4, sxth = 5, sxtw = 6, sxtx = 7,
};

var map_cond = {
  eq = 0, ne = 1, cs = 2, cc = 3, mi = 4, pl = 5, vs = 6, vc = 7,
  hi = 8, ls = 9, ge = 10, lt = 11, gt = 12, le = 13, al = 14,
  hs = 2, lo = 3,
};

//----------------------------------------------------------------------------

var parse_reg_type;

var function parse_reg(expr) {
  if( ! expr ) { werror("expected register name"); }
  var tname, ovreg = match(expr, "^([%w_]+):(@?%l%d+)$");
  var tp = map_type[tname || expr];
  if( tp ) {
    var reg = ovreg || tp.reg;
    if( ! reg ) {
      werror("type `"..(tname || expr).."' needs a register override");
    }
    expr = reg;
  }
  var ok31, rt, r = match(expr, "^(@?)([xwqdshb])([123]?[0-9])$");
  if( r ) {
    r = tonumber(r);
    if( r <= 30 || (r == 31 && ok31 != "" || (rt != "w" && rt != "x")) ) {
      if( ! parse_reg_type ) {
	parse_reg_type = rt;
      } else if( parse_reg_type != rt ) {
	werror("register size mismatch");
      }
      return r, tp;
    }
  }
  werror("bad register name `"..expr.."'");
}

var function parse_reg_base(expr) {
  if( expr == "sp" ) { return 0x3e0; }
  var base, tp = parse_reg(expr);
  if( parse_reg_type != "x" ) { werror("bad register type"); }
  parse_reg_type = false;
  return shl(base, 5), tp;
}

var parse_ctx = {};

var loadenv = setfenv && function(s) {
  var code = loadstring(s, "");
  if( code ) { setfenv(code, parse_ctx); }
  return code;
} || function(s) {
  return load(s, "", null, parse_ctx);
};

// Try to parse simple arithmetic, too, since some basic ops are aliases.
var function parse_number(n) {
  var x = tonumber(n);
  if( x ) { return x; }
  var code = loadenv("return "..n);
  if( code ) {
    var ok, y = pcall(code);
    if( ok ) { return y; }
  }
  return null;
}

var function parse_imm(imm, bits, shift, scale, signed) {
  imm = match(imm, "^#(.*)$");
  if( ! imm ) { werror("expected immediate operand"); }
  var n = parse_number(imm);
  if( n ) {
    var m = sar(n, scale);
    if( shl(m, scale) == n ) {
      if( signed ) {
	var s = sar(m, bits-1);
	if( s == 0 ) { return shl(m, shift);
	} else if( s == -1 ) { return shl(m + shl(1, bits), shift); }
      } else {
	if( sar(m, bits) == 0 ) { return shl(m, shift); }
      }
    }
    werror("out of range immediate `"..imm.."'");
  } else {
    waction("IMM", (signed && 32768 || 0)+scale*1024+bits*32+shift, imm);
    return 0;
  }
}

var function parse_imm12(imm) {
  imm = match(imm, "^#(.*)$");
  if( ! imm ) { werror("expected immediate operand"); }
  var n = parse_number(imm);
  if( n ) {
    if( shr(n, 12) == 0 ) {
      return shl(n, 10);
    } else if( band(n, 0xff000fff) == 0 ) {
      return shr(n, 2) + 0x00400000;
    }
    werror("out of range immediate `"..imm.."'");
  } else {
    waction("IMM12", 0, imm);
    return 0;
  }
}

var function parse_imm13(imm) {
  imm = match(imm, "^#(.*)$");
  if( ! imm ) { werror("expected immediate operand"); }
  var n = parse_number(imm);
  var r64 = parse_reg_type == "x";
  if( n && n % 1 == 0 && n >= 0 && n <= 0xffffffff ) {
    var inv = false;
    if( band(n, 1) == 1 ) { n = bit.bnot(n); inv = true; }
    var t = {};
    for( i=1,32 ) { t[i] = band(n, 1); n = shr(n, 1); }
    var b = table.concat(t);
    b = b..(r64 && (inv && "1" || "0")->rep(32) || b);
    var p0, p1, p0a, p1a = b->match("^(0+)(1+)(0*)(1*)");
    if( p0 ) {
      var w = p1a == "" && (r64 && 64 || 32) || #p1+#p0a;
      if( band(w, w-1) == 0 && b == b->sub(1, w)->rep(64/w) ) {
	var s = band(-2*w, 0x3f) - 1;
	if( w == 64 ) { s +=   0x1000; }
	if( inv ) {
	  return shl(w-#p1-#p0, 16) + shl(s+w-#p1, 10);
	} else {
	  return shl(w-#p0, 16) + shl(s+#p1, 10);
	}
      }
    }
    werror("out of range immediate `"..imm.."'");
  } else if( r64 ) {
    waction("IMM13X", 0, format("(unsigned int)(%s)", imm));
    actargs[#actargs+1] = format("(unsigned int)((unsigned long long)(%s)>>32)", imm);
    return 0;
  } else {
    waction("IMM13W", 0, imm);
    return 0;
  }
}

var function parse_imm6(imm) {
  imm = match(imm, "^#(.*)$");
  if( ! imm ) { werror("expected immediate operand"); }
  var n = parse_number(imm);
  if( n ) {
    if( n >= 0 && n <= 63 ) {
      return shl(band(n, 0x1f), 19) + (n >= 32 && 0x80000000 || 0);
    }
    werror("out of range immediate `"..imm.."'");
  } else {
    waction("IMM6", 0, imm);
    return 0;
  }
}

var function parse_imm_load(imm, scale) {
  var n = parse_number(imm);
  if( n ) {
    var m = sar(n, scale);
    if( shl(m, scale) == n && m >= 0 && m < 0x1000 ) {
      return shl(m, 10) + 0x01000000; // Scaled, unsigned 12 bit offset.
    } else if( n >= -256 && n < 256 ) {
      return shl(band(n, 511), 12); // Unscaled, signed 9 bit offset.
    }
    werror("out of range immediate `"..imm.."'");
  } else {
    waction("IMML", 0, imm);
    return 0;
  }
}

var function parse_fpimm(imm) {
  imm = match(imm, "^#(.*)$");
  if( ! imm ) { werror("expected immediate operand"); }
  var n = parse_number(imm);
  if( n ) {
    var m, e = math.frexp(n);
    var s, e2 = 0, band(e-2, 7);
    if( m < 0 ) { m = -m; s = 0x00100000; }
    m = m*32-16;
    if( m % 1 == 0 && m >= 0 && m <= 15 && sar(shl(e2, 29), 29)+2 == e ) {
      return s + shl(e2, 17) + shl(m, 13);
    }
    werror("out of range immediate `"..imm.."'");
  } else {
    werror("NYI fpimm action");
  }
}

var function parse_shift(expr) {
  var s, s2 = match(expr, "^(%S+)%s*(.*)$");
  s = map_shift[s];
  if( ! s ) { werror("expected shift operand"); }
  return parse_imm(s2, 6, 10, 0, false) + shl(s, 22);
}

var function parse_lslx16(expr) {
  var n = match(expr, "^lsl%s*#(%d+)$");
  n = tonumber(n);
  if( ! n ) { werror("expected shift operand"); }
  if( band(n, parse_reg_type == "x" && 0xffffffcf || 0xffffffef) != 0 ) {
    werror("bad shift amount");
  }
  return shl(n, 17);
}

var function parse_extend(expr) {
  var s, s2 = match(expr, "^(%S+)%s*(.*)$");
  if( s == "lsl" ) {
    s = parse_reg_type == "x" && 3 || 2;
  } else {
    s = map_extend[s];
  }
  if( ! s ) { werror("expected extend operand"); }
  return (s2 == "" && 0 || parse_imm(s2, 3, 10, 0, false)) + shl(s, 13);
}

var function parse_cond(expr, inv) {
  var c = map_cond[expr];
  if( ! c ) { werror("expected condition operand"); }
  return shl(bit.bxor(c, inv), 12);
}

var function parse_load(params, nparams, n, op) {
  if( params[n+2] ) { werror("too many operands"); }
  var pn, p2 = params[n], params[n+1];
  var p1, wb = match(pn, "^%[%s*(.-)%s*%](!?)$");
  if( ! p1 ) {
    if( ! p2 ) {
      var reg, tailr = match(pn, "^([%w_:]+)%s*(.*)$");
      if( reg && tailr != "" ) {
	var base, tp = parse_reg_base(reg);
	if( tp ) {
	  waction("IMML", 0, format(tp.ctypefmt, tailr));
	  return op + base;
	}
      }
    }
    werror("expected address operand");
  }
  var scale = shr(op, 30);
  if( p2 ) {
    if( wb == "!" ) { werror("bad use of '!'"); }
    op +=   parse_reg_base(p1) + parse_imm(p2, 9, 12, 0, true) + 0x400;
  } else if( wb == "!" ) {
    var p1a, p2a = match(p1, "^([^,%s]*)%s*,%s*(.*)$");
    if( ! p1a ) { werror("bad use of '!'"); }
    op +=   parse_reg_base(p1a) + parse_imm(p2a, 9, 12, 0, true) + 0xc00;
  } else {
    var p1a, p2a = match(p1, "^([^,%s]*)%s*(.*)$");
    op +=   parse_reg_base(p1a);
    if( p2a != "" ) {
      var imm = match(p2a, "^,%s*#(.*)$");
      if( imm ) {
	op +=   parse_imm_load(imm, scale);
      } else {
	var p2b, p3b, p3s = match(p2a, "^,%s*([^,%s]*)%s*,?%s*(%S*)%s*(.*)$");
	op +=   shl(parse_reg(p2b), 16) + 0x00200800;
	if( parse_reg_type != "x" && parse_reg_type != "w" ) {
	  werror("bad index register type");
	}
	if( p3b == "" ) {
	  if( parse_reg_type != "x" ) { werror("bad index register type"); }
	  op +=   0x6000;
	} else {
	  if( p3s == "" || p3s == "#0" ) {
	  } else if( p3s == "#"..scale ) {
	    op +=   0x1000;
	  } else {
	    werror("bad scale");
	  }
	  if( parse_reg_type == "x" ) {
	    if( p3b == "lsl" && p3s != "" ) { op +=   0x6000;
	    } else if( p3b == "sxtx" ) { op +=   0xe000;
	    } else {
	      werror("bad extend/shift specifier");
	    }
	  } else {
	    if( p3b == "uxtw" ) { op +=   0x4000;
	    } else if( p3b == "sxtw" ) { op +=   0xc000;
	    } else {
	      werror("bad extend/shift specifier");
	    }
	  }
	}
      }
    } else {
      if( wb == "!" ) { werror("bad use of '!'"); }
      op +=   0x01000000;
    }
  }
  return op;
}

var function parse_load_pair(params, nparams, n, op) {
  if( params[n+2] ) { werror("too many operands"); }
  var pn, p2 = params[n], params[n+1];
  var scale = shr(op, 30) == 0 && 2 || 3;
  var p1, wb = match(pn, "^%[%s*(.-)%s*%](!?)$");
  if( ! p1 ) {
    if( ! p2 ) {
      var reg, tailr = match(pn, "^([%w_:]+)%s*(.*)$");
      if( reg && tailr != "" ) {
	var base, tp = parse_reg_base(reg);
	if( tp ) {
	  waction("IMM", 32768+7*32+15+scale*1024, format(tp.ctypefmt, tailr));
	  return op + base + 0x01000000;
	}
      }
    }
    werror("expected address operand");
  }
  if( p2 ) {
    if( wb == "!" ) { werror("bad use of '!'"); }
    op +=   0x00800000;
  } else {
    var p1a, p2a = match(p1, "^([^,%s]*)%s*,%s*(.*)$");
    if( p1a ) { p1, p2 = p1a, p2a; } else { p2 = "#0"; }
    op +=   (wb == "!" && 0x01800000 || 0x01000000);
  }
  return op + parse_reg_base(p1) + parse_imm(p2, 7, 15, scale, true);
}

var function parse_label(label, def) {
  var prefix = sub(label, 1, 2);
  // =>label (pc label reference)
  if( prefix == "=>" ) {
    return "PC", 0, sub(label, 3);
  }
  // ->name (global label reference)
  if( prefix == "->" ) {
    return "LG", map_global[sub(label, 3)];
  }
  if( def ) {
    // [1-9] (local label definition)
    if( match(label, "^[1-9]$") ) {
      return "LG", 10+tonumber(label);
    }
  } else {
    // [<>][1-9] (local label reference)
    var dir, lnum = match(label, "^([<>])([1-9])$");
    if( dir ) { // Fwd: 1-9, Bkwd: 11-19.
      return "LG", lnum + (dir == ">" && 0 || 10);
    }
    // extern label (extern label reference)
    var extname = match(label, "^extern%s+(%S+)$");
    if( extname ) {
      return "EXT", map_extern[extname];
    }
  }
  werror("bad label `"..label.."'");
}

var function branch_type(op) {
  if( band(op, 0x7c000000) == 0x14000000 ) { return 0; // B, BL
  } else if( shr(op, 24) == 0x54 || band(op, 0x7e000000) == 0x34000000 ||
	 band(op, 0x3b000000) == 0x18000000 ) {
    return 0x800; // B.cond, CBZ, CBNZ, LDR* literal
  } else if( band(op, 0x7e000000) == 0x36000000 ) { return 0x1000; // TBZ, TBNZ
  } else if( band(op, 0x9f000000) == 0x10000000 ) { return 0x2000; // ADR
  } else if( band(op, 0x9f000000) == band(0x90000000) ) { return 0x3000; // ADRP
  } else {
    assert(false, "unknown branch type");
  }
}

//----------------------------------------------------------------------------

var map_op, op_template;

var function op_alias(opname, f) {
  return function(params, nparams) {
    if( ! params ) { return "-> "..opname->sub(1, -3); }
    f(params, nparams);
    op_template(params, map_op[opname], nparams);
  };
}

var function alias_bfx(p) {
  p[4] = "#("..p[3]->sub(2)..")+("..p[4]->sub(2)..")-1";
}

var function alias_bfiz(p) {
  parse_reg(p[1]);
  if( parse_reg_type == "w" ) {
    p[3] = "#-("..p[3]->sub(2)..")%32";
    p[4] = "#("..p[4]->sub(2)..")-1";
  } else {
    p[3] = "#-("..p[3]->sub(2)..")%64";
    p[4] = "#("..p[4]->sub(2)..")-1";
  }
}

var alias_lslimm = op_alias("ubfm_4", function(p) {
  parse_reg(p[1]);
  var sh = p[3]->sub(2);
  if( parse_reg_type == "w" ) {
    p[3] = "#-("..sh..")%32";
    p[4] = "#31-("..sh..")";
  } else {
    p[3] = "#-("..sh..")%64";
    p[4] = "#63-("..sh..")";
  }
});

// Template strings for ARM instructions.
map_op = {
  // Basic data processing instructions.
  add_3  = "0b000000DNMg|11000000pDpNIg|8b206000pDpNMx",
  add_4  = "0b000000DNMSg|0b200000DNMXg|8b200000pDpNMXx|8b200000pDpNxMwX",
  adds_3 = "2b000000DNMg|31000000DpNIg|ab206000DpNMx",
  adds_4 = "2b000000DNMSg|2b200000DNMXg|ab200000DpNMXx|ab200000DpNxMwX",
  cmn_2  = "2b00001fNMg|3100001fpNIg|ab20601fpNMx",
  cmn_3  = "2b00001fNMSg|2b20001fNMXg|ab20001fpNMXx|ab20001fpNxMwX",

  sub_3  = "4b000000DNMg|51000000pDpNIg|cb206000pDpNMx",
  sub_4  = "4b000000DNMSg|4b200000DNMXg|cb200000pDpNMXx|cb200000pDpNxMwX",
  subs_3 = "6b000000DNMg|71000000DpNIg|eb206000DpNMx",
  subs_4 = "6b000000DNMSg|6b200000DNMXg|eb200000DpNMXx|eb200000DpNxMwX",
  cmp_2  = "6b00001fNMg|7100001fpNIg|eb20601fpNMx",
  cmp_3  = "6b00001fNMSg|6b20001fNMXg|eb20001fpNMXx|eb20001fpNxMwX",

  neg_2  = "4b0003e0DMg",
  neg_3  = "4b0003e0DMSg",
  negs_2 = "6b0003e0DMg",
  negs_3 = "6b0003e0DMSg",

  adc_3  = "1a000000DNMg",
  adcs_3 = "3a000000DNMg",
  sbc_3  = "5a000000DNMg",
  sbcs_3 = "7a000000DNMg",
  ngc_2  = "5a0003e0DMg",
  ngcs_2 = "7a0003e0DMg",

  and_3  = "0a000000DNMg|12000000pDNig",
  and_4  = "0a000000DNMSg",
  orr_3  = "2a000000DNMg|32000000pDNig",
  orr_4  = "2a000000DNMSg",
  eor_3  = "4a000000DNMg|52000000pDNig",
  eor_4  = "4a000000DNMSg",
  ands_3 = "6a000000DNMg|72000000DNig",
  ands_4 = "6a000000DNMSg",
  tst_2  = "6a00001fNMg|7200001fNig",
  tst_3  = "6a00001fNMSg",

  bic_3  = "0a200000DNMg",
  bic_4  = "0a200000DNMSg",
  orn_3  = "2a200000DNMg",
  orn_4  = "2a200000DNMSg",
  eon_3  = "4a200000DNMg",
  eon_4  = "4a200000DNMSg",
  bics_3 = "6a200000DNMg",
  bics_4 = "6a200000DNMSg",

  movn_2 = "12800000DWg",
  movn_3 = "12800000DWRg",
  movz_2 = "52800000DWg",
  movz_3 = "52800000DWRg",
  movk_2 = "72800000DWg",
  movk_3 = "72800000DWRg",

  // TODO: this doesn't cover all valid immediates for mov reg, #imm.
  mov_2  = "2a0003e0DMg|52800000DW|320003e0pDig|11000000pDpNg",
  mov_3  = "2a0003e0DMSg",
  mvn_2  = "2a2003e0DMg",
  mvn_3  = "2a2003e0DMSg",

  adr_2  = "10000000DBx",
  adrp_2 = "90000000DBx",

  csel_4  = "1a800000DNMCg",
  csinc_4 = "1a800400DNMCg",
  csinv_4 = "5a800000DNMCg",
  csneg_4 = "5a800400DNMCg",
  cset_2  = "1a9f07e0Dcg",
  csetm_2 = "5a9f03e0Dcg",
  cinc_3  = "1a800400DNmcg",
  cinv_3  = "5a800000DNmcg",
  cneg_3  = "5a800400DNmcg",

  ccmn_4 = "3a400000NMVCg|3a400800N5VCg",
  ccmp_4 = "7a400000NMVCg|7a400800N5VCg",

  madd_4 = "1b000000DNMAg",
  msub_4 = "1b008000DNMAg",
  mul_3  = "1b007c00DNMg",
  mneg_3 = "1b00fc00DNMg",

  smaddl_4 = "9b200000DxNMwAx",
  smsubl_4 = "9b208000DxNMwAx",
  smull_3  = "9b207c00DxNMw",
  smnegl_3 = "9b20fc00DxNMw",
  smulh_3  = "9b407c00DNMx",
  umaddl_4 = "9ba00000DxNMwAx",
  umsubl_4 = "9ba08000DxNMwAx",
  umull_3  = "9ba07c00DxNMw",
  umnegl_3 = "9ba0fc00DxNMw",
  umulh_3  = "9bc07c00DNMx",

  udiv_3 = "1ac00800DNMg",
  sdiv_3 = "1ac00c00DNMg",

  // Bit operations.
  sbfm_4 = "13000000DN12w|93400000DN12x",
  bfm_4  = "33000000DN12w|b3400000DN12x",
  ubfm_4 = "53000000DN12w|d3400000DN12x",
  extr_4 = "13800000DNM2w|93c00000DNM2x",

  sxtb_2 = "13001c00DNw|93401c00DNx",
  sxth_2 = "13003c00DNw|93403c00DNx",
  sxtw_2 = "93407c00DxNw",
  uxtb_2 = "53001c00DNw",
  uxth_2 = "53003c00DNw",

  sbfx_4  = op_alias("sbfm_4", alias_bfx),
  bfxil_4 = op_alias("bfm_4", alias_bfx),
  ubfx_4  = op_alias("ubfm_4", alias_bfx),
  sbfiz_4 = op_alias("sbfm_4", alias_bfiz),
  bfi_4   = op_alias("bfm_4", alias_bfiz),
  ubfiz_4 = op_alias("ubfm_4", alias_bfiz),

  lsl_3  = function(params, nparams) {
    if( params && params[3]->byte() == 35 ) {
      return alias_lslimm(params, nparams);
    } else {
      return op_template(params, "1ac02000DNMg", nparams);
    }
  },
  lsr_3  = "1ac02400DNMg|53007c00DN1w|d340fc00DN1x",
  asr_3  = "1ac02800DNMg|13007c00DN1w|9340fc00DN1x",
  ror_3  = "1ac02c00DNMg|13800000DNm2w|93c00000DNm2x",

  clz_2   = "5ac01000DNg",
  cls_2   = "5ac01400DNg",
  rbit_2  = "5ac00000DNg",
  rev_2   = "5ac00800DNw|dac00c00DNx",
  rev16_2 = "5ac00400DNg",
  rev32_2 = "dac00800DNx",

  // Loads and stores.
  ["strb_*"]  = "38000000DwL",
  ["ldrb_*"]  = "38400000DwL",
  ["ldrsb_*"] = "38c00000DwL|38800000DxL",
  ["strh_*"]  = "78000000DwL",
  ["ldrh_*"]  = "78400000DwL",
  ["ldrsh_*"] = "78c00000DwL|78800000DxL",
  ["str_*"]   = "b8000000DwL|f8000000DxL|bc000000DsL|fc000000DdL",
  ["ldr_*"]   = "18000000DwB|58000000DxB|1c000000DsB|5c000000DdB|b8400000DwL|f8400000DxL|bc400000DsL|fc400000DdL",
  ["ldrsw_*"] = "98000000DxB|b8800000DxL",
  // NOTE: ldur etc. are handled by ldr et al.

  ["stp_*"]   = "28000000DAwP|a8000000DAxP|2c000000DAsP|6c000000DAdP",
  ["ldp_*"]   = "28400000DAwP|a8400000DAxP|2c400000DAsP|6c400000DAdP",
  ["ldpsw_*"] = "68400000DAxP",

  // Branches.
  b_1    = "14000000B",
  bl_1   = "94000000B",
  blr_1  = "d63f0000Nx",
  br_1   = "d61f0000Nx",
  ret_0  = "d65f03c0",
  ret_1  = "d65f0000Nx",
  // b.cond is added below.
  cbz_2  = "34000000DBg",
  cbnz_2 = "35000000DBg",
  tbz_3  = "36000000DTBw|36000000DTBx",
  tbnz_3 = "37000000DTBw|37000000DTBx",

  // Miscellaneous instructions.
  // TODO: hlt, hvc, smc, svc, eret, dcps[123], drps, mrs, msr
  // TODO: sys, sysl, ic, dc, at, tlbi
  // TODO: hint, yield, wfe, wfi, sev, sevl
  // TODO: clrex, dsb, dmb, isb
  nop_0  = "d503201f",
  brk_0  = "d4200000",
  brk_1  = "d4200000W",

  // Floating point instructions.
  fmov_2  = "1e204000DNf|1e260000DwNs|1e270000DsNw|9e660000DxNd|9e670000DdNx|1e201000DFf",
  fabs_2  = "1e20c000DNf",
  fneg_2  = "1e214000DNf",
  fsqrt_2 = "1e21c000DNf",

  fcvt_2  = "1e22c000DdNs|1e624000DsNd",

  // TODO: half-precision and fixed-point conversions.
  fcvtas_2 = "1e240000DwNs|9e240000DxNs|1e640000DwNd|9e640000DxNd",
  fcvtau_2 = "1e250000DwNs|9e250000DxNs|1e650000DwNd|9e650000DxNd",
  fcvtms_2 = "1e300000DwNs|9e300000DxNs|1e700000DwNd|9e700000DxNd",
  fcvtmu_2 = "1e310000DwNs|9e310000DxNs|1e710000DwNd|9e710000DxNd",
  fcvtns_2 = "1e200000DwNs|9e200000DxNs|1e600000DwNd|9e600000DxNd",
  fcvtnu_2 = "1e210000DwNs|9e210000DxNs|1e610000DwNd|9e610000DxNd",
  fcvtps_2 = "1e280000DwNs|9e280000DxNs|1e680000DwNd|9e680000DxNd",
  fcvtpu_2 = "1e290000DwNs|9e290000DxNs|1e690000DwNd|9e690000DxNd",
  fcvtzs_2 = "1e380000DwNs|9e380000DxNs|1e780000DwNd|9e780000DxNd",
  fcvtzu_2 = "1e390000DwNs|9e390000DxNs|1e790000DwNd|9e790000DxNd",

  scvtf_2  = "1e220000DsNw|9e220000DsNx|1e620000DdNw|9e620000DdNx",
  ucvtf_2  = "1e230000DsNw|9e230000DsNx|1e630000DdNw|9e630000DdNx",

  frintn_2 = "1e244000DNf",
  frintp_2 = "1e24c000DNf",
  frintm_2 = "1e254000DNf",
  frintz_2 = "1e25c000DNf",
  frinta_2 = "1e264000DNf",
  frintx_2 = "1e274000DNf",
  frinti_2 = "1e27c000DNf",

  fadd_3   = "1e202800DNMf",
  fsub_3   = "1e203800DNMf",
  fmul_3   = "1e200800DNMf",
  fnmul_3  = "1e208800DNMf",
  fdiv_3   = "1e201800DNMf",

  fmadd_4  = "1f000000DNMAf",
  fmsub_4  = "1f008000DNMAf",
  fnmadd_4 = "1f200000DNMAf",
  fnmsub_4 = "1f208000DNMAf",

  fmax_3   = "1e204800DNMf",
  fmaxnm_3 = "1e206800DNMf",
  fmin_3   = "1e205800DNMf",
  fminnm_3 = "1e207800DNMf",

  fcmp_2   = "1e202000NMf|1e202008NZf",
  fcmpe_2  = "1e202010NMf|1e202018NZf",

  fccmp_4  = "1e200400NMVCf",
  fccmpe_4 = "1e200410NMVCf",

  fcsel_4  = "1e200c00DNMCf",

  // TODO: crc32*, aes*, sha*, pmull
  // TODO: SIMD instructions.
};

for( cond,c in pairs(map_cond) ) {
  map_op["b"..cond.."_1"] = tohex(0x54000000+c).."B";
}

//----------------------------------------------------------------------------

// Handle opcodes defined with template strings.
var function parse_template(params, template, nparams, pos) {
  var op = tonumber(sub(template, 1, 8), 16);
  var n = 1;
  var rtt = {};

  parse_reg_type = false;

  // Process each character.
  for( p in gmatch(sub(template, 9), ".") ) {
    var q = params[n];
    if( p == "D" ) {
      op +=   parse_reg(q); n +=   1;
    } else if( p == "N" ) {
      op +=   shl(parse_reg(q), 5); n +=   1;
    } else if( p == "M" ) {
      op +=   shl(parse_reg(q), 16); n +=   1;
    } else if( p == "A" ) {
      op +=   shl(parse_reg(q), 10); n +=   1;
    } else if( p == "m" ) {
      op +=   shl(parse_reg(params[n-1]), 16);

    } else if( p == "p" ) {
      if( q == "sp" ) { params[n] = "@x31"; }
    } else if( p == "g" ) {
      if( parse_reg_type == "x" ) {
	op +=   0x80000000;
      } else if( parse_reg_type != "w" ) {
	werror("bad register type");
      }
      parse_reg_type = false;
    } else if( p == "f" ) {
      if( parse_reg_type == "d" ) {
	op +=   0x00400000;
      } else if( parse_reg_type != "s" ) {
	werror("bad register type");
      }
      parse_reg_type = false;
    } else if( p == "x" || p == "w" || p == "d" || p == "s" ) {
      if( parse_reg_type != p ) {
	werror("register size mismatch");
      }
      parse_reg_type = false;

    } else if( p == "L" ) {
      op = parse_load(params, nparams, n, op);
    } else if( p == "P" ) {
      op = parse_load_pair(params, nparams, n, op);

    } else if( p == "B" ) {
      var mode, v, s = parse_label(q, false); n +=   1;
      var m = branch_type(op);
      waction("REL_"..mode, v+m, s, 1);

    } else if( p == "I" ) {
      op +=   parse_imm12(q); n +=   1;
    } else if( p == "i" ) {
      op +=   parse_imm13(q); n +=   1;
    } else if( p == "W" ) {
      op +=   parse_imm(q, 16, 5, 0, false); n +=   1;
    } else if( p == "T" ) {
      op +=   parse_imm6(q); n +=   1;
    } else if( p == "1" ) {
      op +=   parse_imm(q, 6, 16, 0, false); n +=   1;
    } else if( p == "2" ) {
      op +=   parse_imm(q, 6, 10, 0, false); n +=   1;
    } else if( p == "5" ) {
      op +=   parse_imm(q, 5, 16, 0, false); n +=   1;
    } else if( p == "V" ) {
      op +=   parse_imm(q, 4, 0, 0, false); n +=   1;
    } else if( p == "F" ) {
      op +=   parse_fpimm(q); n +=   1;
    } else if( p == "Z" ) {
      if( q != "#0" && q != "#0.0" ) { werror("expected zero immediate"); }
      n +=   1;

    } else if( p == "S" ) {
      op +=   parse_shift(q); n +=   1;
    } else if( p == "X" ) {
      op +=   parse_extend(q); n +=   1;
    } else if( p == "R" ) {
      op +=   parse_lslx16(q); n +=   1;
    } else if( p == "C" ) {
      op +=   parse_cond(q, 0); n +=   1;
    } else if( p == "c" ) {
      op +=   parse_cond(q, 1); n +=   1;

    } else {
      assert(false);
    }
  }
  wputpos(pos, op);
}

function op_template(params, template, nparams) {
  if( ! params ) { return template->gsub("%x%x%x%x%x%x%x%x", ""); }

  // Limit number of section buffer positions used by a single dasm_put().
  // A single opcode needs a maximum of 3 positions.
  if( secpos+3 > maxsecpos ) { wflush(); }
  var pos = wpos();
  var lpos, apos, spos = #actlist, #actargs, secpos;

  var ok, err;
  for( t in gmatch(template, "[^|]+") ) {
    ok, err = pcall(parse_template, params, t, nparams, pos);
    if( ok ) { return; }
    secpos = spos;
    actlist[lpos+1] = null;
    actlist[lpos+2] = null;
    actlist[lpos+3] = null;
    actargs[apos+1] = null;
    actargs[apos+2] = null;
    actargs[apos+3] = null;
  }
  error(err, 0);
}

map_op[".template__"] = op_template;

//----------------------------------------------------------------------------

// Pseudo-opcode to mark the position where the action list is to be emitted.
map_op[".actionlist_1"] = function(params) {
  if( ! params ) { return "cvar"; }
  var name = params[1]; // No syntax check. You get to keep the pieces.
  wline(function(out) { writeactions(out, name); });
};

// Pseudo-opcode to mark the position where the global enum is to be emitted.
map_op[".globals_1"] = function(params) {
  if( ! params ) { return "prefix"; }
  var prefix = params[1]; // No syntax check. You get to keep the pieces.
  wline(function(out) { writeglobals(out, prefix); });
};

// Pseudo-opcode to mark the position where the global names are to be emitted.
map_op[".globalnames_1"] = function(params) {
  if( ! params ) { return "cvar"; }
  var name = params[1]; // No syntax check. You get to keep the pieces.
  wline(function(out) { writeglobalnames(out, name); });
};

// Pseudo-opcode to mark the position where the extern names are to be emitted.
map_op[".externnames_1"] = function(params) {
  if( ! params ) { return "cvar"; }
  var name = params[1]; // No syntax check. You get to keep the pieces.
  wline(function(out) { writeexternnames(out, name); });
};

//----------------------------------------------------------------------------

// Label pseudo-opcode (converted from trailing colon form).
map_op[".label_1"] = function(params) {
  if( ! params ) { return "[1-9] | ->global | =>pcexpr"; }
  if( secpos+1 > maxsecpos ) { wflush(); }
  var mode, n, s = parse_label(params[1], true);
  if( mode == "EXT" ) { werror("bad label definition"); }
  waction("LABEL_"..mode, n, s, 1);
};

//----------------------------------------------------------------------------

// Pseudo-opcodes for data storage.
map_op[".long_*"] = function(params) {
  if( ! params ) { return "imm..."; }
  for( _,p in ipairs(params) ) {
    var n = tonumber(p);
    if( ! n ) { werror("bad immediate `"..p.."'"); }
    if( n < 0 ) { n +=   2**32; }
    wputw(n);
    if( secpos+2 > maxsecpos ) { wflush(); }
  }
};

// Alignment pseudo-opcode.
map_op[".align_1"] = function(params) {
  if( ! params ) { return "numpow2"; }
  if( secpos+1 > maxsecpos ) { wflush(); }
  var align = tonumber(params[1]);
  if( align ) {
    var x = align;
    // Must be a power of 2 in the range (2 ... 256).
    for( i=1,8 ) {
      x = x / 2;
      if( x == 1 ) {
	waction("ALIGN", align-1, null, 1); // Action byte is 2**n-1.
	return;
      }
    }
  }
  werror("bad alignment");
};

//----------------------------------------------------------------------------

// Pseudo-opcode for (primitive) type definitions (map to C types).
map_op[".type_3"] = function(params, nparams) {
  if( ! params ) {
    return nparams == 2 && "name, ctype" || "name, ctype, reg";
  }
  var name, ctype, reg = params[1], params[2], params[3];
  if( ! match(name, "^[%a_][%w_]*$") ) {
    werror("bad type name `"..name.."'");
  }
  var tp = map_type[name];
  if( tp ) {
    werror("duplicate type `"..name.."'");
  }
  // Add #type to defines. A bit unclean to put it in map_archdef.
  map_archdef["#"..name] = "sizeof("..ctype..")";
  // Add new type and emit shortcut define.
  var num = ctypenum + 1;
  map_type[name] = {
    ctype = ctype,
    ctypefmt = format("Dt%X(%%s)", num),
    reg = reg,
  };
  wline(format("#define Dt%X(_V) (int)(ptrdiff_t)&(((%s *)0)_V)", num, ctype));
  ctypenum = num;
};
map_op[".type_2"] = map_op[".type_3"];

// Dump type definitions.
var function dumptypes(out, lvl) {
  var t = {};
  for( name in pairs(map_type) ) { t[#t+1] = name; }
  sort(t);
  out->write("Type definitions:\n");
  for( _,name in ipairs(t) ) {
    var tp = map_type[name];
    var reg = tp.reg || "";
    out->write(format("  %-20s %-20s %s\n", name, tp.ctype, reg));
  }
  out->write("\n");
}

//----------------------------------------------------------------------------

// Set the current section.
function _M.section(num) {
  waction("SECTION", num);
  wflush(true); // SECTION is a terminal action.
}

//----------------------------------------------------------------------------

// Dump architecture description.
function _M.dumparch(out) {
  out->write(format("DynASM %s version %s, released %s\n\n",
    _info.arch, _info.version, _info.release));
  dumpactions(out);
}

// Dump all user defined elements.
function _M.dumpdef(out, lvl) {
  dumptypes(out, lvl);
  dumpglobals(out, lvl);
  dumpexterns(out, lvl);
}

//----------------------------------------------------------------------------

// Pass callbacks from/to the DynASM core.
function _M.passcb(wl, we, wf, ww) {
  wline, werror, wfatal, wwarn = wl, we, wf, ww;
  return wflush;
}

// Setup the arch-specific module.
function _M.setup(arch, opt) {
  g_arch, g_opt = arch, opt;
}

// Merge the core maps and the arch-specific maps.
function _M.mergemaps(map_coreop, map_def) {
  setmetatable(map_op, { __index = map_coreop });
  setmetatable(map_def, { __index = map_archdef });
  return map_op, map_def;
}

return _M;

//----------------------------------------------------------------------------

