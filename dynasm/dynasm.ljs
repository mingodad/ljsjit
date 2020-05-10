//----------------------------------------------------------------------------
// DynASM. A dynamic assembler for code generation engines.
// Originally designed and implemented for LuaJIT.
//
// Copyright (C) 2005-2020 Mike Pall. All rights reserved.
// See below for full copyright notice.
//----------------------------------------------------------------------------

// Application information.
var _info = {
  name =	"DynASM",
  description =	"A dynamic assembler for code generation engines",
  version =	"1.4.0",
  vernum =	 10400,
  release =	"2015-10-18",
  author =	"Mike Pall",
  url =		"http://luajit.org/dynasm.html",
  license =	"MIT",
  copyright =	[=[
Copyright (C) 2005-2020 Mike Pall. All rights reserved.

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

[ MIT license: http://www.opensource.org/licenses/mit-license.php ]
]=],
};

// Cache library functions.
var type, pairs, ipairs = type, pairs, ipairs;
var pcall, error, assert = pcall, error, assert;
var _s = string;
var sub, match, gmatch, gsub = _s.sub, _s.match, _s.gmatch, _s.gsub;
var format, rep, upper = _s.format, _s.rep, _s.upper;
var _t = table;
var insert, remove, concat, sort = _t.insert, _t.remove, _t.concat, _t.sort;
var exit = os.exit;
var io = io;
var stdin, stdout, stderr = io.stdin, io.stdout, io.stderr;

//----------------------------------------------------------------------------

// Program options.
var g_opt = {};

// Global state for current file.
var g_fname, g_curline, g_indent, g_lineno, g_synclineno, g_arch;
var g_errcount = 0;

// Write buffer for output file.
var g_wbuffer, g_capbuffer;

//----------------------------------------------------------------------------

// Write an output line (or callback function) to the buffer.
var function wline(line, needindent) {
  var buf = g_capbuffer || g_wbuffer;
  buf[#buf+1] = needindent && g_indent..line || line;
  g_synclineno +=   1;
}

// Write assembler line as a comment, if requestd.
var function wcomment(aline) {
  if( g_opt.comment ) {
    wline(g_opt.comment..aline..g_opt.endcomment, true);
  }
}

// Resync CPP line numbers.
var function wsync() {
  if( g_synclineno != g_lineno && g_opt.cpp ) {
    wline("#line "..g_lineno..' "'..g_fname..'"');
    g_synclineno = g_lineno;
  }
}

// Dummy action flush function. Replaced with arch-specific function later.
var function wflush(term) {
}

// Dump all buffered output lines.
var function wdumplines(out, buf) {
  for( _,line in ipairs(buf) ) {
    if( type(line) == "string" ) {
      assert(out->write(line, "\n"));
    } else {
      // Special callback to dynamically insert lines after end of processing.
      line(out);
    }
  }
}

//----------------------------------------------------------------------------

// Emit an error. Processing continues with next statement.
var function werror(msg) {
  error(format("%s:%s: error: %s:\n%s", g_fname, g_lineno, msg, g_curline), 0);
}

// Emit a fatal error. Processing stops.
var function wfatal(msg) {
  g_errcount = "fatal";
  werror(msg);
}

// Print a warning. Processing continues.
var function wwarn(msg) {
  stderr->write(format("%s:%s: warning: %s:\n%s\n",
    g_fname, g_lineno, msg, g_curline));
}

// Print caught error message. But suppress excessive errors.
var function wprinterr(...) {
  if( type(g_errcount) == "number" ) {
    // Regular error.
    g_errcount +=   1;
    if( g_errcount < 21 ) { // Seems to be a reasonable limit.
      stderr->write(...);
    } else if( g_errcount == 21 ) {
      stderr->write(g_fname,
	":*: warning: too many errors (suppressed further messages).\n");
    }
  } else {
    // Fatal error.
    stderr->write(...);
    return true; // Stop processing.
  }
}

//----------------------------------------------------------------------------

// Map holding all option handlers.
var opt_map = {};
var opt_current;

// Print error and exit with error status.
var function opterror(...) {
  stderr->write("dynasm.ljs: ERROR: ", ...);
  stderr->write("\n");
  exit(1);
}

// Get option parameter.
var function optparam(args) {
  var argn = args.argn;
  var p = args[argn];
  if( ! p ) {
    opterror("missing parameter for option `", opt_current, "'.");
  }
  args.argn = argn + 1;
  return p;
}

//----------------------------------------------------------------------------

// Core pseudo-opcodes.
var map_coreop = {};
// Dummy opcode map. Replaced by arch-specific map.
var map_op = {};

// Forward declarations.
var dostmt;
var readfile;

//----------------------------------------------------------------------------

// Map for defines (initially empty, chains to arch-specific map).
var map_def = {};

// Pseudo-opcode to define a substitution.
map_coreop[".define_2"] = function(params, nparams) {
  if( ! params ) { return nparams == 1 && "name" || "name, subst"; }
  var name, def = params[1], params[2] || "1";
  if( ! match(name, "^[%a_][%w_]*$") ) { werror("bad or duplicate define"); }
  map_def[name] = def;
};
map_coreop[".define_1"] = map_coreop[".define_2"];

// Define a substitution on the command line.
function opt_map.D(args) {
  var namesubst = optparam(args);
  var name, subst = match(namesubst, "^([%a_][%w_]*)=(.*)$");
  if( name ) {
    map_def[name] = subst;
  } else if( match(namesubst, "^[%a_][%w_]*$") ) {
    map_def[namesubst] = "1";
  } else {
    opterror("bad define");
  }
}

// Undefine a substitution on the command line.
function opt_map.U(args) {
  var name = optparam(args);
  if( match(name, "^[%a_][%w_]*$") ) {
    map_def[name] = null;
  } else {
    opterror("bad define");
  }
}

// Helper for definesubst.
var gotsubst;

var function definesubst_one(word) {
  var subst = map_def[word];
  if( subst ) { gotsubst = word; return subst; } else { return word; }
}

// Iteratively substitute defines.
var function definesubst(stmt) {
  // Limit number of iterations.
  for( i=1,100 ) {
    gotsubst = false;
    stmt = gsub(stmt, "#?[%w_]+", definesubst_one);
    if( ! gotsubst ) { break; }
  }
  if( gotsubst ) { wfatal("recursive define involving `"..gotsubst.."'"); }
  return stmt;
}

// Dump all defines.
var function dumpdefines(out, lvl) {
  var t = {};
  for( name in pairs(map_def) ) {
    t[#t+1] = name;
  }
  sort(t);
  out->write("Defines:\n");
  for( _,name in ipairs(t) ) {
    var subst = map_def[name];
    if( g_arch ) { subst = g_arch.revdef(subst); }
    out->write(format("  %-20s %s\n", name, subst));
  }
  out->write("\n");
}

//----------------------------------------------------------------------------

// Support variables for conditional assembly.
var condlevel = 0;
var condstack = {};

// Evaluate condition with a Lua expression. Substitutions already performed.
var function cond_eval(cond) {
  var func, err;
  if( setfenv ) {
    func, err = loadstring("return "..cond, "=expr");
  } else {
    // No globals. All unknown identifiers evaluate to nil.
    func, err = load("return "..cond, "=expr", "t", {});
  }
  if( func ) {
    if( setfenv ) {
      setfenv(func, {}); // No globals. All unknown identifiers evaluate to nil.
    }
    var ok, res = pcall(func);
    if( ok ) {
      if( res == 0 ) { return false; } // Oh well.
      return ! ! res;
    }
    err = res;
  }
  wfatal("bad condition: "..err);
}

// Skip statements until next conditional pseudo-opcode at the same level.
var function stmtskip() {
  var dostmt_save = dostmt;
  var lvl = 0;
  dostmt = function(stmt) {
    var op = match(stmt, "^%s*(%S+)");
    if( op == ".if" ) {
      lvl +=   1;
    } else if( lvl != 0 ) {
      if( op == ".endif" ) { lvl -=   1; }
    } else if( op == ".elif" || op == ".else" || op == ".endif" ) {
      dostmt = dostmt_save;
      dostmt(stmt);
    }
  };
}

// Pseudo-opcodes for conditional assembly.
map_coreop[".if_1"] = function(params) {
  if( ! params ) { return "condition"; }
  var lvl = condlevel + 1;
  var res = cond_eval(params[1]);
  condlevel = lvl;
  condstack[lvl] = res;
  if( ! res ) { stmtskip(); }
};

map_coreop[".elif_1"] = function(params) {
  if( ! params ) { return "condition"; }
  if( condlevel == 0 ) { wfatal(".elif without .if"); }
  var lvl = condlevel;
  var res = condstack[lvl];
  if( res ) {
    if( res == "else" ) { wfatal(".elif after .else"); }
  } else {
    res = cond_eval(params[1]);
    if( res ) {
      condstack[lvl] = res;
      return;
    }
  }
  stmtskip();
};

map_coreop[".else_0"] = function(params) {
  if( condlevel == 0 ) { wfatal(".else without .if"); }
  var lvl = condlevel;
  var res = condstack[lvl];
  condstack[lvl] = "else";
  if( res ) {
    if( res == "else" ) { wfatal(".else after .else"); }
    stmtskip();
  }
};

map_coreop[".endif_0"] = function(params) {
  var lvl = condlevel;
  if( lvl == 0 ) { wfatal(".endif without .if"); }
  condlevel = lvl - 1;
};

// Check for unfinished conditionals.
var function checkconds() {
  if( g_errcount != "fatal" && condlevel != 0 ) {
    wprinterr(g_fname, ":*: error: unbalanced conditional\n");
  }
}

//----------------------------------------------------------------------------

// Search for a file in the given path and open it for reading.
var function pathopen(path, name) {
  var dirsep = package && match(package.path, "\\") && "\\" || "/";
  for( _,p in ipairs(path) ) {
    var fullname = p == "" && name || p..dirsep..name;
    var fin = io.open(fullname, "r");
    if( fin ) {
      g_fname = fullname;
      return fin;
    }
  }
}

// Include a file.
map_coreop[".include_1"] = function(params) {
  if( ! params ) { return "filename"; }
  var name = params[1];
  // Save state. Ugly, I know. but upvalues are fast.
  var gf, gl, gcl, gi = g_fname, g_lineno, g_curline, g_indent;
  // Read the included file.
  var fatal = readfile(pathopen(g_opt.include, name) ||
			 wfatal("include file `"..name.."' not found"));
  // Restore state.
  g_synclineno = -1;
  g_fname, g_lineno, g_curline, g_indent = gf, gl, gcl, gi;
  if( fatal ) { wfatal("in include file"); }
};

// Make .include and conditionals initially available, too.
map_op[".include_1"] = map_coreop[".include_1"];
map_op[".if_1"] = map_coreop[".if_1"];
map_op[".elif_1"] = map_coreop[".elif_1"];
map_op[".else_0"] = map_coreop[".else_0"];
map_op[".endif_0"] = map_coreop[".endif_0"];

//----------------------------------------------------------------------------

// Support variables for macros.
var mac_capture, mac_lineno, mac_name;
var mac_active = {};
var mac_list = {};

// Pseudo-opcode to define a macro.
map_coreop[".macro_*"] = function(mparams) {
  if( ! mparams ) { return "name [, params...]"; }
  // Split off and validate macro name.
  var name = remove(mparams, 1);
  if( ! name ) { werror("missing macro name"); }
  if( ! (match(name, "^[%a_][%w_%.]*$") || match(name, "^%.[%w_%.]*$")) ) {
    wfatal("bad macro name `"..name.."'");
  }
  // Validate macro parameter names.
  var mdup = {};
  for( _,mp in ipairs(mparams) ) {
    if( ! match(mp, "^[%a_][%w_]*$") ) {
      wfatal("bad macro parameter name `"..mp.."'");
    }
    if( mdup[mp] ) { wfatal("duplicate macro parameter name `"..mp.."'"); }
    mdup[mp] = true;
  }
  // Check for duplicate or recursive macro definitions.
  var opname = name.."_"..#mparams;
  if( map_op[opname] || map_op[name.."_*"] ) {
    wfatal("duplicate macro `"..name.."' ("..#mparams.." parameters)");
  }
  if( mac_capture ) { wfatal("recursive macro definition"); }

  // Enable statement capture.
  var lines = {};
  mac_lineno = g_lineno;
  mac_name = name;
  mac_capture = function(stmt) { // Statement capture function.
    // Stop macro definition with .endmacro pseudo-opcode.
    if( ! match(stmt, "^%s*.endmacro%s*$") ) {
      lines[#lines+1] = stmt;
      return;
    }
    mac_capture = null;
    mac_lineno = null;
    mac_name = null;
    mac_list[#mac_list+1] = opname;
    // Add macro-op definition.
    map_op[opname] = function(params) {
      if( ! params ) { return mparams, lines; }
      // Protect against recursive macro invocation.
      if( mac_active[opname] ) { wfatal("recursive macro invocation"); }
      mac_active[opname] = true;
      // Setup substitution map.
      var subst = {};
      for( i,mp in ipairs(mparams) ) { subst[mp] = params[i]; }
      var mcom;
      if( g_opt.maccomment && g_opt.comment ) {
	mcom = " MACRO "..name.." ("..#mparams..")";
	wcomment("{"..mcom);
      }
      // Loop through all captured statements
      for( _,stmt in ipairs(lines) ) {
	// Substitute macro parameters.
	var st = gsub(stmt, "[%w_]+", subst);
	st = definesubst(st);
	st = gsub(st, "%s*%.%.%s*", ""); // Token paste a..b.
	if( mcom && sub(st, 1, 1) != "|" ) { wcomment(st); }
	// Emit statement. Use a protected call for better diagnostics.
	var ok, err = pcall(dostmt, st);
	if( ! ok ) {
	  // Add the captured statement to the error.
	  wprinterr(err, "\n", g_indent, "|  ", stmt,
		    "\t[MACRO ", name, " (", #mparams, ")]\n");
	}
      }
      if( mcom ) { wcomment("}"..mcom); }
      mac_active[opname] = null;
    };
  };
};

// An .endmacro pseudo-opcode outside of a macro definition is an error.
map_coreop[".endmacro_0"] = function(params) {
  wfatal(".endmacro without .macro");
};

// Dump all macros and their contents (with -PP only).
var function dumpmacros(out, lvl) {
  sort(mac_list);
  out->write("Macros:\n");
  for( _,opname in ipairs(mac_list) ) {
    var name = sub(opname, 1, -3);
    var params, lines = map_op[opname]();
    out->write(format("  %-20s %s\n", name, concat(params, ", ")));
    if( lvl > 1 ) {
      for( _,line in ipairs(lines) ) {
	out->write("  |", line, "\n");
      }
      out->write("\n");
    }
  }
  out->write("\n");
}

// Check for unfinished macro definitions.
var function checkmacros() {
  if( mac_capture ) {
    wprinterr(g_fname, ":", mac_lineno,
	      ": error: unfinished .macro `", mac_name ,"'\n");
  }
}

//----------------------------------------------------------------------------

// Support variables for captures.
var cap_lineno, cap_name;
var cap_buffers = {};
var cap_used = {};

// Start a capture.
map_coreop[".capture_1"] = function(params) {
  if( ! params ) { return "name"; }
  wflush();
  var name = params[1];
  if( ! match(name, "^[%a_][%w_]*$") ) {
    wfatal("bad capture name `"..name.."'");
  }
  if( cap_name ) {
    wfatal("already capturing to `"..cap_name.."' since line "..cap_lineno);
  }
  cap_name = name;
  cap_lineno = g_lineno;
  // Create or continue a capture buffer and start the output line capture.
  var buf = cap_buffers[name];
  if( ! buf ) { buf = {}; cap_buffers[name] = buf; }
  g_capbuffer = buf;
  g_synclineno = 0;
};

// Stop a capture.
map_coreop[".endcapture_0"] = function(params) {
  wflush();
  if( ! cap_name ) { wfatal(".endcapture without a valid .capture"); }
  cap_name = null;
  cap_lineno = null;
  g_capbuffer = null;
  g_synclineno = 0;
};

// Dump a capture buffer.
map_coreop[".dumpcapture_1"] = function(params) {
  if( ! params ) { return "name"; }
  wflush();
  var name = params[1];
  if( ! match(name, "^[%a_][%w_]*$") ) {
    wfatal("bad capture name `"..name.."'");
  }
  cap_used[name] = true;
  wline(function(out) {
    var buf = cap_buffers[name];
    if( buf ) { wdumplines(out, buf); }
  });
  g_synclineno = 0;
};

// Dump all captures and their buffers (with -PP only).
var function dumpcaptures(out, lvl) {
  out->write("Captures:\n");
  for( name,buf in pairs(cap_buffers) ) {
    out->write(format("  %-20s %4s)\n", name, "("..#buf));
    if( lvl > 1 ) {
      var bar = rep("=", 76);
      out->write("  ", bar, "\n");
      for( _,line in ipairs(buf) ) {
	out->write("  ", line, "\n");
      }
      out->write("  ", bar, "\n\n");
    }
  }
  out->write("\n");
}

// Check for unfinished or unused captures.
var function checkcaptures() {
  if( cap_name ) {
    wprinterr(g_fname, ":", cap_lineno,
	      ": error: unfinished .capture `", cap_name,"'\n");
    return;
  }
  for( name in pairs(cap_buffers) ) {
    if( ! cap_used[name] ) {
      wprinterr(g_fname, ":*: error: missing .dumpcapture ", name ,"\n");
    }
  }
}

//----------------------------------------------------------------------------

// Sections names.
var map_sections = {};

// Pseudo-opcode to define code sections.
// TODO: Data sections, BSS sections. Needs extra C code and API.
map_coreop[".section_*"] = function(params) {
  if( ! params ) { return "name..."; }
  if( #map_sections > 0 ) { werror("duplicate section definition"); }
  wflush();
  for( sn,name in ipairs(params) ) {
    var opname = "."..name.."_0";
    if( ! match(name, "^[%a][%w_]*$") ||
       map_op[opname] || map_op["."..name.."_*"] ) {
      werror("bad section name `"..name.."'");
    }
    map_sections[#map_sections+1] = name;
    wline(format("#define DASM_SECTION_%s\t%d", upper(name), sn-1));
    map_op[opname] = function(params) { g_arch.section(sn-1); };
  }
  wline(format("#define DASM_MAXSECTION\t\t%d", #map_sections));
};

// Dump all sections.
var function dumpsections(out, lvl) {
  out->write("Sections:\n");
  for( _,name in ipairs(map_sections) ) {
    out->write(format("  %s\n", name));
  }
  out->write("\n");
}

//----------------------------------------------------------------------------

// Replacement for customized Lua, which lacks the package library.
var prefix = "";
if( ! require ) {
  function require(name) {
    var fp = assert(io.open(prefix..name..".ljs"));
    var s = fp->read("*a");
    assert(fp->close());
    return assert(loadstring(s, "@"..name..".ljs"))();
  }
}

// Load architecture-specific module.
var function loadarch(arch) {
  if( ! match(arch, "^[%w_]+$") ) { return "bad arch name"; }
  _G._map_def = map_def;
  var ok, m_arch = pcall(require, "dasm_"..arch);
  if( ! ok ) { return "cannot load module: "..m_arch; }
  g_arch = m_arch;
  wflush = m_arch.passcb(wline, werror, wfatal, wwarn);
  m_arch.setup(arch, g_opt);
  map_op, map_def = m_arch.mergemaps(map_coreop, map_def);
}

// Dump architecture description.
function opt_map.dumparch(args) {
  var name = optparam(args);
  if( ! g_arch ) {
    var err = loadarch(name);
    if( err ) { opterror(err); }
  }

  var t = {};
  for( xname in pairs(map_coreop) ) { t[#t+1] = xname; }
  for( xname in pairs(map_op) ) { t[#t+1] = xname; }
  sort(t);

  var out = stdout;
  var _arch = g_arch._info;
  out->write(format("%s version %s, released %s, %s\n",
    _info.name, _info.version, _info.release, _info.url));
  g_arch.dumparch(out);

  var pseudo = true;
  out->write("Pseudo-Opcodes:\n");
  for( _,sname in ipairs(t) ) {
    var xname, nparam = match(sname, "^(.+)_([0-9%*])$");
    if( xname ) {
      if( pseudo && sub(xname, 1, 1) != "." ) {
	out->write("\nOpcodes:\n");
	pseudo = false;
      }
      var f = map_op[sname];
      var s;
      if( nparam != "*" ) { nparam +=   0; }
      if( nparam == 0 ) {
	s = "";
      } else if( type(f) == "string" ) {
	s = map_op[".template__"](null, f, nparam);
      } else {
	s = f(null, nparam);
      }
      if( type(s) == "table" ) {
	for( _,s2 in ipairs(s) ) {
	  out->write(format("  %-12s %s\n", xname, s2));
	}
      } else {
	out->write(format("  %-12s %s\n", xname, s));
      }
    }
  }
  out->write("\n");
  exit(0);
}

// Pseudo-opcode to set the architecture.
// Only initially available (map_op is replaced when called).
map_op[".arch_1"] = function(params) {
  if( ! params ) { return "name"; }
  var err = loadarch(params[1]);
  if( err ) { wfatal(err); }
  wline(format("#if DASM_VERSION != %d", _info.vernum));
  wline('#error "Version mismatch between DynASM and included encoding engine"');
  wline("#endif");
};

// Dummy .arch pseudo-opcode to improve the error report.
map_coreop[".arch_1"] = function(params) {
  if( ! params ) { return "name"; }
  wfatal("duplicate .arch statement");
};

//----------------------------------------------------------------------------

// Dummy pseudo-opcode. Don't confuse '.nop' with 'nop'.
map_coreop[".nop_*"] = function(params) {
  if( ! params ) { return "[ignored...]"; }
};

// Pseudo-opcodes to raise errors.
map_coreop[".error_1"] = function(params) {
  if( ! params ) { return "message"; }
  werror(params[1]);
};

map_coreop[".fatal_1"] = function(params) {
  if( ! params ) { return "message"; }
  wfatal(params[1]);
};

// Dump all user defined elements.
var function dumpdef(out) {
  var lvl = g_opt.dumpdef;
  if( lvl == 0 ) { return; }
  dumpsections(out, lvl);
  dumpdefines(out, lvl);
  if( g_arch ) { g_arch.dumpdef(out, lvl); }
  dumpmacros(out, lvl);
  dumpcaptures(out, lvl);
}

//----------------------------------------------------------------------------

// Helper for splitstmt.
var splitlvl;

var function splitstmt_one(c) {
  if( c == "(" ) {
    splitlvl = ")"..splitlvl;
  } else if( c == "[" ) {
    splitlvl = "]"..splitlvl;
  } else if( c == "{" ) {
    splitlvl = "}"..splitlvl;
  } else if( c == ")" || c == "]" || c == "}" ) {
    if( sub(splitlvl, 1, 1) != c ) { werror("unbalanced (), [] or {}"); }
    splitlvl = sub(splitlvl, 2);
  } else if( splitlvl == "" ) {
    return " \0 ";
  }
  return c;
}

// Split statement into (pseudo-)opcode and params.
var function splitstmt(stmt) {
  // Convert label with trailing-colon into .label statement.
  var label = match(stmt, "^%s*(.+):%s*$");
  if( label ) { return ".label", {label}; }

  // Split at commas and equal signs, but obey parentheses and brackets.
  splitlvl = "";
  stmt = gsub(stmt, "[,%(%)%[%]{}]", splitstmt_one);
  if( splitlvl != "" ) { werror("unbalanced () or []"); }

  // Split off opcode.
  var op, other = match(stmt, "^%s*([^%s%z]+)%s*(.*)$");
  if( ! op ) { werror("bad statement syntax"); }

  // Split parameters.
  var params = {};
  for( p in gmatch(other, "%s*(%Z+)%z?") ) {
    params[#params+1] = gsub(p, "%s+$", "");
  }
  if( #params > 16 ) { werror("too many parameters"); }

  params.op = op;
  return op, params;
}

// Process a single statement.
dostmt = function(stmt) {
  // Ignore empty statements.
  if( match(stmt, "^%s*$") ) { return; }

  // Capture macro defs before substitution.
  if( mac_capture ) { return mac_capture(stmt); }
  stmt = definesubst(stmt);

  // Emit C code without parsing the line.
  if( sub(stmt, 1, 1) == "|" ) {
    var tail = sub(stmt, 2);
    wflush();
    if( sub(tail, 1, 2) == "//" ) { wcomment(tail); } else { wline(tail, true); }
    return;
  }

  // Split into (pseudo-)opcode and params.
  var op, params = splitstmt(stmt);

  // Get opcode handler (matching # of parameters or generic handler).
  var f = map_op[op.."_"..#params] || map_op[op.."_*"];
  if( ! f ) {
    if( ! g_arch ) { wfatal("first statement must be .arch"); }
    // Improve error report.
    for( i=0,9 ) {
      if( map_op[op.."_"..i] ) {
	werror("wrong number of parameters for `"..op.."'");
      }
    }
    werror("unknown statement `"..op.."'");
  }

  // Call opcode handler or special handler for template strings.
  if( type(f) == "string" ) {
    map_op[".template__"](params, f);
  } else {
    f(params);
  }
};

// Process a single line.
var function doline(line) {
  if( g_opt.flushline ) { wflush(); }

  // Assembler line?
  var indent, aline = match(line, "^(%s*)%|(.*)$");
  if( ! aline ) {
    // No, plain C code line, need to flush first.
    wflush();
    wsync();
    wline(line, false);
    return;
  }

  g_indent = indent; // Remember current line indentation.

  // Emit C code (even from macros). Avoids echo and line parsing.
  if( sub(aline, 1, 1) == "|" ) {
    if( ! mac_capture ) {
      wsync();
    } else if( g_opt.comment ) {
      wsync();
      wcomment(aline);
    }
    dostmt(aline);
    return;
  }

  // Echo assembler line as a comment.
  if( g_opt.comment ) {
    wsync();
    wcomment(aline);
  }

  // Strip assembler comments.
  aline = gsub(aline, "//.*$", "");

  // Split line into statements at semicolons.
  if( match(aline, ";") ) {
    for( stmt in gmatch(aline, "[^;]+") ) { dostmt(stmt); }
  } else {
    dostmt(aline);
  }
}

//----------------------------------------------------------------------------

// Write DynASM header.
var function dasmhead(out) {
  out->write(format([=[
/*
** This file has been pre-processed with DynASM.
** %s
** DynASM version %s, DynASM %s version %s
** DO NOT EDIT! The original file is in "%s".
*/

]=], _info.url,
    _info.version, g_arch._info.arch, g_arch._info.version,
    g_fname));
}

// Read input file.
readfile = function(fin) {
  g_indent = "";
  g_lineno = 0;
  g_synclineno = -1;

  // Process all lines.
  for( line in fin->lines() ) {
    g_lineno +=   1;
    g_curline = line;
    var ok, err = pcall(doline, line);
    if( ! ok && wprinterr(err, "\n") ) { return true; }
  }
  wflush();

  // Close input file.
  assert(fin == stdin || fin->close());
};

// Write output file.
var function writefile(outfile) {
  var fout;

  // Open output file.
  if( outfile == null || outfile == "-" ) {
    fout = stdout;
  } else {
    fout = assert(io.open(outfile, "w"));
  }

  // Write all buffered lines
  wdumplines(fout, g_wbuffer);

  // Close output file.
  assert(fout == stdout || fout->close());

  // Optionally dump definitions.
  dumpdef(fout == stdout && stderr || stdout);
}

// Translate an input file to an output file.
var function translate(infile, outfile) {
  g_wbuffer = {};
  g_indent = "";
  g_lineno = 0;
  g_synclineno = -1;

  // Put header.
  wline(dasmhead);

  // Read input file.
  var fin;
  if( infile == "-" ) {
    g_fname = "(stdin)";
    fin = stdin;
  } else {
    g_fname = infile;
    fin = assert(io.open(infile, "r"));
  }
  readfile(fin);

  // Check for errors.
  if( ! g_arch ) {
    wprinterr(g_fname, ":*: error: missing .arch directive\n");
  }
  checkconds();
  checkmacros();
  checkcaptures();

  if( g_errcount != 0 ) {
    stderr->write(g_fname, ":*: info: ", g_errcount, " error",
      (type(g_errcount) == "number" && g_errcount > 1) && "s" || "",
      " in input file -- no output file generated.\n");
    dumpdef(stderr);
    exit(1);
  }

  // Write output file.
  writefile(outfile);
}

//----------------------------------------------------------------------------

// Print help text.
function opt_map.help() {
  stdout->write("DynASM -- ", _info.description, ".\n");
  stdout->write("DynASM ", _info.version, " ", _info.release, "  ", _info.url, "\n");
  stdout->write([=[

Usage: dynasm [OPTION]... INFILE.dasc|-

  -h, --help           Display this help text.
  -V, --version        Display version and copyright information.

  -o, --outfile FILE   Output file name (default is stdout).
  -I, --include DIR    Add directory to the include search path.

  -c, --ccomment       Use /* */ comments for assembler lines.
  -C, --cppcomment     Use // comments for assembler lines (default).
  -N, --nocomment      Suppress assembler lines in output.
  -M, --maccomment     Show macro expansions as comments (default off).

  -L, --nolineno       Suppress CPP line number information in output.
  -F, --flushline      Flush action list for every line.

  -D NAME[=SUBST]      Define a substitution.
  -U NAME              Undefine a substitution.

  -P, --dumpdef        Dump defines, macros, etc. Repeat for more output.
  -A, --dumparch ARCH  Load architecture ARCH and dump description.
]=]);
  exit(0);
}

// Print version information.
function opt_map.version() {
  stdout->write(format("%s version %s, released %s\n%s\n\n%s",
    _info.name, _info.version, _info.release, _info.url, _info.copyright));
  exit(0);
}

// Misc. options.
function opt_map.outfile(args) { g_opt.outfile = optparam(args); }
function opt_map.include(args) { insert(g_opt.include, 1, optparam(args)); }
function opt_map.ccomment() { g_opt.comment = "/*|"; g_opt.endcomment = " */"; }
function opt_map.cppcomment() { g_opt.comment = "//|"; g_opt.endcomment = ""; }
function opt_map.nocomment() { g_opt.comment = false; }
function opt_map.maccomment() { g_opt.maccomment = true; }
function opt_map.nolineno() { g_opt.cpp = false; }
function opt_map.flushline() { g_opt.flushline = true; }
function opt_map.dumpdef() { g_opt.dumpdef = g_opt.dumpdef + 1; }

//----------------------------------------------------------------------------

// Short aliases for long options.
var opt_alias = {
  h = "help", ["?"] = "help", V = "version",
  o = "outfile", I = "include",
  c = "ccomment", C = "cppcomment", N = "nocomment", M = "maccomment",
  L = "nolineno", F = "flushline",
  P = "dumpdef", A = "dumparch",
};

// Parse single option.
var function parseopt(opt, args) {
  opt_current = #opt == 1 && "-"..opt || "--"..opt;
  var f = opt_map[opt] || opt_map[opt_alias[opt]];
  if( ! f ) {
    opterror("unrecognized option `", opt_current, "'. Try `--help'.\n");
  }
  f(args);
}

// Parse arguments.
var function parseargs(args) {
  // Default options.
  g_opt.comment = "//|";
  g_opt.endcomment = "";
  g_opt.cpp = true;
  g_opt.dumpdef = 0;
  g_opt.include = { "" };

  // Process all option arguments.
  args.argn = 1;
  do {
    var a = args[args.argn];
    if( ! a ) { break; }
    var lopt, opt = match(a, "^%-(%-?)(.+)");
    if( ! opt ) { break; }
    args.argn = args.argn + 1;
    if( lopt == "" ) {
      // Loop through short options.
      for( o in gmatch(opt, ".") ) { parseopt(o, args); }
    } else {
      // Long option.
      parseopt(opt, args);
    }
  } while(!( false) );

  // Check for proper number of arguments.
  var nargs = #args - args.argn + 1;
  if( nargs != 1 ) {
    if( nargs == 0 ) {
      if( g_opt.dumpdef > 0 ) { return dumpdef(stdout); }
    }
    opt_map.help();
  }

  // Translate a single input file to a single output file
  // TODO: Handle multiple files?
  translate(args[args.argn], g_opt.outfile);
}

//----------------------------------------------------------------------------

// Add the directory dynasm.ljs resides in to the Lua module search path.
var arg = arg;
if( arg && arg[0] ) {
  prefix = match(arg[0], "^(.*[/\\])");
  if( package && prefix ) { package.path = prefix.."?.ljs;"..package.path; }
}

// Start DynASM.
parseargs({...});

//----------------------------------------------------------------------------

