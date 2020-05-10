//----------------------------------------------------------------------------
// DynASM ARM module.
//
// Copyright (C) 2005-2020 Mike Pall. All rights reserved.
// See dynasm.lua for full copyright notice.
//----------------------------------------------------------------------------

// Module information:
var _info = {
  arch =	"arm",
  description =	"DynASM ARM module",
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
  "REL_PC", "LABEL_PC", "IMM", "IMM12", "IMM16", "IMML8", "IMML12", "IMMV8",
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
var map_archdef = { sp = "r13", lr = "r14", pc = "r15", };

// Int. register name -> ext. name.
var map_reg_rev = { r13 = "sp", r14 = "lr", r15 = "pc", };

var map_type = {};		// Type name -> { ctype, reg }
var ctypenum = 0;		// Type number (for Dt... macros).

// Reverse defines for registers.
function _M.revdef(s) {
  return map_reg_rev[s] || s;
}

var map_shift = { lsl = 0, lsr = 1, asr = 2, ror = 3, };

var map_cond = {
  eq = 0, ne = 1, cs = 2, cc = 3, mi = 4, pl = 5, vs = 6, vc = 7,
  hi = 8, ls = 9, ge = 10, lt = 11, gt = 12, le = 13, al = 14,
  hs = 2, lo = 3,
};

//----------------------------------------------------------------------------

// Template strings for ARM instructions.
var map_op = {
  // Basic data processing instructions.
  and_3 = "e0000000DNPs",
  eor_3 = "e0200000DNPs",
  sub_3 = "e0400000DNPs",
  rsb_3 = "e0600000DNPs",
  add_3 = "e0800000DNPs",
  adc_3 = "e0a00000DNPs",
  sbc_3 = "e0c00000DNPs",
  rsc_3 = "e0e00000DNPs",
  tst_2 = "e1100000NP",
  teq_2 = "e1300000NP",
  cmp_2 = "e1500000NP",
  cmn_2 = "e1700000NP",
  orr_3 = "e1800000DNPs",
  mov_2 = "e1a00000DPs",
  bic_3 = "e1c00000DNPs",
  mvn_2 = "e1e00000DPs",

  and_4 = "e0000000DNMps",
  eor_4 = "e0200000DNMps",
  sub_4 = "e0400000DNMps",
  rsb_4 = "e0600000DNMps",
  add_4 = "e0800000DNMps",
  adc_4 = "e0a00000DNMps",
  sbc_4 = "e0c00000DNMps",
  rsc_4 = "e0e00000DNMps",
  tst_3 = "e1100000NMp",
  teq_3 = "e1300000NMp",
  cmp_3 = "e1500000NMp",
  cmn_3 = "e1700000NMp",
  orr_4 = "e1800000DNMps",
  mov_3 = "e1a00000DMps",
  bic_4 = "e1c00000DNMps",
  mvn_3 = "e1e00000DMps",

  lsl_3 = "e1a00000DMws",
  lsr_3 = "e1a00020DMws",
  asr_3 = "e1a00040DMws",
  ror_3 = "e1a00060DMws",
  rrx_2 = "e1a00060DMs",

  // Multiply and multiply-accumulate.
  mul_3 = "e0000090NMSs",
  mla_4 = "e0200090NMSDs",
  umaal_4 = "e0400090DNMSs",	// v6
  mls_4 = "e0600090DNMSs",	// v6T2
  umull_4 = "e0800090DNMSs",
  umlal_4 = "e0a00090DNMSs",
  smull_4 = "e0c00090DNMSs",
  smlal_4 = "e0e00090DNMSs",

  // Halfword multiply and multiply-accumulate.
  smlabb_4 = "e1000080NMSD",	// v5TE
  smlatb_4 = "e10000a0NMSD",	// v5TE
  smlabt_4 = "e10000c0NMSD",	// v5TE
  smlatt_4 = "e10000e0NMSD",	// v5TE
  smlawb_4 = "e1200080NMSD",	// v5TE
  smulwb_3 = "e12000a0NMS",	// v5TE
  smlawt_4 = "e12000c0NMSD",	// v5TE
  smulwt_3 = "e12000e0NMS",	// v5TE
  smlalbb_4 = "e1400080NMSD",	// v5TE
  smlaltb_4 = "e14000a0NMSD",	// v5TE
  smlalbt_4 = "e14000c0NMSD",	// v5TE
  smlaltt_4 = "e14000e0NMSD",	// v5TE
  smulbb_3 = "e1600080NMS",	// v5TE
  smultb_3 = "e16000a0NMS",	// v5TE
  smulbt_3 = "e16000c0NMS",	// v5TE
  smultt_3 = "e16000e0NMS",	// v5TE

  // Miscellaneous data processing instructions.
  clz_2 = "e16f0f10DM", // v5T
  rev_2 = "e6bf0f30DM", // v6
  rev16_2 = "e6bf0fb0DM", // v6
  revsh_2 = "e6ff0fb0DM", // v6
  sel_3 = "e6800fb0DNM", // v6
  usad8_3 = "e780f010NMS", // v6
  usada8_4 = "e7800010NMSD", // v6
  rbit_2 = "e6ff0f30DM", // v6T2
  movw_2 = "e3000000DW", // v6T2
  movt_2 = "e3400000DW", // v6T2
  // Note: the X encodes width-1, not width.
  sbfx_4 = "e7a00050DMvX", // v6T2
  ubfx_4 = "e7e00050DMvX", // v6T2
  // Note: the X encodes the msb field, not the width.
  bfc_3 = "e7c0001fDvX", // v6T2
  bfi_4 = "e7c00010DMvX", // v6T2

  // Packing and unpacking instructions.
  pkhbt_3 = "e6800010DNM", pkhbt_4 = "e6800010DNMv", // v6
  pkhtb_3 = "e6800050DNM", pkhtb_4 = "e6800050DNMv", // v6
  sxtab_3 = "e6a00070DNM", sxtab_4 = "e6a00070DNMv", // v6
  sxtab16_3 = "e6800070DNM", sxtab16_4 = "e6800070DNMv", // v6
  sxtah_3 = "e6b00070DNM", sxtah_4 = "e6b00070DNMv", // v6
  sxtb_2 = "e6af0070DM", sxtb_3 = "e6af0070DMv", // v6
  sxtb16_2 = "e68f0070DM", sxtb16_3 = "e68f0070DMv", // v6
  sxth_2 = "e6bf0070DM", sxth_3 = "e6bf0070DMv", // v6
  uxtab_3 = "e6e00070DNM", uxtab_4 = "e6e00070DNMv", // v6
  uxtab16_3 = "e6c00070DNM", uxtab16_4 = "e6c00070DNMv", // v6
  uxtah_3 = "e6f00070DNM", uxtah_4 = "e6f00070DNMv", // v6
  uxtb_2 = "e6ef0070DM", uxtb_3 = "e6ef0070DMv", // v6
  uxtb16_2 = "e6cf0070DM", uxtb16_3 = "e6cf0070DMv", // v6
  uxth_2 = "e6ff0070DM", uxth_3 = "e6ff0070DMv", // v6

  // Saturating instructions.
  qadd_3 = "e1000050DMN",	// v5TE
  qsub_3 = "e1200050DMN",	// v5TE
  qdadd_3 = "e1400050DMN",	// v5TE
  qdsub_3 = "e1600050DMN",	// v5TE
  // Note: the X for ssat* encodes sat_imm-1, not sat_imm.
  ssat_3 = "e6a00010DXM", ssat_4 = "e6a00010DXMp", // v6
  usat_3 = "e6e00010DXM", usat_4 = "e6e00010DXMp", // v6
  ssat16_3 = "e6a00f30DXM", // v6
  usat16_3 = "e6e00f30DXM", // v6

  // Parallel addition and subtraction.
  sadd16_3 = "e6100f10DNM", // v6
  sasx_3 = "e6100f30DNM", // v6
  ssax_3 = "e6100f50DNM", // v6
  ssub16_3 = "e6100f70DNM", // v6
  sadd8_3 = "e6100f90DNM", // v6
  ssub8_3 = "e6100ff0DNM", // v6
  qadd16_3 = "e6200f10DNM", // v6
  qasx_3 = "e6200f30DNM", // v6
  qsax_3 = "e6200f50DNM", // v6
  qsub16_3 = "e6200f70DNM", // v6
  qadd8_3 = "e6200f90DNM", // v6
  qsub8_3 = "e6200ff0DNM", // v6
  shadd16_3 = "e6300f10DNM", // v6
  shasx_3 = "e6300f30DNM", // v6
  shsax_3 = "e6300f50DNM", // v6
  shsub16_3 = "e6300f70DNM", // v6
  shadd8_3 = "e6300f90DNM", // v6
  shsub8_3 = "e6300ff0DNM", // v6
  uadd16_3 = "e6500f10DNM", // v6
  uasx_3 = "e6500f30DNM", // v6
  usax_3 = "e6500f50DNM", // v6
  usub16_3 = "e6500f70DNM", // v6
  uadd8_3 = "e6500f90DNM", // v6
  usub8_3 = "e6500ff0DNM", // v6
  uqadd16_3 = "e6600f10DNM", // v6
  uqasx_3 = "e6600f30DNM", // v6
  uqsax_3 = "e6600f50DNM", // v6
  uqsub16_3 = "e6600f70DNM", // v6
  uqadd8_3 = "e6600f90DNM", // v6
  uqsub8_3 = "e6600ff0DNM", // v6
  uhadd16_3 = "e6700f10DNM", // v6
  uhasx_3 = "e6700f30DNM", // v6
  uhsax_3 = "e6700f50DNM", // v6
  uhsub16_3 = "e6700f70DNM", // v6
  uhadd8_3 = "e6700f90DNM", // v6
  uhsub8_3 = "e6700ff0DNM", // v6

  // Load/store instructions.
  str_2 = "e4000000DL", str_3 = "e4000000DL", str_4 = "e4000000DL",
  strb_2 = "e4400000DL", strb_3 = "e4400000DL", strb_4 = "e4400000DL",
  ldr_2 = "e4100000DL", ldr_3 = "e4100000DL", ldr_4 = "e4100000DL",
  ldrb_2 = "e4500000DL", ldrb_3 = "e4500000DL", ldrb_4 = "e4500000DL",
  strh_2 = "e00000b0DL", strh_3 = "e00000b0DL",
  ldrh_2 = "e01000b0DL", ldrh_3 = "e01000b0DL",
  ldrd_2 = "e00000d0DL", ldrd_3 = "e00000d0DL", // v5TE
  ldrsb_2 = "e01000d0DL", ldrsb_3 = "e01000d0DL",
  strd_2 = "e00000f0DL", strd_3 = "e00000f0DL", // v5TE
  ldrsh_2 = "e01000f0DL", ldrsh_3 = "e01000f0DL",

  ldm_2 = "e8900000oR", ldmia_2 = "e8900000oR", ldmfd_2 = "e8900000oR",
  ldmda_2 = "e8100000oR", ldmfa_2 = "e8100000oR",
  ldmdb_2 = "e9100000oR", ldmea_2 = "e9100000oR",
  ldmib_2 = "e9900000oR", ldmed_2 = "e9900000oR",
  stm_2 = "e8800000oR", stmia_2 = "e8800000oR", stmfd_2 = "e8800000oR",
  stmda_2 = "e8000000oR", stmfa_2 = "e8000000oR",
  stmdb_2 = "e9000000oR", stmea_2 = "e9000000oR",
  stmib_2 = "e9800000oR", stmed_2 = "e9800000oR",
  pop_1 = "e8bd0000R", push_1 = "e92d0000R",

  // Branch instructions.
  b_1 = "ea000000B",
  bl_1 = "eb000000B",
  blx_1 = "e12fff30C",
  bx_1 = "e12fff10M",

  // Miscellaneous instructions.
  nop_0 = "e1a00000",
  mrs_1 = "e10f0000D",
  bkpt_1 = "e1200070K", // v5T
  svc_1 = "ef000000T", swi_1 = "ef000000T",
  ud_0 = "e7f001f0",

  // VFP instructions.
  ["vadd.f32_3"] = "ee300a00dnm",
  ["vadd.f64_3"] = "ee300b00Gdnm",
  ["vsub.f32_3"] = "ee300a40dnm",
  ["vsub.f64_3"] = "ee300b40Gdnm",
  ["vmul.f32_3"] = "ee200a00dnm",
  ["vmul.f64_3"] = "ee200b00Gdnm",
  ["vnmul.f32_3"] = "ee200a40dnm",
  ["vnmul.f64_3"] = "ee200b40Gdnm",
  ["vmla.f32_3"] = "ee000a00dnm",
  ["vmla.f64_3"] = "ee000b00Gdnm",
  ["vmls.f32_3"] = "ee000a40dnm",
  ["vmls.f64_3"] = "ee000b40Gdnm",
  ["vnmla.f32_3"] = "ee100a40dnm",
  ["vnmla.f64_3"] = "ee100b40Gdnm",
  ["vnmls.f32_3"] = "ee100a00dnm",
  ["vnmls.f64_3"] = "ee100b00Gdnm",
  ["vdiv.f32_3"] = "ee800a00dnm",
  ["vdiv.f64_3"] = "ee800b00Gdnm",

  ["vabs.f32_2"] = "eeb00ac0dm",
  ["vabs.f64_2"] = "eeb00bc0Gdm",
  ["vneg.f32_2"] = "eeb10a40dm",
  ["vneg.f64_2"] = "eeb10b40Gdm",
  ["vsqrt.f32_2"] = "eeb10ac0dm",
  ["vsqrt.f64_2"] = "eeb10bc0Gdm",
  ["vcmp.f32_2"] = "eeb40a40dm",
  ["vcmp.f64_2"] = "eeb40b40Gdm",
  ["vcmpe.f32_2"] = "eeb40ac0dm",
  ["vcmpe.f64_2"] = "eeb40bc0Gdm",
  ["vcmpz.f32_1"] = "eeb50a40d",
  ["vcmpz.f64_1"] = "eeb50b40Gd",
  ["vcmpze.f32_1"] = "eeb50ac0d",
  ["vcmpze.f64_1"] = "eeb50bc0Gd",

  vldr_2 = "ed100a00dl|ed100b00Gdl",
  vstr_2 = "ed000a00dl|ed000b00Gdl",
  vldm_2 = "ec900a00or",
  vldmia_2 = "ec900a00or",
  vldmdb_2 = "ed100a00or",
  vpop_1 = "ecbd0a00r",
  vstm_2 = "ec800a00or",
  vstmia_2 = "ec800a00or",
  vstmdb_2 = "ed000a00or",
  vpush_1 = "ed2d0a00r",

  ["vmov.f32_2"] = "eeb00a40dm|eeb00a00dY",	// #imm is VFPv3 only
  ["vmov.f64_2"] = "eeb00b40Gdm|eeb00b00GdY",	// #imm is VFPv3 only
  vmov_2 = "ee100a10Dn|ee000a10nD",
  vmov_3 = "ec500a10DNm|ec400a10mDN|ec500b10GDNm|ec400b10GmDN",

  vmrs_0 = "eef1fa10",
  vmrs_1 = "eef10a10D",
  vmsr_1 = "eee10a10D",

  ["vcvt.s32.f32_2"] = "eebd0ac0dm",
  ["vcvt.s32.f64_2"] = "eebd0bc0dGm",
  ["vcvt.u32.f32_2"] = "eebc0ac0dm",
  ["vcvt.u32.f64_2"] = "eebc0bc0dGm",
  ["vcvtr.s32.f32_2"] = "eebd0a40dm",
  ["vcvtr.s32.f64_2"] = "eebd0b40dGm",
  ["vcvtr.u32.f32_2"] = "eebc0a40dm",
  ["vcvtr.u32.f64_2"] = "eebc0b40dGm",
  ["vcvt.f32.s32_2"] = "eeb80ac0dm",
  ["vcvt.f64.s32_2"] = "eeb80bc0GdFm",
  ["vcvt.f32.u32_2"] = "eeb80a40dm",
  ["vcvt.f64.u32_2"] = "eeb80b40GdFm",
  ["vcvt.f32.f64_2"] = "eeb70bc0dGm",
  ["vcvt.f64.f32_2"] = "eeb70ac0GdFm",

  // VFPv4 only:
  ["vfma.f32_3"] = "eea00a00dnm",
  ["vfma.f64_3"] = "eea00b00Gdnm",
  ["vfms.f32_3"] = "eea00a40dnm",
  ["vfms.f64_3"] = "eea00b40Gdnm",
  ["vfnma.f32_3"] = "ee900a40dnm",
  ["vfnma.f64_3"] = "ee900b40Gdnm",
  ["vfnms.f32_3"] = "ee900a00dnm",
  ["vfnms.f64_3"] = "ee900b00Gdnm",

  // NYI: Advanced SIMD instructions.

  // NYI: I have no need for these instructions right now:
  // swp, swpb, strex, ldrex, strexd, ldrexd, strexb, ldrexb, strexh, ldrexh
  // msr, nopv6, yield, wfe, wfi, sev, dbg, bxj, smc, srs, rfe
  // cps, setend, pli, pld, pldw, clrex, dsb, dmb, isb
  // stc, ldc, mcr, mcr2, mrc, mrc2, mcrr, mcrr2, mrrc, mrrc2, cdp, cdp2
};

// Add mnemonics for "s" variants.
{
  var t = {};
  for( k,v in pairs(map_op) ) {
    if( sub(v, -1) == "s" ) {
      var v2 = sub(v, 1, 2)..char(byte(v, 3)+1)..sub(v, 4, -2);
      t[sub(k, 1, -3).."s"..sub(k, -2)] = v2;
    }
  }
  for( k,v in pairs(t) ) {
    map_op[k] = v;
  }
}

//----------------------------------------------------------------------------

var function parse_gpr(expr) {
  var tname, ovreg = match(expr, "^([%w_]+):(r1?[0-9])$");
  var tp = map_type[tname || expr];
  if( tp ) {
    var reg = ovreg || tp.reg;
    if( ! reg ) {
      werror("type `"..(tname || expr).."' needs a register override");
    }
    expr = reg;
  }
  var r = match(expr, "^r(1?[0-9])$");
  if( r ) {
    r = tonumber(r);
    if( r <= 15 ) { return r, tp; }
  }
  werror("bad register name `"..expr.."'");
}

var function parse_gpr_pm(expr) {
  var pm, expr2 = match(expr, "^([+-]?)(.*)$");
  return parse_gpr(expr2), (pm == "-");
}

var function parse_vr(expr, tp) {
  var t, r = match(expr, "^([sd])([0-9]+)$");
  if( t == tp ) {
    r = tonumber(r);
    if( r <= 31 ) {
      if( t == "s" ) { return shr(r, 1), band(r, 1); }
      return band(r, 15), shr(r, 4);
    }
  }
  werror("bad register name `"..expr.."'");
}

var function parse_reglist(reglist) {
  reglist = match(reglist, "^{%s*([^}]*)}$");
  if( ! reglist ) { werror("register list expected"); }
  var rr = 0;
  for( p in gmatch(reglist..",", "%s*([^,]*),") ) {
    var rbit = shl(1, parse_gpr(gsub(p, "%s+$", "")));
    if( band(rr, rbit) != 0 ) {
      werror("duplicate register `"..p.."'");
    }
    rr +=   rbit;
  }
  return rr;
}

var function parse_vrlist(reglist) {
  var ta, ra, tb, rb = match(reglist,
			   "^{%s*([sd])([0-9]+)%s*%-%s*([sd])([0-9]+)%s*}$");
  ra, rb = tonumber(ra), tonumber(rb);
  if( ta && ta == tb && ra && rb && ra <= 31 && rb <= 31 && ra <= rb ) {
    var nr = rb+1 - ra;
    if( ta == "s" ) {
      return shl(shr(ra,1),12)+shl(band(ra,1),22) + nr;
    } else {
      return shl(band(ra,15),12)+shl(shr(ra,4),22) + nr*2 + 0x100;
    }
  }
  werror("register list expected");
}

var function parse_imm(imm, bits, shift, scale, signed) {
  imm = match(imm, "^#(.*)$");
  if( ! imm ) { werror("expected immediate operand"); }
  var n = tonumber(imm);
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
  var n = tonumber(imm);
  if( n ) {
    var m = band(n);
    for( i=0,-15,-1 ) {
      if( shr(m, 8) == 0 ) { return m + shl(band(i, 15), 8); }
      m = ror(m, 2);
    }
    werror("out of range immediate `"..imm.."'");
  } else {
    waction("IMM12", 0, imm);
    return 0;
  }
}

var function parse_imm16(imm) {
  imm = match(imm, "^#(.*)$");
  if( ! imm ) { werror("expected immediate operand"); }
  var n = tonumber(imm);
  if( n ) {
    if( shr(n, 16) == 0 ) { return band(n, 0x0fff) + shl(band(n, 0xf000), 4); }
    werror("out of range immediate `"..imm.."'");
  } else {
    waction("IMM16", 32*16, imm);
    return 0;
  }
}

var function parse_imm_load(imm, ext) {
  var n = tonumber(imm);
  if( n ) {
    if( ext ) {
      if( n >= -255 && n <= 255 ) {
	var up = 0x00800000;
	if( n < 0 ) { n = -n; up = 0; }
	return shl(band(n, 0xf0), 4) + band(n, 0x0f) + up;
      }
    } else {
      if( n >= -4095 && n <= 4095 ) {
	if( n >= 0 ) { return n+0x00800000; }
	return -n;
      }
    }
    werror("out of range immediate `"..imm.."'");
  } else {
    waction(ext && "IMML8" || "IMML12", 32768 + shl(ext && 8 || 12, 5), imm);
    return 0;
  }
}

var function parse_shift(shift, gprok) {
  if( shift == "rrx" ) {
    return 3 * 32;
  } else {
    var s, s2 = match(shift, "^(%S+)%s*(.*)$");
    s = map_shift[s];
    if( ! s ) { werror("expected shift operand"); }
    if( sub(s2, 1, 1) == "#" ) {
      return parse_imm(s2, 5, 7, 0, false) + shl(s, 5);
    } else {
      if( ! gprok ) { werror("expected immediate shift operand"); }
      return shl(parse_gpr(s2), 8) + shl(s, 5) + 16;
    }
  }
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

var function parse_load(params, nparams, n, op) {
  var oplo = band(op, 255);
  var ext, ldrd = (oplo != 0), (oplo == 208);
  var d;
  if( (ldrd || oplo == 240) ) {
    d = band(shr(op, 12), 15);
    if( band(d, 1) != 0 ) { werror("odd destination register"); }
  }
  var pn = params[n];
  var p1, wb = match(pn, "^%[%s*(.-)%s*%](!?)$");
  var p2 = params[n+1];
  if( ! p1 ) {
    if( ! p2 ) {
      if( match(pn, "^[<>=%-]") || match(pn, "^extern%s+") ) {
	var mode, mn, s = parse_label(pn, false);
	waction("REL_"..mode, mn + (ext && 0x1800 || 0x0800), s, 1);
	return op + 15 * 65536 + 0x01000000 + (ext && 0x00400000 || 0);
      }
      var reg, tailr = match(pn, "^([%w_:]+)%s*(.*)$");
      if( reg && tailr != "" ) {
	var dp, tp = parse_gpr(reg);
	if( tp ) {
	  waction(ext && "IMML8" || "IMML12", 32768 + 32*(ext && 8 || 12),
		  format(tp.ctypefmt, tailr));
	  return op + shl(dp, 16) + 0x01000000 + (ext && 0x00400000 || 0);
	}
      }
    }
    werror("expected address operand");
  }
  if( wb == "!" ) { op +=   0x00200000; }
  if( p2 ) {
    if( wb == "!" ) { werror("bad use of '!'"); }
    var p3 = params[n+2];
    op +=   shl(parse_gpr(p1), 16);
    var imm = match(p2, "^#(.*)$");
    if( imm ) {
      var m = parse_imm_load(imm, ext);
      if( p3 ) { werror("too many parameters"); }
      op +=   m + (ext && 0x00400000 || 0);
    } else {
      var m, neg = parse_gpr_pm(p2);
      if( ldrd && (m == d || m-1 == d) ) { werror("register conflict"); }
      op +=   m + (neg && 0 || 0x00800000) + (ext && 0 || 0x02000000);
      if( p3 ) { op +=   parse_shift(p3); }
    }
  } else {
    var p1a;
    p1a, p2 = match(p1, "^([^,%s]*)%s*(.*)$");
    op +=   shl(parse_gpr(p1a), 16) + 0x01000000;
    if( p2 != "" ) {
      var imm = match(p2, "^,%s*#(.*)$");
      if( imm ) {
	var m = parse_imm_load(imm, ext);
	op +=   m + (ext && 0x00400000 || 0);
      } else {
	var p2a, p3 = match(p2, "^,%s*([^,%s]*)%s*,?%s*(.*)$");
	var m, neg = parse_gpr_pm(p2a);
	if( ldrd && (m == d || m-1 == d) ) { werror("register conflict"); }
	op +=   m + (neg && 0 || 0x00800000) + (ext && 0 || 0x02000000);
	if( p3 != "" ) {
	  if( ext ) { werror("too many parameters"); }
	  op +=   parse_shift(p3);
	}
      }
    } else {
      if( wb == "!" ) { werror("bad use of '!'"); }
      op +=   (ext && 0x00c00000 || 0x00800000);
    }
  }
  return op;
}

var function parse_vload(q) {
  var reg, imm = match(q, "^%[%s*([^,%s]*)%s*(.*)%]$");
  if( reg ) {
    var d = shl(parse_gpr(reg), 16);
    if( imm == "" ) { return d; }
    imm = match(imm, "^,%s*#(.*)$");
    if( imm ) {
      var n = tonumber(imm);
      if( n ) {
	if( n >= -1020 && n <= 1020 && n%4 == 0 ) {
	  return d + (n >= 0 && n/4+0x00800000 || -n/4);
	}
	werror("out of range immediate `"..imm.."'");
      } else {
	waction("IMMV8", 32768 + 32*8, imm);
	return d;
      }
    }
  } else {
    if( match(q, "^[<>=%-]") || match(q, "^extern%s+") ) {
      var mode, n, s = parse_label(q, false);
      waction("REL_"..mode, n + 0x2800, s, 1);
      return 15 * 65536;
    }
    var tailr;
    reg, tailr = match(q, "^([%w_:]+)%s*(.*)$");
    if( reg && tailr != "" ) {
      var d, tp = parse_gpr(reg);
      if( tp ) {
	waction("IMMV8", 32768 + 32*8, format(tp.ctypefmt, tailr));
	return shl(d, 16);
      }
    }
  }
  werror("expected address operand");
}

//----------------------------------------------------------------------------

// Handle opcodes defined with template strings.
var function parse_template(params, template, nparams, pos) {
  var op = tonumber(sub(template, 1, 8), 16);
  var n = 1;
  var vr = "s";

  // Process each character.
  for( p in gmatch(sub(template, 9), ".") ) {
    var q = params[n];
    if( p == "D" ) {
      op +=   shl(parse_gpr(q), 12); n +=   1;
    } else if( p == "N" ) {
      op +=   shl(parse_gpr(q), 16); n +=   1;
    } else if( p == "S" ) {
      op +=   shl(parse_gpr(q), 8); n +=   1;
    } else if( p == "M" ) {
      op +=   parse_gpr(q); n +=   1;
    } else if( p == "d" ) {
      var r,h = parse_vr(q, vr); op += shl(r,12)+shl(h,22); n +=   1;
    } else if( p == "n" ) {
      var r,h = parse_vr(q, vr); op += shl(r,16)+shl(h,7); n +=   1;
    } else if( p == "m" ) {
      var r,h = parse_vr(q, vr); op += r+shl(h,5); n +=   1;
    } else if( p == "P" ) {
      var imm = match(q, "^#(.*)$");
      if( imm ) {
	op +=   parse_imm12(imm) + 0x02000000;
      } else {
	op +=   parse_gpr(q);
      }
      n +=   1;
    } else if( p == "p" ) {
      op +=   parse_shift(q, true); n +=   1;
    } else if( p == "L" ) {
      op = parse_load(params, nparams, n, op);
    } else if( p == "l" ) {
      op +=   parse_vload(q);
    } else if( p == "B" ) {
      var mode, mn, s = parse_label(q, false);
      waction("REL_"..mode, mn, s, 1);
    } else if( p == "C" ) { // blx gpr vs. blx label.
      if( match(q, "^([%w_]+):(r1?[0-9])$") || match(q, "^r(1?[0-9])$") ) {
	op +=   parse_gpr(q);
      } else {
	if( op < 0xe0000000 ) { werror("unconditional instruction"); }
	var mode, mn, s = parse_label(q, false);
	waction("REL_"..mode, mn, s, 1);
	op = 0xfa000000;
      }
    } else if( p == "F" ) {
      vr = "s";
    } else if( p == "G" ) {
      vr = "d";
    } else if( p == "o" ) {
      var r, wb = match(q, "^([^!]*)(!?)$");
      op +=   shl(parse_gpr(r), 16) + (wb == "!" && 0x00200000 || 0);
      n +=   1;
    } else if( p == "R" ) {
      op +=   parse_reglist(q); n +=   1;
    } else if( p == "r" ) {
      op +=   parse_vrlist(q); n +=   1;
    } else if( p == "W" ) {
      op +=   parse_imm16(q); n +=   1;
    } else if( p == "v" ) {
      op +=   parse_imm(q, 5, 7, 0, false); n +=   1;
    } else if( p == "w" ) {
      var imm = match(q, "^#(.*)$");
      if( imm ) {
	op +=   parse_imm(q, 5, 7, 0, false); n +=   1;
      } else {
	op +=   shl(parse_gpr(q), 8) + 16;
      }
    } else if( p == "X" ) {
      op +=   parse_imm(q, 5, 16, 0, false); n +=   1;
    } else if( p == "Y" ) {
      var imm = tonumber(match(q, "^#(.*)$")); n +=   1;
      if( ! imm || shr(imm, 8) != 0 ) {
	werror("bad immediate operand");
      }
      op +=   shl(band(imm, 0xf0), 12) + band(imm, 0x0f);
    } else if( p == "K" ) {
      var imm = tonumber(match(q, "^#(.*)$")); n +=   1;
      if( ! imm || shr(imm, 16) != 0 ) {
	werror("bad immediate operand");
      }
      op +=   shl(band(imm, 0xfff0), 4) + band(imm, 0x000f);
    } else if( p == "T" ) {
      op +=   parse_imm(q, 24, 0, 0, false); n +=   1;
    } else if( p == "s" ) {
      // Ignored.
    } else {
      assert(false);
    }
  }
  wputpos(pos, op);
}

map_op[".template__"] = function(params, template, nparams) {
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
};

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
  setmetatable(map_op, { __index = function(t, k) {
    var v = map_coreop[k];
    if( v ) { return v; }
    var k1, cc, k2 = match(k, "^(.-)(..)([._].*)$");
    var cv = map_cond[cc];
    if( cv ) {
      v = rawget(t, k1..k2);
      if( type(v) == "string" ) {
	var scv = format("%x", cv);
	return gsub(scv..sub(v, 2), "|e", "|"..scv);
      }
    }
  } });
  setmetatable(map_def, { __index = map_archdef });
  return map_op, map_def;
}

return _M;

//----------------------------------------------------------------------------

