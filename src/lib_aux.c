/*
** Auxiliary library for the Lua/C API.
** Copyright (C) 2005-2017 Mike Pall. See Copyright Notice in luajit.h
**
** Major parts taken verbatim or adapted from the Lua interpreter.
** Copyright (C) 1994-2008 Lua.org, PUC-Rio. See Copyright Notice in lua.h
*/

#include <errno.h>
#include <stdarg.h>
#include <stdio.h>

#define lib_aux_c
#define LUA_LIB

#include "lua.h"
#include "lauxlib.h"

#include "lj_obj.h"
#include "lj_err.h"
#include "lj_state.h"
#include "lj_trace.h"
#include "lj_lib.h"

#if LJ_TARGET_POSIX
#include <sys/wait.h>
#endif

/* -- I/O error handling -------------------------------------------------- */

LUALIB_API int luaL_fileresult(lua_State *L, int stat, const char *fname)
{
  if (stat) {
    setboolV(L->top++, 1);
    return 1;
  } else {
    int en = errno;  /* Lua API calls may change this value. */
    setnilV(L->top++);
    if (fname)
      lua_pushfstring(L, "%s: %s", fname, strerror(en));
    else
      lua_pushfstring(L, "%s", strerror(en));
    setintV(L->top++, en);
    lj_trace_abort(G(L));
    return 3;
  }
}

LUALIB_API int luaL_execresult(lua_State *L, int stat)
{
  if (stat != -1) {
#if LJ_TARGET_POSIX
    if (WIFSIGNALED(stat)) {
      stat = WTERMSIG(stat);
      setnilV(L->top++);
      lua_pushliteral(L, "signal");
    } else {
      if (WIFEXITED(stat))
	stat = WEXITSTATUS(stat);
      if (stat == 0)
	setboolV(L->top++, 1);
      else
	setnilV(L->top++);
      lua_pushliteral(L, "exit");
    }
#else
    if (stat == 0)
      setboolV(L->top++, 1);
    else
      setnilV(L->top++);
    lua_pushliteral(L, "exit");
#endif
    setintV(L->top++, stat);
    return 3;
  }
  return luaL_fileresult(L, 0, NULL);
}

/* -- Module registration ------------------------------------------------- */

LUALIB_API const char *luaL_findtable(lua_State *L, int idx,
				      const char *fname, int szhint)
{
  const char *e;
  lua_pushvalue(L, idx);
  do {
    e = strchr(fname, '.');
    if (e == NULL) e = fname + strlen(fname);
    lua_pushlstring(L, fname, (size_t)(e - fname));
    lua_rawget(L, -2);
    if (lua_isnil(L, -1)) {  /* no such field? */
      lua_pop(L, 1);  /* remove this nil */
      lua_createtable(L, 0, (*e == '.' ? 1 : szhint)); /* new table for field */
      lua_pushlstring(L, fname, (size_t)(e - fname));
      lua_pushvalue(L, -2);
      lua_settable(L, -4);  /* set new table into field */
    } else if (!lua_istable(L, -1)) {  /* field has a non-table value? */
      lua_pop(L, 2);  /* remove table and value */
      return fname;  /* return problematic part of the name */
    }
    lua_remove(L, -2);  /* remove previous table */
    fname = e + 1;
  } while (*e == '.');
  return NULL;
}

static int libsize(const luaL_Reg *l)
{
  int size = 0;
  for (; l && l->name; l++) size++;
  return size;
}

LUALIB_API void luaL_pushmodule(lua_State *L, const char *modname, int sizehint)
{
  luaL_findtable(L, LUA_REGISTRYINDEX, "_LOADED", 16);
  lua_getfield(L, -1, modname);
  if (!lua_istable(L, -1)) {
    lua_pop(L, 1);
    if (luaL_findtable(L, LUA_GLOBALSINDEX, modname, sizehint) != NULL)
      lj_err_callerv(L, LJ_ERR_BADMODN, modname);
    lua_pushvalue(L, -1);
    lua_setfield(L, -3, modname);  /* _LOADED[modname] = new table. */
  }
  lua_remove(L, -2);  /* Remove _LOADED table. */
}

LUALIB_API void luaL_openlib(lua_State *L, const char *libname,
			     const luaL_Reg *l, int nup)
{
  lj_lib_checkfpu(L);
  if (libname) {
    luaL_pushmodule(L, libname, libsize(l));
    lua_insert(L, -(nup + 1));  /* Move module table below upvalues. */
  }
  if (l)
    luaL_setfuncs(L, l, nup);
  else
    lua_pop(L, nup);  /* Remove upvalues. */
}

LUALIB_API void luaL_register(lua_State *L, const char *libname,
			      const luaL_Reg *l)
{
  luaL_openlib(L, libname, l, 0);
}

LUALIB_API void luaL_setfuncs(lua_State *L, const luaL_Reg *l, int nup)
{
  luaL_checkstack(L, nup, "too many upvalues");
  for (; l->name; l++) {
    int i;
    for (i = 0; i < nup; i++)  /* Copy upvalues to the top. */
      lua_pushvalue(L, -nup);
    lua_pushcclosure(L, l->func, nup);
    lua_setfield(L, -(nup + 2), l->name);
  }
  lua_pop(L, nup);  /* Remove upvalues. */
}

LUALIB_API const char *luaL_gsub(lua_State *L, const char *s,
				 const char *p, const char *r)
{
  const char *wild;
  size_t l = strlen(p);
  luaL_Buffer b;
  luaL_buffinit(L, &b);
  while ((wild = strstr(s, p)) != NULL) {
    luaL_addlstring(&b, s, (size_t)(wild - s));  /* push prefix */
    luaL_addstring(&b, r);  /* push replacement in place of pattern */
    s = wild + l;  /* continue after `p' */
  }
  luaL_addstring(&b, s);  /* push last suffix */
  luaL_pushresult(&b);
  return lua_tostring(L, -1);
}

/* -- Buffer handling ----------------------------------------------------- */

/* userdata to box arbitrary data */
typedef struct UBox {
  void *box;
  size_t bsize;
} UBox;

static void *resizebox (lua_State *L, int idx, size_t newsize) {
  void *ud;
  lua_Alloc allocf = lua_getallocf(L, &ud);
  UBox *box = (UBox *)lua_touserdata(L, idx);
  void *temp = allocf(ud, box->box, box->bsize, newsize);
  if (temp == NULL && newsize > 0) {  /* allocation error? */
    resizebox(L, idx, 0);  /* free buffer */
    luaL_error(L, "not enough memory for buffer allocation");
  }
  box->box = temp;
  box->bsize = newsize;
  return temp;
}

static int boxgc (lua_State *L) {
  resizebox(L, 1, 0);
  return 0;
}


static void *newbox (lua_State *L, size_t newsize) {
  UBox *box = (UBox *)lua_newuserdata(L, sizeof(UBox));
  box->box = NULL;
  box->bsize = 0;
  if (luaL_newmetatable(L, "LUABOX")) {  /* creating metatable? */
    lua_pushcfunction(L, boxgc);
    lua_setfield(L, -2, "__gc");  /* metatable.__gc = boxgc */
  }
  lua_setmetatable(L, -2);
  return resizebox(L, -1, newsize);
}

/*
** check whether buffer is using a userdata on the stack as a temporary
** buffer
*/
#define buffonstack(B)	((B)->b != (B)->initb)


/*
** returns a pointer to a free area with at least 'sz' bytes
*/
LUALIB_API char *luaL_prepbuffsize (luaL_Buffer *B, size_t sz) {
  lua_State *L = B->L;
  if (B->size - B->n < sz) {  /* not enough space? */
    char *newbuff;
    size_t newsize = B->size * 2;  /* double buffer size */
    if (newsize - B->n < sz)  /* not big enough? */
      newsize = B->n + sz;
    if (newsize < B->n || newsize - B->n < sz)
      luaL_error(L, "buffer too large");
    /* create larger buffer */
    if (buffonstack(B))
      newbuff = (char *)resizebox(L, -1, newsize);
    else {  /* no buffer yet */
      newbuff = (char *)newbox(L, newsize);
      memcpy(newbuff, B->b, B->n * sizeof(char));  /* copy original content */
    }
    B->b = newbuff;
    B->size = newsize;
  }
  return &B->b[B->n];
}

LUALIB_API void luaL_addlstring (luaL_Buffer *B, const char *s, size_t l) {
  if (l > 0) {  /* avoid 'memcpy' when 's' can be NULL */
    char *b = luaL_prepbuffsize(B, l);
    memcpy(b, s, l * sizeof(char));
    luaL_addsize(B, l);
  }
}

LUALIB_API void luaL_addstring(luaL_Buffer *B, const char *s)
{
  luaL_addlstring(B, s, strlen(s));
}

LUALIB_API void luaL_pushresult (luaL_Buffer *B) {
  lua_State *L = B->L;
  lua_pushlstring(L, B->b, B->n);
  if (buffonstack(B)) {
    resizebox(L, -2, 0);  /* delete old buffer */
    lua_remove(L, -2);  /* remove its header from the stack */
  }
}

LUALIB_API void luaL_addvalue (luaL_Buffer *B) {
  lua_State *L = B->L;
  size_t l;
  const char *s = lua_tolstring(L, -1, &l);
  if (buffonstack(B))
    lua_insert(L, -2);  /* put value below buffer */
  luaL_addlstring(B, s, l);
  lua_remove(L, (buffonstack(B)) ? -2 : -1);  /* remove value */
}

LUALIB_API void luaL_buffinit (lua_State *L, luaL_Buffer *B) {
  B->L = L;
  B->b = B->initb;
  B->n = 0;
  B->size = LUAL_BUFFERSIZE;
}

/* -- Reference management ------------------------------------------------ */

#define FREELIST_REF	0

/* Convert a stack index to an absolute index. */
#define abs_index(L, i) \
  ((i) > 0 || (i) <= LUA_REGISTRYINDEX ? (i) : lua_gettop(L) + (i) + 1)

LUALIB_API int luaL_ref(lua_State *L, int t)
{
  int ref;
  t = abs_index(L, t);
  if (lua_isnil(L, -1)) {
    lua_pop(L, 1);  /* remove from stack */
    return LUA_REFNIL;  /* `nil' has a unique fixed reference */
  }
  lua_rawgeti(L, t, FREELIST_REF);  /* get first free element */
  ref = (int)lua_tointeger(L, -1);  /* ref = t[FREELIST_REF] */
  lua_pop(L, 1);  /* remove it from stack */
  if (ref != 0) {  /* any free element? */
    lua_rawgeti(L, t, ref);  /* remove it from list */
    lua_rawseti(L, t, FREELIST_REF);  /* (t[FREELIST_REF] = t[ref]) */
  } else {  /* no free elements */
    ref = (int)lua_objlen(L, t) + LUA_INDEX_BASE; /* create new reference */
  }
  lua_rawseti(L, t, ref);
  return ref;
}

LUALIB_API void luaL_unref(lua_State *L, int t, int ref)
{
  if (ref >= 0) {
    t = abs_index(L, t);
    lua_rawgeti(L, t, FREELIST_REF);
    lua_rawseti(L, t, ref);  /* t[ref] = t[FREELIST_REF] */
    lua_pushinteger(L, ref);
    lua_rawseti(L, t, FREELIST_REF);  /* t[FREELIST_REF] = ref */
  }
}

/* -- Default allocator and panic function -------------------------------- */

static int panic(lua_State *L)
{
  const char *s = lua_tostring(L, -1);
  fputs("PANIC: unprotected error in call to Lua API (", stderr);
  fputs(s ? s : "?", stderr);
  fputc(')', stderr); fputc('\n', stderr);
  fflush(stderr);
  return 0;
}

#ifdef LUAJIT_USE_SYSMALLOC

#if LJ_64 && !LJ_GC64 && !defined(LUAJIT_USE_VALGRIND)
#error "Must use builtin allocator for 64 bit target"
#endif

static void *mem_alloc(void *ud, void *ptr, size_t osize, size_t nsize)
{
  (void)ud;
  (void)osize;
  if (nsize == 0) {
    free(ptr);
    return NULL;
  } else {
    return realloc(ptr, nsize);
  }
}

LUALIB_API lua_State *luaL_newstate(void)
{
  lua_State *L = lua_newstate(mem_alloc, NULL);
  if (L) G(L)->panic = panic;
  return L;
}

#else

#include "lj_alloc.h"

LUALIB_API lua_State *luaL_newstate(void)
{
  lua_State *L;
  void *ud = lj_alloc_create();
  if (ud == NULL) return NULL;
#if LJ_64 && !LJ_GC64
  L = lj_state_newstate(lj_alloc_f, ud);
#else
  L = lua_newstate(lj_alloc_f, ud);
#endif
  if (L) G(L)->panic = panic;
  return L;
}

#if LJ_64 && !LJ_GC64
LUA_API lua_State *lua_newstate(lua_Alloc f, void *ud)
{
  UNUSED(f); UNUSED(ud);
  fputs("Must use luaL_newstate() for 64 bit target\n", stderr);
  return NULL;
}
#endif

#endif

