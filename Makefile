##############################################################################
# LuaJIT top level Makefile for installation. Requires GNU Make.
#
# Please read doc/install.html before changing any variables!
#
# Suitable for POSIX platforms (Linux, *BSD, OSX etc.).
# Note: src/Makefile has many more configurable options.
#
# ##### This Makefile is NOT useful for Windows! #####
# For MSVC, please follow the instructions given in src/msvcbuild.bat.
# For MinGW and Cygwin, cd to src and run make with the Makefile there.
#
# Copyright (C) 2005-2020 Mike Pall. See Copyright Notice in luajit.h
##############################################################################

MAJVER=  2
MINVER=  1
RELVER=  0
PREREL=  -beta3
VERSION= $(MAJVER).$(MINVER).$(RELVER)$(PREREL)
ABIVER=  5.1

##############################################################################
#
# Change the installation path as needed. This automatically adjusts
# the paths in src/luaconf.h, too. Note: PREFIX must be an absolute path!
#
#export PREFIX= /usr/local
export PREFIX= $(HOME)/local/ljsjit
export MULTILIB= lib
##############################################################################

DPREFIX= $(DESTDIR)$(PREFIX)
INSTALL_BIN=   $(DPREFIX)/bin
INSTALL_LIB=   $(DPREFIX)/$(MULTILIB)
INSTALL_SHARE= $(DPREFIX)/share
INSTALL_INC=   $(DPREFIX)/include/luajit-$(MAJVER).$(MINVER)

INSTALL_LJLIBD= $(INSTALL_SHARE)/luajit-$(VERSION)
INSTALL_JITLIB= $(INSTALL_LJLIBD)/jit
INSTALL_LMODD= $(INSTALL_SHARE)/lua
INSTALL_LMOD= $(INSTALL_LMODD)/$(ABIVER)
INSTALL_CMODD= $(INSTALL_LIB)/lua
INSTALL_CMOD= $(INSTALL_CMODD)/$(ABIVER)
INSTALL_MAN= $(INSTALL_SHARE)/man/man1
INSTALL_PKGCONFIG= $(INSTALL_LIB)/pkgconfig

INSTALL_TNAME= ljsjit-$(VERSION)
INSTALL_TSYMNAME= ljsjit
INSTALL_ANAME= libluajit-$(ABIVER).a
INSTALL_SOSHORT1= libluajit-$(ABIVER).so
INSTALL_SOSHORT2= libluajit-$(ABIVER).so.$(MAJVER)
INSTALL_SONAME= $(INSTALL_SOSHORT2).$(MINVER).$(RELVER)
INSTALL_DYLIBSHORT1= libluajit-$(ABIVER).dylib
INSTALL_DYLIBSHORT2= libluajit-$(ABIVER).$(MAJVER).dylib
INSTALL_DYLIBNAME= libluajit-$(ABIVER).$(MAJVER).$(MINVER).$(RELVER).dylib
INSTALL_PCNAME= ljsjit.pc

INSTALL_STATIC= $(INSTALL_LIB)/$(INSTALL_ANAME)
INSTALL_DYN= $(INSTALL_LIB)/$(INSTALL_SONAME)
INSTALL_SHORT1= $(INSTALL_LIB)/$(INSTALL_SOSHORT1)
INSTALL_SHORT2= $(INSTALL_LIB)/$(INSTALL_SOSHORT2)
INSTALL_T= $(INSTALL_BIN)/$(INSTALL_TNAME)
INSTALL_TSYM= $(INSTALL_BIN)/$(INSTALL_TSYMNAME)
INSTALL_PC= $(INSTALL_PKGCONFIG)/$(INSTALL_PCNAME)

INSTALL_DIRS= $(INSTALL_BIN) $(INSTALL_LIB) $(INSTALL_INC) $(INSTALL_MAN) \
  $(INSTALL_PKGCONFIG) $(INSTALL_JITLIB) $(INSTALL_LMOD) $(INSTALL_CMOD)
UNINSTALL_DIRS= $(INSTALL_JITLIB) $(INSTALL_LJLIBD) $(INSTALL_INC) \
  $(INSTALL_LMOD) $(INSTALL_LMODD) $(INSTALL_CMOD) $(INSTALL_CMODD)

RM= rm -f
MKDIR= mkdir -p
RMDIR= rmdir 2>/dev/null
SYMLINK= ln -sf
INSTALL_X= install -m 0755
INSTALL_F= install -m 0644
UNINSTALL= $(RM)
LDCONFIG= ldconfig -n 2>/dev/null
SED_PC= sed -e "s|^prefix=.*|prefix=$(PREFIX)|" \
            -e "s|^multilib=.*|multilib=$(MULTILIB)|"

FILE_T= ljsjit
FILE_A= libluajit.a
FILE_SO= libluajit.so
FILE_MAN= ljsjit.1
FILE_PC= ljsjit.pc
FILES_INC= lua.h lualib.h lauxlib.h luaconf.h lua.hpp luajit.h
FILES_JITLIB= bc.ljs bcsave.ljs dump.ljs p.ljs v.ljs zone.ljs \
	      dis_x86.ljs dis_x64.ljs dis_arm.ljs dis_arm64.ljs \
	      dis_arm64be.ljs dis_ppc.ljs dis_mips.ljs dis_mipsel.ljs \
	      dis_mips64.ljs dis_mips64el.ljs vmdef.ljs

ifeq (,$(findstring Windows,$(OS)))
  HOST_SYS:= $(shell uname -s)
else
  HOST_SYS= Windows
endif
TARGET_SYS?= $(HOST_SYS)

ifeq (Darwin,$(TARGET_SYS))
  INSTALL_SONAME= $(INSTALL_DYLIBNAME)
  INSTALL_SOSHORT1= $(INSTALL_DYLIBSHORT1)
  INSTALL_SOSHORT2= $(INSTALL_DYLIBSHORT2)
  LDCONFIG= :
endif

##############################################################################

INSTALL_DEP= src/ljsjit

default all $(INSTALL_DEP):
	@echo "==== Building LuaJIT $(VERSION) ===="
	$(MAKE) -C src
	@echo "==== Successfully built LuaJIT $(VERSION) ===="

install: $(INSTALL_DEP)
	@echo "==== Installing LuaJIT $(VERSION) to $(PREFIX) ===="
	$(MKDIR) $(INSTALL_DIRS)
	cd src && $(INSTALL_X) $(FILE_T) $(INSTALL_T)
	cd src && test -f $(FILE_A) && $(INSTALL_F) $(FILE_A) $(INSTALL_STATIC) || :
	$(RM) $(INSTALL_DYN) $(INSTALL_SHORT1) $(INSTALL_SHORT2)
	cd src && test -f $(FILE_SO) && \
	  $(INSTALL_X) $(FILE_SO) $(INSTALL_DYN) && \
	  ( $(LDCONFIG) $(INSTALL_LIB) || : ) && \
	  $(SYMLINK) $(INSTALL_SONAME) $(INSTALL_SHORT1) && \
	  $(SYMLINK) $(INSTALL_SONAME) $(INSTALL_SHORT2) || :
	cd etc && $(INSTALL_F) $(FILE_MAN) $(INSTALL_MAN)
	cd etc && $(SED_PC) $(FILE_PC) > $(FILE_PC).tmp && \
	  $(INSTALL_F) $(FILE_PC).tmp $(INSTALL_PC) && \
	  $(RM) $(FILE_PC).tmp
	cd src && $(INSTALL_F) $(FILES_INC) $(INSTALL_INC)
	cd src/jit && $(INSTALL_F) $(FILES_JITLIB) $(INSTALL_JITLIB)
	@echo "==== Successfully installed LuaJIT $(VERSION) to $(PREFIX) ===="
	@echo ""
	@echo "Note: the development releases deliberately do NOT install a symlink for luajit"
	@echo "You can do this now by running this command (with sudo):"
	@echo ""
	@echo "  $(SYMLINK) $(INSTALL_TNAME) $(INSTALL_TSYM)"
	@echo ""


uninstall:
	@echo "==== Uninstalling LuaJIT $(VERSION) from $(PREFIX) ===="
	$(UNINSTALL) $(INSTALL_T) $(INSTALL_STATIC) $(INSTALL_DYN) $(INSTALL_SHORT1) $(INSTALL_SHORT2) $(INSTALL_MAN)/$(FILE_MAN) $(INSTALL_PC)
	for file in $(FILES_JITLIB); do \
	  $(UNINSTALL) $(INSTALL_JITLIB)/$$file; \
	  done
	for file in $(FILES_INC); do \
	  $(UNINSTALL) $(INSTALL_INC)/$$file; \
	  done
	$(LDCONFIG) $(INSTALL_LIB)
	$(RMDIR) $(UNINSTALL_DIRS) || :
	@echo "==== Successfully uninstalled LuaJIT $(VERSION) from $(PREFIX) ===="

##############################################################################

amalg:
	@echo "Building LuaJIT $(VERSION)"
	$(MAKE) -C src amalg

clean:
	$(MAKE) -C src clean

.PHONY: all install amalg clean

##############################################################################
