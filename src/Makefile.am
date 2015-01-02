### Makefile.am
include $(top_builddir)/version.mk

AM_CFLAGS = $(EXTRA_CFLAGS)
AM_CPPFLAGS = -D_POSIX_C_SOURCE=201001L -D_XOPEN_SOURCE=700 -D_BSD_SOURCE
AM_LDFLAGS = $(XCCLDFLAGS)

bin_PROGRAMS =
noinst_PROGRAMS =
lib_LTLIBRARIES =
noinst_LTLIBRARIES =
pkglib_LTLIBRARIES =
noinst_HEADERS =
BUILT_SOURCES =
EXTRA_DIST = $(BUILT_SOURCES)
CLEANFILES = 
SUFFIXES =

CLEANFILES += version.c
EXTRA_DIST += version.c.in

bin_PROGRAMS += gleis2rdf
gleis2rdf_SOURCES = gleis2rdf.c gleis2rdf.yuck
gleis2rdf_CPPFLAGS = $(AM_CPPFLAGS)
gleis2rdf_CPPFLAGS += $(shell pkg-config --cflags libxml-2.0)
gleis2rdf_LDFLAGS = $(AM_LDFLAGS)
gleis2rdf_LDFLAGS += $(shell pkg-config --libs libxml-2.0)
BUILT_SOURCES += gleis2rdf.yucc

bin_PROGRAMS += gleis4dbpjoin
gleis4dbpjoin_SOURCES = gleis4dbpjoin.c gleis4dbpjoin.yuck
gleis4dbpjoin_CPPFLAGS = $(AM_CPPFLAGS)
gleis4dbpjoin_CPPFLAGS += $(shell pkg-config --cflags libxml-2.0)
gleis4dbpjoin_LDFLAGS = $(AM_LDFLAGS)
gleis4dbpjoin_LDFLAGS += $(shell pkg-config --libs libxml-2.0)
BUILT_SOURCES += gleis4dbpjoin.yucc


## version rules
version.c: version.c.in $(top_builddir)/.version
	$(AM_V_GEN) PATH="$(top_builddir)/build-aux:$${PATH}" \
		yuck$(EXEEXT) scmver --ignore-noscm --force -o $@ \
			--use-reference --reference $(top_builddir)/.version $<

## yuck rule
SUFFIXES += .yuck
SUFFIXES += .yucc
.yuck.yucc:
	$(AM_V_GEN) PATH=$(top_builddir)/build-aux:"$${PATH}" \
		yuck$(EXEEXT) gen -o $@ $<

## Create preprocessor output (debugging purposes only)
.c.i:
	$(COMPILE) -E -o $@ $<

## Create assembler output (debugging purposes only)
.c.s:
	$(COMPILE) -S -c $(AM_CFLAGS) $<
