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

bin_PROGRAMS += cleis2rdf
cleis2rdf_SOURCES = cleis2rdf.c cleis2rdf.yuck
cleis2rdf_CPPFLAGS = $(AM_CPPFLAGS)
cleis2rdf_CPPFLAGS += $(shell pkg-config --cflags libxml-2.0)
cleis2rdf_LDFLAGS = $(AM_LDFLAGS)
cleis2rdf_LDFLAGS += $(shell pkg-config --libs libxml-2.0)
BUILT_SOURCES += cleis2rdf.yucc

bin_PROGRAMS += pleis2rdf
pleis2rdf_SOURCES = pleis2rdf.c pleis2rdf.yuck
pleis2rdf_CPPFLAGS = $(AM_CPPFLAGS)
pleis2rdf_CPPFLAGS += $(shell pkg-config --cflags libxml-2.0)
pleis2rdf_LDFLAGS = $(AM_LDFLAGS)
pleis2rdf_LDFLAGS += $(shell pkg-config --libs libxml-2.0)
BUILT_SOURCES += pleis2rdf.yucc

bin_PROGRAMS += cleis4dbpjoin
cleis4dbpjoin_SOURCES = cleis4dbpjoin.c cleis4dbpjoin.yuck
cleis4dbpjoin_CPPFLAGS = $(AM_CPPFLAGS)
cleis4dbpjoin_CPPFLAGS += $(shell pkg-config --cflags libxml-2.0)
cleis4dbpjoin_LDFLAGS = $(AM_LDFLAGS)
cleis4dbpjoin_LDFLAGS += $(shell pkg-config --libs libxml-2.0)
BUILT_SOURCES += cleis4dbpjoin.yucc

bin_PROGRAMS += pleis4dbpjoin
pleis4dbpjoin_SOURCES = pleis4dbpjoin.c pleis4dbpjoin.yuck
pleis4dbpjoin_CPPFLAGS = $(AM_CPPFLAGS)
pleis4dbpjoin_CPPFLAGS += $(shell pkg-config --cflags libxml-2.0)
pleis4dbpjoin_LDFLAGS = $(AM_LDFLAGS)
pleis4dbpjoin_LDFLAGS += $(shell pkg-config --libs libxml-2.0)
BUILT_SOURCES += pleis4dbpjoin.yucc


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
