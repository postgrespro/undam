MODULE_big = undam
OBJS = undam.o
PGFILEDESC = "undam - MVCC storage with undo log"

EXTENSION = undam
DATA = undam--0.1.sql

REGRESS = undam

ifdef USE_PGXS
PG_CONFIG ?= pg_config
PGXS := $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)
else
subdir = contrib/undam
top_builddir = ../..
include $(top_builddir)/src/Makefile.global
include $(top_srcdir)/contrib/contrib-global.mk
endif
