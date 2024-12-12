#
# This Makefile is not called from Opam but only used for
# convenience during development
#

DUNE 	= dune

.PHONY: all install test clean uninstall

all:
	$(DUNE) build

install: all
	$(DUNE) install ou-lang

uninstall:
	$(DUNE) uninstall

test:
	$(DUNE) runtest

clean:
	$(DUNE) clean

utop:
	$(DUNE) utop
