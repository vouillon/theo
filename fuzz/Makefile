# afl-fuzz workflow for the Theo Monolith harness.
#
# This includes Monolith's own demo Makefile, which provides the standard
# targets: setup, all, random, test, unattended, show, summary, min, multicore,
# tmux, clean. See fuzz/README.md for how to use them.
#
# afl targets require an afl-instrumented switch (one built with
# ocaml-option-afl) that has monolith installed; `make setup` creates/prepares
# it. Override SWITCH on the command line to use a different one, e.g.
#   make SWITCH=4.14.2+afl test
#
# The `random` target does NOT require afl instrumentation (it feeds the harness
# from /dev/urandom); to run it on your current switch instead of the afl one,
# use the plain dune invocation documented in fuzz/README.md.

SWITCH := 5.5.0+afl
EXE    := main.exe

include $(shell ocamlfind query monolith)/Makefile.monolith
