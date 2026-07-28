# The module list has exactly one home: _CoqProject, which is what
# coq_makefile reads. Keeping a second copy here was a silent hole in
# the strongest gate -- COQMODULES below drives `make coqchk`, so a file
# present in _CoqProject and missing from this list would compile on
# every build and never be re-checked by the separate kernel.
COQFILES := $(shell sed -n 's|^\(coq/.*\.v\)[[:space:]]*$$|\1|p' _CoqProject)

# An empty list would rebuild nothing and coqchk nothing, silently -- the
# same hole in a new place. Fail loudly instead.
ifeq ($(strip $(COQFILES)),)
$(error no .v files found in _CoqProject; the COQFILES extraction is broken)
endif

.PHONY: all coq verify coqchk rust test testbed mutants clean print-assumptions \
        axiom-audit statements statements-accept

all: coq rust

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject $(COQFILES)
	coq_makefile -f _CoqProject -o Makefile.coq

verify: clean coq print-assumptions axiom-audit statements
	@echo
	@echo "[verify] All proofs compiled."
	@echo "[verify] See axiom audit above."
	@echo "[verify] For an independent re-check of every module:"
	@echo "[verify]   make coqchk   -- re-typecheck with Coq's separate kernel checker"
	@echo "[verify] For the definition-level checks no kernel can make:"
	@echo "[verify]   make mutants  -- perturb each definition, see what breaks"
	@echo "[verify]   make testbed  -- exhaustive falsification of the spread axiom"
	@echo "[verify] Statement baselines were checked; 'make statements-accept' to update."

print-assumptions: coq
	@echo "============================================"
	@echo "  Print Assumptions audit (closed theorems)"
	@echo "============================================"
	@total=0; for thm in $$(sed -n 's/^thm //p' tools/audited.txt); do \
	  result=$$(printf 'From Sunflower Require Import $(MODULES).\nPrint Assumptions %s.\n' "$$thm" \
	    | coqtop -q -Q coq Sunflower 2>/dev/null | grep -m1 -E '^(Closed|Axioms)'); \
	  printf "  %-60s %s\n" "$$thm" "$$result"; \
	  total=$$((total + 1)); \
	done; \
	echo "  --------------------------------------------"; \
	echo "  audited theorems: $$total"
	@echo "============================================"

axiom-audit: coq
	@echo "===================================================="
	@echo "  Axiom dependency of the modern (2020) bound"
	@echo "===================================================="
	@printf 'From Sunflower Require Import ALWZ.\nPrint Assumptions ALWZ.sunflower_bound_from_spread_lemma.\n' \
	  | coqtop -Q coq Sunflower 2>/dev/null \
	  | sed -n '/^Axioms:/,/^$$/p' | sed 's/^/  [axiom-dep] /'
	@echo "===================================================="

MODULES    := $(patsubst coq/%.v,%,$(COQFILES))
COQMODULES := $(patsubst coq/%.v,Sunflower.%,$(COQFILES))

# Independent re-verification.
#
# coqchk is a separate program from coqc: it re-typechecks the compiled
# proof terms with its own kernel implementation, with no elaborator, no
# tactics, and no unification. Two things it gives that
# `print-assumptions` cannot.
#
# First, it covers the *whole library* rather than a curated list of
# theorem names. `Print Assumptions` only ever reports on the theorems
# the Makefile happens to name; an `Admitted` lemma somewhere else, or a
# second `Axiom`, would go unreported. coqchk's context summary lists
# every assumption in every module.
#
# Second, it reports the escape hatches nothing else here checks:
# type-in-type, unsafe (co)fixpoints, and inductives whose positivity is
# assumed. CI gates on all three being empty.
coqchk: coq
	@echo "===================================================="
	@echo "  coqchk -- independent re-check of every module"
	@echo "===================================================="
	coqchk -Q coq Sunflower -o -silent $(COQMODULES)
	@echo "===================================================="

# Statement baselines: snapshot testing for what the development claims.
#
# Neither the kernel, `Print Assumptions`, nor coqchk can see a change of
# *statement* -- a theorem whose hypothesis quietly weakened still
# compiles, still reports closed, and still re-typechecks. This records
# what every audited name says, so changing it becomes a deliberate act
# with a reviewable one-line diff instead of a side effect buried in
# tactic churn. See tools/statements.py.
statements: coq
	@echo "===================================================="
	@echo "  Statement baselines vs tools/statements.txt"
	@echo "===================================================="
	@python3 tools/statements.py
	@echo "===================================================="

statements-accept: coq
	@python3 tools/statements.py --accept

rust:
	cd rust && cargo build --release

test: rust
	cd rust && cargo test --release

# Exhaustive search for counterexamples to the spread hypothesis, plus
# the differential checks against the Coq definitions. --nocapture so
# the empirical threshold table reaches the build log.
#
# The second suite falsifies the Chvatal-Hanson identification: that one
# extremal function governs both the sharp spread threshold at
# uniformity 2 and the exact sunflower numbers f(2,k).
testbed:
	cd rust && cargo test --release --test spread_axiom -- --nocapture
	cd rust && cargo test --release --test chvatal_hanson -- --nocapture

# Mutation testing: weaken one definition at a time and see whether
# anything in the development notices. See tools/mutations.toml.
MUTANT_JOBS ?= 4
mutants:
	python3 tools/mutate.py --jobs $(MUTANT_JOBS)

clean:
	@if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	@rm -f Makefile.coq Makefile.coq.conf coq/*.vo coq/*.vok coq/*.vos \
	       coq/*.glob coq/.*.aux coq/*.d
	@if [ -d rust/target ]; then rm -rf rust/target; fi
