COQFILES := coq/Sets.v coq/Sunflower.v coq/Graph.v coq/Matching.v \
            coq/HallCore.v coq/KoenigHall.v coq/Pigeonhole.v coq/ErdosRado.v \
            coq/ErdosRado_Greedy.v coq/LowerBound.v coq/ProductLowerBound.v \
            coq/Spread.v coq/Reflect.v coq/SpreadReduction.v coq/ALWZ.v \
            coq/Conjecture.v coq/SmallCases.v coq/F23.v coq/Audit.v

.PHONY: all coq verify coqchk rust test testbed mutants clean print-assumptions axiom-audit

all: coq rust

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject $(COQFILES)
	coq_makefile -f _CoqProject -o Makefile.coq

verify: clean coq print-assumptions axiom-audit
	@echo
	@echo "[verify] All proofs compiled."
	@echo "[verify] See axiom audit above."
	@echo "[verify] For an independent re-check of every module:"
	@echo "[verify]   make coqchk   -- re-typecheck with Coq's separate kernel checker"
	@echo "[verify] For the definition-level checks no kernel can make:"
	@echo "[verify]   make mutants  -- perturb each definition, see what breaks"
	@echo "[verify]   make testbed  -- exhaustive falsification of the spread axiom"

print-assumptions: coq
	@echo "============================================"
	@echo "  Print Assumptions audit (closed theorems)"
	@echo "============================================"
	@for thm in \
	    'ErdosRado.erdos_rado_upper_bound' \
	    'ErdosRado_Greedy.erdos_rado_via_greedy' \
	    'ErdosRado_Greedy.erdos_rado_contrapositive' \
	    'LowerBound.lower_bound_trivial' \
	    'LowerBound.no_k_sunflower_short_family' \
	    'ProductLowerBound.lower_bound_exponential' \
	    'ProductLowerBound.prod_family_no_literal_sunflower' \
	    'F23.f_2_3_eq_7' \
	    'HallCore.hall_abstract' \
	    'KoenigHall.hall_marriage_theorem' \
	    'KoenigHall.koenig_theorem' \
	    'F23.f_2_3_lower' \
	    'SmallCases.f_n_2_eq_2' \
	    'SmallCases.f_1_k_eq_k' \
	    'Pigeonhole.pigeonhole_family' \
	    'Sunflower.sunflower_lift' \
	    'Spread.sunflower_lift_set' \
	    'Spread.link_sunflower_lift' \
	    'Spread.w_spread_legacy_degenerate' \
	    'Spread.RaoSpread_Spread' \
	    'SpreadReduction.spread_reduction' \
	    'SpreadReduction.elementary_spread_disjoint' \
	    'SpreadReduction.spread_disjoint_above_elementary' \
	    'SpreadReduction.spread_erdos_rado' \
	    'Conjecture.spread_conjecture_suffices' \
	    'ALWZ.spread_singletons' \
	    'ALWZ.elementary_applies_to_singletons' \
	    'ALWZ.threshold_is_inside_the_gap' \
	    'ALWZ.axiom_hypotheses_satisfiable_in_the_gap' \
	    'Reflect.rao_spreadb_correct' \
	    'Reflect.rao_witness_agrees' \
	    'Reflect.rao_witness_complete' \
	    'Audit.lower_bound_excludes_upper' \
	    'Audit.lower_lt_upper' \
	    'Audit.no_upper_bound_below_exponential' \
	    'Audit.LowerBound_antitone' \
	    'Audit.LowerBound_ge_equiv' \
	    'Audit.ContainsKSunflower_equiv' \
	    'Audit.ContainsKSunflower_perm' \
	    'Audit.sunflower_core_unique' \
	    'Audit.distinct_strictly_stronger' \
	    'Audit.pairwise_disjoint_ground_bound' \
	    'Audit.no_k_disjoint_of_no_sunflower' \
	    'Audit.spread_yields_disjoint_below_threshold' \
	    'Audit.spread_yields_disjoint_needs_r' \
	    'Audit.spread_yields_disjoint_sandwich' \
	    'Audit.no_spread_yields_disjoint_2_3_2' \
	    'Audit.no_spread_yields_disjoint_2_3_2_alt' \
	    'Audit.bounds_coherent_er' \
	    'Audit.bounds_coherent_spread' \
	    'Audit.bounds_coherent_f_2_3' ; do \
	  result=$$(printf 'From Sunflower Require Import ErdosRado ErdosRado_Greedy LowerBound ProductLowerBound F23 SmallCases Pigeonhole Sunflower HallCore KoenigHall Spread Reflect SpreadReduction ALWZ Conjecture Audit.\nPrint Assumptions %s.\n' "$$thm" \
	    | coqtop -Q coq Sunflower 2>/dev/null | grep -m1 -E '^(Closed|Axioms)'); \
	  printf "  %-55s %s\n" "$$thm" "$$result"; \
	done
	@echo "============================================"

axiom-audit: coq
	@echo "===================================================="
	@echo "  Axiom dependency of the modern (2020) bound"
	@echo "===================================================="
	@printf 'From Sunflower Require Import ALWZ.\nPrint Assumptions ALWZ.sunflower_bound_from_spread_lemma.\n' \
	  | coqtop -Q coq Sunflower 2>/dev/null \
	  | sed -n '/^Axioms:/,/^$$/p' | sed 's/^/  [axiom-dep] /'
	@echo "===================================================="

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

rust:
	cd rust && cargo build --release

test: rust
	cd rust && cargo test --release

# Exhaustive search for counterexamples to the spread hypothesis, plus
# the differential checks against the Coq definitions. --nocapture so
# the empirical threshold table reaches the build log.
testbed:
	cd rust && cargo test --release --test spread_axiom -- --nocapture

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
