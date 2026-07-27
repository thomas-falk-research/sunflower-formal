COQFILES := coq/Sets.v coq/Sunflower.v coq/Graph.v coq/Matching.v \
            coq/HallCore.v coq/KoenigHall.v coq/Pigeonhole.v coq/ErdosRado.v \
            coq/ErdosRado_Greedy.v coq/LowerBound.v coq/ProductLowerBound.v \
            coq/Spread.v coq/SpreadReduction.v coq/ALWZ.v \
            coq/Conjecture.v coq/SmallCases.v coq/F23.v

.PHONY: all coq verify rust test clean print-assumptions axiom-audit

all: coq rust

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject $(COQFILES)
	coq_makefile -f _CoqProject -o Makefile.coq

verify: clean coq print-assumptions axiom-audit
	@echo
	@echo "[verify] All proofs compiled."
	@echo "[verify] See axiom audit above."

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
	    'SpreadReduction.spread_reduction' \
	    'SpreadReduction.elementary_spread_disjoint' \
	    'SpreadReduction.spread_erdos_rado' ; do \
	  result=$$(printf 'From Sunflower Require Import ErdosRado ErdosRado_Greedy LowerBound ProductLowerBound F23 SmallCases Pigeonhole Sunflower HallCore KoenigHall Spread SpreadReduction.\nPrint Assumptions %s.\n' "$$thm" \
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

rust:
	cd rust && cargo build --release

test: rust
	cd rust && cargo test --release

clean:
	@if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	@rm -f Makefile.coq Makefile.coq.conf coq/*.vo coq/*.vok coq/*.vos \
	       coq/*.glob coq/.*.aux coq/*.d
	@if [ -d rust/target ]; then rm -rf rust/target; fi
