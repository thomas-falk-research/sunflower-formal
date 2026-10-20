# Audit record of the LPCert port (roadmap §73–§74)

The raw outputs behind the figures and verdicts of `docs/roadmap.md` §73 and
§74: the kernel build of the certificate modules, `make certs`, the
assumptions and statement audits, `coqchk` on every certificate module, the
mutation runs, and the solves and conversions that produced the
certificates. They are kept as evidence that the runs happened as
reported, not as inputs: everything here can be regenerated from the
committed sources (`make certs`, `make certs-assumptions`,
`make certs-statements`, `make certs-coqchk`, `tools/mutate.py`), at the
cost §73 records. Paths inside the logs refer to the build machine's
working directories (`/tmp/claude-0/s21/port/…`).

Recorded 2026-10-13 to 2026-10-15 on one 4-core, 15 GB machine, Coq 8.18.0.

| file | what it is | sha256 |
|---|---|---|
| `build.out` | one line per certificate module compiled by the detached builders (`build.sh`, `build2.sh`): exit code, wall time, peak memory; `NOTE` lines record the `Link21s109` event of §73.3 (compiled twice at once, then deleted and rebuilt alone); `BUILT`/`SWITCHED` lines mark the batches | `8734d517a8f5c17640dc8d1f2299e0c067f7f2caadd95fae1955b965dec174ee` |
| `build_logs.tar.gz` | the per-module build logs (`coq/*.buildlog`, 655 of 656: `Link23s0` was compiled first, by hand, in the side-by-side timing of §73.3, outside the builders) | `54fc93dfbd25f145e276ebb78bb5048e257de85f8df37e98defd155b4f4da7f1` |
| `censusiota_assumptions.out` | `Print Assumptions` of `CensusIota.iota_of_census` and `g_four_at_most_76_of_census` | `dfd7d954dd0eb1958170e60c0ca038537d25996565f730577c670524cffd3c75` |
| `censusiota_statements_diff.log` | the certificate statement baseline before accepting the two `CensusIota` entries (additions only) | `039ad19d0ad4b35d1af70ef9c1b46a1ff51dc9b9d278629d943fa7aae0412f27` |
| `certs_assumptions.log` | `make certs-assumptions`: the eleven certificate theorems, all closed under the global context | `42e375aed3fc7a185044afa47ce09d231a4851c121c5c8b81e4aa52551e67dda` |
| `certs_statements_diff.log` | `make certs-statements` before acceptance: the only changes, `descent_23` and `g_four_at_most_78_of_census_23` | `7dade6b3fae741eed564ce44e3ceb4f2fbd0571e3529e933ee9bfa12340d736c` |
| `coqchk_logs.tar.gz` | the 691 coqchk logs (`coqchk-certs/*.log`): the 690 modules of `_CoqProject.certs` and `CensusIota`, each `-norec` | `13f5f080e152fafb3f73c7d72043369cb1d95ef29ae4223d4b46c707267162f0` |
| `coqchk_results.out` | `ok`/`FAIL`/`AXIOM`/`HATCH` line per module from the two resumable coqchk instances (`chkall.sh` forward, `chkrev.sh` reversed); 691 `ok` lines for 690 modules (one checked by both at the meeting point), no other verdict | `883b37089c01dd22cef353aa4628c012d2d2fbc150e27fa3821d86ffc2505aa3` |
| `lpconvert.log` | `link23_coq.py lpconvert`: one line per converted tree file (sizes 21, 22, 23–27), every tree re-checked exactly after conversion | `c298749a393dfbcbfa272b87c7551ddc8f2ae7192f8039d35e3ad007546640c5` |
| `make_certs.log` | `make certs` after the builds: only the three combining modules compiled; exit 0 | `a4664f79a11d3e66c0ea67e086869b1fc128fefcec23239de6b0326202bad56b` |
| `mutations/mut_down2.log` | `distinct-is-nodup` and `upperbound-strict`, the expected kills that do not break their own file, re-run through the harness | `77d06e1e65a871df593085a427752f85c85d0bad27648b2f66e3b5a49225adf1` |
| `mutations/mut_lrat.log` | the four `lrat-*` mutations, first run: one killed, three and the control timed out at 600 s beside four coqchk processes | `dbb4b8ad60b40295316263b189ce30c53130df56b40d7a8fb4bdab7314124884` |
| `mutations/mut_lrat2.log` | the three timed-out `lrat-*` mutations and the control, re-run with a 3,600 s limit: all as declared | `4705addc9686ea8a9ab041ecaab4563f7fd3ce4183b369e1477ed3f3e85264e2` |
| `mutations/mut_old6.log` | the six earlier `lpcert-*` mutations re-run against the extended checker | `2ca7c4a3cbf2ac87555ad4fce2628659928c2dfa3579c3c3cc4e35313e074656` |
| `mutations/mut_port.log` | the six mutations added with the port (`lpcert-slack-*`, `lpcert-declare-all`, `link23-lp-*`) and the control | `c27009f51fd188cff105bd7654e19dd8449bac4b8ceb1507ca2ff2f784ae2eb1` |
| `mutations/mut_surv.log` | the two genuine survivors re-run against the ported code | `72f899ea82ce39e3fe5b258063771166abc4ea4fc3c0698c7016b65473d359fd` |
| `mutations/ownfile_results.txt` | every mutation expected to be killed, applied to its own file alone in a scratch copy of the library: `own-file-breaks` or `own-file-compiles` (the latter re-run through the harness above) | `1f6dc2d4245968bfee7fe063d20fdb7c93b431391694c685c131e9f4ac8d3353` |
| `solve_23_27.log.gz` | `link23_coq.py batch` on the 14,805 classes of sizes 23–27: per-class tree statistics, and per shard `wrote … classes; failed 0 []` | `97e6c1a53113030a27defb330974a3affdfb92152fc087e47d608d3a92715e31` |
