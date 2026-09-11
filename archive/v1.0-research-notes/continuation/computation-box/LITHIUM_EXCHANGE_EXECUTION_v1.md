> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# N=3 signed-exchange execution checkpoint

The refined finite Slater computation produced the paper-supported rational
enclosure

`[-27/2, -11457461579/8589934592]`

for the N=3,Z=3 full fermionic Dirichlet-box energy on `(-2,2)^9` and for the
full-space lithium spectral infimum under the stated classical continuum
foundations. Its exact width is `104506655413/8589934592`, approximately 12.1662.
This is intentionally broad and does not improve earlier paper lithium bounds.
Its contribution is executed fermionic direct/exchange integration with a
replayable exact arithmetic path. It is not a Lean theorem or a new efficient
lithium method.

The trial occupies `phi111 up`, `phi111 down`, `phi211 up`. The proof in
`LITHIUM_EXCHANGE_STAGE_v1.md` includes its spin coefficients, the sixfold
noninteracting ground degeneracy, the unchanged ground-level complement
threshold, both clipping signs, and separate positive/negative exchange
convolutions. Only the full pair expectation is intersected with nonnegativity;
the clipped exchange operator is not assumed positive definite.

| Certificate | M | nuclear J | pair J | seconds | full-space upper |
|---|---:|---:|---:|---:|---|
| `n3_Z3_R1_M8_Jn32_Jp16_v1.json` | 8 | 32 | 16 | 6.5933 | `0` |
| `n3_Z3_R1_M16_Jn64_Jp32_v1.json` | 16 | 64 | 32 | 55.0986 | `-11457461579/8589934592` |

Both use R=1,bits=32,eta=1. Peak resident memory was 25,591,808 and 25,739,264
bytes. The refined upper is approximately -1.33382. The first stage's box upper
was positive, and its full-space output correctly used the known upper zero;
it did not silently report a negative midpoint estimate as certified. Both
stage lower endpoints use the elementary hydrogen bound -27/2 because the
computed complement/restoration lower estimate is weaker.

`exact_lithium_stage_v1.py` has SHA-256
`9916119d0868c3fd82ea432036939bd9b845434a9bb52a4391567513b97ad561`; certificates
also bind the unchanged N1 and N2 primitive source hashes. The four grouped
tests in `test_lithium_stage_v1.py` pass: mixed probability normalization,
mathematically known exchange signs/cancellation, exactly constant direct and
exchange kernels, and the full constant-potential Slater compression.

Independent review `INDEPENDENT_N3_REVIEW_v1.md` checked the source and exact
paper statement. Its separate script explicitly enumerated 8,320 six-dimensional
cell pairs. All four intervals (mixed direct, exchange, positive exchange part,
and negative exchange magnitude) exactly matched the convolution computation;
`independent_n3_checks_v1.json` records PASS. Constant kernels independently
yield direct=M and exchange=0. These finite tests corroborate the mathematical
argument and are not kernel verification.

`check_n3_M8_Jp16_v1.json` and `check_n3_M16_Jp32_v1.json` record fresh full
recomputation of all integrals and bounds. `isolated_lithium_rebuild_result_v1.json`
records PASS for copied-source compilation, tests, certificate regeneration,
and checking both original and regenerated coarse certificates under Python
`-I -B` in a fresh temporary directory. All exact mathematical fields agree.
No disk numerical cache, bytecode cache or third-party module was used;
memoization was limited to mathematical primitives within individual processes.
The checker shares the published implementation, which remains a trust boundary.

This fixed-rank computation cannot converge to arbitrary requested precision.
The next implemented prerequisite is `general_sine_integrals_v1.py`, extending
signed quadrature to arbitrary four-index sine Coulomb integrals on grids that
resolve every orbital node. Its local tests pass, but it is not yet connected
to a general spin/Slater matrix assembler or the arbitrary-N bounded-box
termination schedule. Those remain concrete implementation obligations.

Frozen provenance and original dictionary preservation are stated in the
mathematical stage file. No frozen artifact or completed N1/N2 certificate was
changed.
