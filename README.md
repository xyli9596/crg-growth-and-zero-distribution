# Completely regular growth: Lean formalization

This repository copy is a private staging archive for the frozen manuscript
and its current expanded Lean formalization. The frozen 24-page paper and
standalone LaTeX source are in [`manuscript/arxiv-v3`](manuscript/arxiv-v3).
The recorded full verification covers **318 modules and 1,720 distinct audited
declarations**. Cite the exact Git commit for this revision: the historical
`1.0.0` package/citation version identifies the earlier Theorem 1.1 revision
and is not a release tag for this expanded tree. No archival DOI has been issued
for this repository copy. Public release is deferred until arXiv announces v3.

This repository contains a Lean proof of the manuscript's Theorem 1.1:
every transcendental entire solution of finite order of a monic linear
differential equation with exponential-polynomial coefficients has positive
rational order, finite nonzero type, and completely regular growth.
It also contains the numbered assertions of Corollary 3.6, the coefficient
expansion criterion of Proposition 5.1, and the analytic integral-coefficient
classes in Corollaries 5.2 and 5.3.

The main declaration is
[`CRGTheorem11.theorem_1_1`](CRGTheorem11.lean).
Its hypotheses describe the actual equation and coefficients. The proof derives
the derivative estimates, residual bounds, fixed finite phase family, and growth
conclusions internally.

**What the conclusion means**

- [`CRGOrder.IsOrder`](CRGOrder.lean) defines order as the least nonnegative
  upper growth exponent. `UpperOrder f ρ` means that for every `δ > 0`,
  `‖f z‖ ≤ exp(‖z‖ ^ (ρ + δ))` outside a sufficiently large disk.
- [`LevinGrowth.FinitePositiveType`](LevinGrowth.lean) proves a global upper
  bound `‖f z‖ ≤ exp(C * ‖z‖ ^ ρ)` at large radii, with `C > 0`, and a matching
  positive lower bound at arbitrarily large points. These bounds determine
  the classical order and finite nonzero type. A separate Lean equivalence
  theorem to the `limsup log log M(r,f) / log r` definition is not included.
- [`LevinGrowth.ManuscriptCRG`](LevinGrowth.lean) includes a countable family
  of disks whose radii satisfy the actual C₀ condition, uniform convergence
  of the normalized logarithm outside those disks, and identification of the
  unrestricted Phragmén–Lindelöf indicator. Zeros have value minus infinity
  in the indicator definition.

**Build and verify**

Install Git, Python 3.9 or newer, and [elan](https://github.com/leanprover/elan), the Lean
toolchain manager. Open a terminal in this repository and run:

```sh
lake exe cache get
python3 verify.py
```

`lean-toolchain` pins **Lean 4.33.0**. The Lake configuration and
`lake-manifest.json` pin mathlib to
`db584cd6d46c92f209a44c0f1c829460d327499d` and record its dependencies.
Keep the committed manifest when reproducing this version; `lake update`
changes dependency resolution and is not part of the verification procedure.
The first setup requires internet access to download the toolchain,
dependencies, and mathlib cache.

`python3 verify.py` recompiles every local module in dependency order and
performs the source and axiom audits, using only the Python standard library.
It includes the complete local compilation; running `lake build` first is
unnecessary. The standard Lean build remains available separately with
`lake build`. The verifier writes module logs
to `verification/modules/` and its report to `verification/verification.json`;
compiled modules are stored in `.lake/build/lib/lean`. A successful run checks
the exact unified declaration set in [`Audit.lean`](Audit.lean), permitted
axioms, source/configuration consistency, and the pinned mathlib checkout.
Warnings are recorded; they do not by themselves fail verification.

The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The proof sources contain no `sorry`, `admit`, custom axioms, or `native_decide`
proofs. The script performs a complete check on every run; it has no resume
mode. Use `python3 verify.py --output-dir PATH` to choose another location for
the logs and report. To check independent modules in parallel, use
`python3 verify.py --jobs 4`; the default is one compiler process. A dependent
module starts only after its freshly rebuilt dependencies pass their audits,
and the unified audit runs last. Parallel runs perform the same complete checks.

Historical validation: on 2026-10-01, a complete local verification of the
standalone Theorem 1.1 revision passed: **223 modules recompiled, zero local modules reused,
and 1,374 distinct declarations audited**. Source, configuration, and compiled
output consistency checks passed. Seven existing unused-variable warnings
were recorded in `MixedVolterra.lean`.

This run used a fresh project directory and fresh checkouts of the pinned
dependencies, the existing Lean installation, and the standard mathlib cache.
It did not reuse compiled modules from the development project. It was not a
fresh operating-system installation; hosted Linux CI has not yet been run.
The historical `v1.0.0` source archive retains that revision and its report.
It does not include the four additional results described above.

Current expanded revision: a complete local rebuild with four dependency-aware
compiler workers passed: **318 modules freshly recompiled, zero local modules
reused, and 1,720 distinct declarations audited**. The report at
[`verification/verification.json`](verification/verification.json) certifies
Theorem 1.1 and all four new numbered results. Source, verifier/configuration,
compiled output, dependency and unified-audit consistency checks all passed.
The run recorded 42 nonfatal warnings about unused variables, simplification,
tactic style and deprecated names; none introduces a proof hole.
It used the pinned local dependency checkout and mathlib cache; a new hosted CI
run has not been performed. The complete rebuild took approximately 27 minutes.

**Read or edit in VS Code**

Open the repository folder in VS Code and install the recommended
[Lean 4 extension](https://github.com/leanprover/vscode-lean4). Start with
[`CRGTheorem11.lean`](CRGTheorem11.lean), and use the Lean infoview to inspect
hypotheses, goals, and declarations. The bundled tasks run the dependency
cache download, `lake build`, and `python3 verify.py` from the workspace root.
On Windows, the verification task uses the Python launcher `py -3`.

**Mathematical entry points**

| Part | Declaration |
| --- | --- |
| Manuscript Theorem 1.1 | [`CRGTheorem11.theorem_1_1`](CRGTheorem11.lean) |
| Corollary 3.6: finite order/indicator pairs, fixed exceptional rays, and negligible zeros away from them | [`CRGZeroDistributionCorollary.corollary_3_6`](CRGZeroDistributionCorollary.lean) |
| Corollary 3.6: finite pairs with order explicitly valued in the real numbers | [`CRGZeroDistributionRealPairs.finite_real_solution_indicator_pairs`](CRGZeroDistributionRealPairs.lean) |
| Proposition 5.1: complete coefficient expansions to growth and a fixed finite fractional phase family | [`CRGPuiseuxProposition.proposition_5_1`](CRGPuiseuxProposition.lean) |
| Corollary 5.2: finite linear kernels with holomorphic weights | [`CRGLinearKernel.corollary_5_2`](CRGLinearKernelConclusion.lean) |
| Corollary 5.3: polynomial kernels with positive integer powers and holomorphic weights | [`CRGPolynomialKernel.corollary_5_3`](CRGPolynomialKernelConclusion.lean) |
| Finite phase comparison to the complete growth conclusion | [`CRGFinitePhaseEndgame.complete_of_finite_phases`](CRGFinitePhaseEndgame.lean) |
| Gundersen angular estimates, all finite jets and positive errors | [`GundersenTheorem.ae_ray_input`](GundersenTheorem.lean) |
| Wasow rational ray normal form | [`WasowRationalNormalForm.rational_ray_normal_form`](WasowRationalNormalForm.lean) |
| Full constant-order Levin criterion, including C₀ disks and indicator | [`LevinC0.constantOrderLevin`](LevinC0.lean) |
| Dense-ray exponential bounds to global finite type | [`CRGPhragmenRay.dense_eventual_finiteType`](CRGPhragmenRay.lean) |
| Dense-ray polynomial bounds to global polynomial growth | [`CRGPhragmenPolynomialRay.dense_eventual_polynomial_bound`](CRGPhragmenPolynomialRay.lean) |

The Wasow result here is a **ray normal form for rational matrix systems**:
a fixed ramification and polynomial phase family precede the choice of a ray,
and the exact ray gauge has an inverse and polynomial bounds. It does not
assert the full sectorial asymptotic expansion or Stokes data of the book's
sector theorem. The Levin entry point proves the full constant-order
criterion used by the manuscript; it is not a formalization of every result
in Levin's book.

Corollary 3.6 accepts the original nonmonic exponential-polynomial equation
and a nonzero leading coefficient. Its zero counts use the actual analytic
divisor, with multiplicities, and the estimate holds at every sufficiently
large radius in each compact angular region separated from the fixed rays.
The more precise indicator derivative-jump formula in the paragraph following
the corollary is not formalized.

Proposition 5.1 is expressed with finite coefficient packets providing
complete expansions on each covered ray. This is a weaker source condition
than the manuscript's uniform expansion on closed subsectors. Negative
starting powers are encoded by a common clearing monomial; the formal
series may diverge. The Lean statement does not introduce a separate
uniform-subsector definition or a conversion theorem for that syntax.
The actual gauge, flat forcing estimates, finite fractional phases and
growth conclusion are constructed from these coefficient data.

Corollaries 5.2 and 5.3 accept only their stated integral representations and
source hypotheses. Their entire coefficients, fixed expansions, branch
choices, cancellations and finite sector families are constructed internally;
the final statements do not assume endpoint estimates or normal forms.
The resulting phase families are fixed by the coefficients before choosing
an ODE solution.

Some source comments record intermediate stages of the development and say
that particular steps were still open at that stage. The final declarations
above and their checked dependencies specify the present scope. Historical
unused-variable warnings in `MixedVolterra.lean` do not introduce proof holes.

**Reproducibility and citation**

Use the exact Git commit or release tag of the source you checked when citing
or comparing this formalization. Citation metadata is provided in
[`CITATION.cff`](CITATION.cff). A repository URL and archival DOI will be added
when they exist. This is a standalone project depending on mathlib; its
inclusion here does not imply acceptance into the upstream mathlib library.

This copy is being prepared locally for publication. Public release is
deferred until the manuscript is available on arXiv.

The workflow in [`.github/workflows/lean.yml`](.github/workflows/lean.yml)
uses the [standard Lean action](https://github.com/leanprover/lean-action) to
install the pinned toolchain, then downloads the mathlib cache and runs the
same verification script used locally. It uploads any available verification
report and module logs as a workflow artifact after success or failure.

**AI assistance**

OpenAI's ChatGPT and Codex were used extensively to develop and debug the Lean
formalization of Theorem 1.1, Corollary 3.6, Proposition 5.1, Corollaries 5.2
and 5.3, and their supporting results, and to prepare and
revise the verification scripts and documentation. The checked declarations,
their stated hypotheses, and the axiom audit specify the formal guarantees;
the mathematical scope and definition boundaries are described above.

**License**

The Lean project and verification code are licensed under the Apache License,
Version 2.0; see [`LICENSE`](LICENSE). Dependencies retain their respective
licenses. The frozen manuscript in `manuscript/arxiv-v3` retains its separate
CC BY-NC-SA 4.0 licence, as described in that folder's README.

**Double-click verification on macOS**

After installing the prerequisites above, double-click
[`验证全部证明.command`](验证全部证明.command). It opens a separate Terminal
window, prepares the pinned dependency cache, and runs the same full verification
as the VS Code task **Lean: verify proofs and axioms**. Progress appears in that
window; the report is saved to `verification/verification.json`. The window
stays open until you press Return after the check finishes.
