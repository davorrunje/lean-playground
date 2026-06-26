# Leshno Universal Approximation (M-class) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a compiling Lean 4 / Mathlib *scaffold* of the full Leshno–Lin–Pinkus–Schocken (1993) universal approximation theorem (`M`-class, dense ⟺ not-a.e.-polynomial), with every deep analytic leaf left as a documented `sorry` and all structural glue genuinely proved.

**Architecture:** A new subfolder `LeanPlayground/UniversalApproximation/Leshno/` follows Pinkus (Acta Numerica 1999, Thm 3.1): mollification (`σ⋆φ`) + the smooth derivative-trick engine + the ridge-function lift, bypassing Riesz duality entirely. All discontinuity of `σ` is confined to one membership fact (`σ⋆φ ∈ T`); everything downstream is ordinary `C(↥K,ℝ)` analysis. PR-candidate lemmas live in `LeanPlayground/ForMathlib/`.

**Tech Stack:** Lean 4, Mathlib `v4.32.0-rc1`, `lake`, lean-lsp MCP tools.

## Global Constraints

- Spec: `docs/superpowers/specs/2026-06-26-leshno-universal-approximation-design.md`. Branch: `feat/leshno-uat` (already created; spec committed).
- All new Leshno code under `LeanPlayground/UniversalApproximation/Leshno/`, `namespace UniversalApproximation.Leshno`, each file beginning `import Mathlib` (plus intra-folder imports). **No existing file is renamed or modified** except the optional new root re-export.
- `ForMathlib` code under `LeanPlayground/ForMathlib/`, in a project-neutral namespace (no `UniversalApproximation`), stated with general typeclasses, tagged `-- TODO(mathlib)`, so it is PR-extractable.
- Input space `EuclideanSpace ℝ (Fin n)`; inner product written `⟪w, x⟫` with `open scoped RealInnerProductSpace` (the `⟪·,·⟫_ℝ` suffix does NOT parse — established in the existing scaffold).
- **Approximation metric is everywhere-sup** (`∀ x, |f x - g x| < ε`), never ess-sup.
- **"Polynomial" at the M-boundary is a.e.** (`IsAEPolynomial`); the smooth/univariate layer uses everywhere-equality (`IsPolynomialFun`); a bridging lemma connects them for continuous functions.
- **Leaf lemmas left as `sorry` this cycle:** `iteratedDeriv_eq_zero_imp_poly`, `ridgePow_span`, `deriv_pow_mem` (B1), `exists_deriv_ne` (B2), `contDiff_mollify` (E — only if the Mathlib name proves elusive), `exists_nonpoly_mollify` (D), `mollify_mem_T` (A). Each gets a full docstring (missing mathematics + "Leshno et al. 1993 / Pinkus, Acta Numerica 1999, Thm 3.1") and a single `sorry`. **Everything else is genuinely proved — no bare `sorry` in glue.**
- **Definition of done per file:** `lean_diagnostic_messages` reports **no `error`-severity items**; the only `warning`s are `declaration uses 'sorry'` on the leaf lemmas above (plus harmless linter style notes).
- **Lean iteration is expected.** Statements below are exact; proofs are strategy + best-effort Mathlib names. For every proof: write it, run `lean_diagnostic_messages` (or `lean_goal` at a tactic position), and when stuck on a name use `lean_leansearch` / `lean_loogle` / `lean_local_search` / `lean_hover_info`. A declaration is done when diagnostics show no `error` and only the intended `sorry` (if any).
- **Per-lemma discipline (TDD analogue):** (a) write the declaration with `:= by sorry` (or `:= sorry`), confirm the *statement/def* elaborates (only a `sorry` warning, no error); (b) for glue, replace `sorry` with the real proof, confirm no `sorry`; (c) commit. Leaves stay at step (a). Never accumulate stray sorries beyond the named leaves.
- Commit after each task. If a commit hangs on SSH/GPG signing, retry once with `-c commit.gpgsign=false` and continue. Commit messages end with:
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`

---

### Task 1: `ForMathlib` leaf lemmas + tracking doc

The two general-purpose lemmas that the Leshno proof needs and Mathlib (probably) lacks. Both are `sorry` leaves this cycle; they have no project dependencies, so they come first.

**Files:**
- Create: `LeanPlayground/ForMathlib/IteratedDerivPolynomial.lean`
- Create: `LeanPlayground/ForMathlib/RidgePowersSpan.lean`
- Create: `docs/superpowers/mathlib-contributions.md`

**Interfaces:**
- Consumes: nothing.
- Produces: `iteratedDeriv_eq_zero_imp_poly`, `ridgePow_span` (signatures below), consumed by Tasks 4 and 6.

- [ ] **Step 1: Confirm absence in Mathlib.** Run `lean_leansearch` for "iterated derivative zero implies polynomial" and `lean_loogle` for `iteratedDeriv _ _ = 0`; run `lean_leansearch` for "powers of linear functionals span homogeneous polynomials" / "polarization". Record findings in the tracking doc. If a usable lemma already exists, note it and skip the corresponding `sorry` (use the Mathlib lemma in Tasks 4/6 instead).

- [ ] **Step 2: Write `IteratedDerivPolynomial.lean`** with the statement and a `sorry`:

```lean
import Mathlib

/-! # (Mathlib candidate) A function with a vanishing iterated derivative is a polynomial.
TODO(mathlib): intended home near `Mathlib/Analysis/Calculus/IteratedDeriv/`. -/

open Polynomial

/-- TODO(mathlib). If the `n`-th iterated derivative of `f : ℝ → ℝ` vanishes identically, then `f`
agrees (everywhere) with a polynomial function of degree `< n`. Needed for the Leshno smooth-engine
step (a nonpolynomial smooth function has some nonvanishing derivative of every order).
Leshno et al. 1993 / Pinkus, Acta Numerica 1999, Thm 3.1. -/
theorem iteratedDeriv_eq_zero_imp_poly {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiff ℝ (n : ℕ∞) f) (h : ∀ x, iteratedDeriv n f x = 0) :
    ∃ p : Polynomial ℝ, (∀ x, f x = p.eval x) ∧ p.natDegree < n := by
  sorry
```
Proof strategy for later: induction on `n` via `iteratedDeriv_succ` (the `n`-th derivative is the 1st derivative of the `(n-1)`-th); base case `n = 0` is `f = 0`; use that a function with zero derivative on `ℝ` is constant (`is_const_of_deriv_eq_zero` / `Constant`), then integrate degree by degree. Candidate names to verify: `iteratedDeriv_succ`, `is_const_of_fderiv_eq_zero`, `Polynomial.eval`.

- [ ] **Step 3: Write `RidgePowersSpan.lean`** with the statement and a `sorry`:

```lean
import Mathlib

/-! # (Mathlib candidate) Powers of linear functionals span the homogeneous polynomials.
TODO(mathlib): polarization; intended home near `Mathlib/LinearAlgebra/Polynomial` /
`Mathlib/RingTheory/MvPolynomial`. -/

open MvPolynomial

variable {n : ℕ}

/-- TODO(mathlib). The powers `x ↦ (∑ i, a i * x i) ^ k`, ranging over `a : Fin n → ℝ`, span (over ℝ)
the space of homogeneous polynomial functions of degree `k` on `Fin n → ℝ`. (Polarization of
symmetric tensors.) Needed for the Leshno ridge-function step.
Leshno et al. 1993 / Pinkus, Acta Numerica 1999, Thm 3.1. -/
theorem ridgePow_span (k : ℕ) :
    Submodule.span ℝ
        (Set.range fun a : Fin n → ℝ =>
          (fun x : Fin n → ℝ => (∑ i, a i * x i) ^ k))
      = -- the submodule of homogeneous degree-k polynomial functions (precise RHS chosen during impl)
        sorry := by
  sorry
```
Note for impl: the exact RHS (how to name "homogeneous degree-`k` polynomial functions" as a `Submodule ℝ ((Fin n → ℝ) → ℝ)`) is to be fixed when writing — likely the span of the monomial functions `x ↦ ∏ x i ^ (e i)` with `∑ e i = k`. Pin it down so the statement elaborates, then `sorry` the proof. This is the only node whose *statement* may need refinement; do that first and confirm it elaborates before moving on.

- [ ] **Step 4: Write `docs/superpowers/mathlib-contributions.md`** — a table with columns: lemma name, file, one-line statement, intended Mathlib location, status (`scaffolded` / `proved` / `PR #`). Seed it with the two lemmas above and a third conditional row for the convolution Riemann-sum approximation (Task 5, Lemma A core).

- [ ] **Step 5: Verify** — `lean_diagnostic_messages` on both `.lean` files: no `error`; only `declaration uses 'sorry'` warnings (two per file at most: one for `ridgePow_span`'s RHS-placeholder if still present — resolve the RHS so only the *proof* `sorry` remains).

- [ ] **Step 6: Commit**

```bash
git add LeanPlayground/ForMathlib/ docs/superpowers/mathlib-contributions.md
git commit -m "feat(leshno): ForMathlib leaf lemmas (iteratedDeriv→poly, ridge-powers span) + tracking doc

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 2: `ClassM.lean` — the activation class and polynomial predicate

**Files:**
- Create: `LeanPlayground/UniversalApproximation/Leshno/ClassM.lean`

**Interfaces:**
- Consumes: nothing.
- Produces: `ClassM : (ℝ → ℝ) → Prop` (fields `.locBdd`, `.discNull`), `IsAEPolynomial : (ℝ → ℝ) → Prop`, `IsPolynomialFun : (ℝ → ℝ) → Prop`, `ClassM.of_continuous : Continuous σ → ClassM σ`. Consumed by Tasks 3, 5, 7, 8.

- [ ] **Step 1: Write defs + statements** (everything proved here except none-required; examples may be `sorry` if slow):

```lean
import Mathlib

namespace UniversalApproximation.Leshno

open MeasureTheory

/-- The Leshno class `M`: locally bounded, and the closure of the discontinuity set is null. -/
structure ClassM (σ : ℝ → ℝ) : Prop where
  locBdd : ∀ R : ℝ, ∃ C, ∀ t, |t| ≤ R → |σ t| ≤ C
  discNull : volume (closure {t : ℝ | ¬ ContinuousAt σ t}) = 0

/-- `σ` agrees Lebesgue-a.e. with a polynomial function. -/
def IsAEPolynomial (σ : ℝ → ℝ) : Prop :=
  ∃ p : Polynomial ℝ, σ =ᵐ[volume] fun t => p.eval t

/-- `σ` equals a polynomial function everywhere. -/
def IsPolynomialFun (σ : ℝ → ℝ) : Prop :=
  ∃ p : Polynomial ℝ, σ = fun t => p.eval t

/-- A continuous function is in class `M` (discontinuity set is empty). -/
theorem ClassM.of_continuous {σ : ℝ → ℝ} (hσ : Continuous σ) : ClassM σ := by
  sorry

/-- A continuous a.e.-polynomial is an everywhere polynomial. (Bridges the two notions for the
smooth engine.) -/
theorem isPolynomialFun_of_continuous_of_aePolynomial {σ : ℝ → ℝ}
    (hσ : Continuous σ) (h : IsAEPolynomial σ) : IsPolynomialFun σ := by
  sorry

end UniversalApproximation.Leshno
```

- [ ] **Step 2: Prove `ClassM.of_continuous`.** `locBdd`: on `|t| ≤ R` (compact `Icc (-R) R`), continuity gives a bound via `IsCompact.exists_bound_of_continuousOn` (as used in the Cybenko `Sigmoidal.bounded`). `discNull`: `{t | ¬ContinuousAt σ t} = ∅` since `hσ.continuousAt`, so its closure is `∅`, measure `0` (`measure_empty`). Verify each name with `lean_local_search` / `lean_hover_info`.

- [ ] **Step 3: Prove `isPolynomialFun_of_continuous_of_aePolynomial`.** Two continuous functions equal a.e. (w.r.t. a measure with full support, `volume` on `ℝ`) are equal everywhere: `Continuous.ae_eq_iff_eq` or `MeasureTheory.eqOn_of_ae_eq` on a dense set + continuity (`Continuous.ext_on`). `p.eval` is continuous (`Polynomial.continuous`). Candidate: `Continuous.ae_eq_iff_eq` — verify; if absent, use `ae_eq` ⇒ equal on a dense set ⇒ `Continuous.ext_on dense_…`.

- [ ] **Step 4: (Optional) examples.** If quick, add `relu` / Heaviside `∈ ClassM` as proved sanity lemmas; if they require effort, add one with a documented `sorry` (counts as an allowed extra leaf, note it in the file docstring). Do NOT block the task on these.

- [ ] **Step 5: Verify** — `lean_diagnostic_messages`: no `error`; `sorry` warnings only on `of_continuous`/the bridge *until proved* and (optionally) the example.

- [ ] **Step 6: Commit**

```bash
git add LeanPlayground/UniversalApproximation/Leshno/ClassM.lean
git commit -m "feat(leshno): ClassM, IsAEPolynomial, IsPolynomialFun + continuous⇒M

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 3: `Family.lean` — the span, the continuous-core submodule `T`, and the reduction

**Files:**
- Create: `LeanPlayground/UniversalApproximation/Leshno/Family.lean`

**Interfaces:**
- Consumes: `ClassM` (Task 2) — not strictly needed for these defs, but the file imports it.
- Produces: `genFun`, `genSpan`, `T`, `genSpan_smul_mem` / dilation-translation invariance, `T_isClosed`, `DenselyApproximates`, `denselyApproximates_of_forall_T_eq_top`. Consumed by Tasks 5, 6, 7, 8.

- [ ] **Step 1: Write defs + statements:**

```lean
import Mathlib
import LeanPlayground.UniversalApproximation.Leshno.ClassM

namespace UniversalApproximation.Leshno

open scoped RealInnerProductSpace
open Topology

-- `genFun`/`genSpan`/`T` are stated over a general real inner-product space `E`, so the SAME
-- objects serve the n-dimensional case (`E = EuclideanSpace ℝ (Fin n)`) and the univariate case
-- (`E = ℝ`, where `⟪w,x⟫ = w*x`). Only the headline `DenselyApproximates` fixes `E` Euclidean.
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A single hidden unit as a plain (possibly discontinuous) function on `↥K`. -/
def genFun (σ : ℝ → ℝ) {K : Set E} (w : E) (b : ℝ) : ↥K → ℝ :=
  fun x => σ (⟪w, (x : E)⟫ + b)

/-- The linear span of all single hidden units, in the module of all functions `↥K → ℝ`. -/
def genSpan (σ : ℝ → ℝ) (K : Set E) : Submodule ℝ (↥K → ℝ) :=
  Submodule.span ℝ (Set.range fun wb : E × ℝ => genFun σ wb.1 wb.2)

/-- Carrier predicate for `T`: a function is an everywhere-sup limit of `genSpan` elements. -/
def ApproxByGen (σ : ℝ → ℝ) (K : Set E) (h : ↥K → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ g ∈ genSpan σ K, ∀ x, |h x - g x| < ε

/-- The continuous functions on `↥K` that are everywhere-sup limits of `genSpan`. A submodule of
`C(↥K,ℝ)`; proving `T σ K = ⊤` is the heart of the forward direction. -/
def T (σ : ℝ → ℝ) (K : Set E) : Submodule ℝ C(↥K, ℝ) where
  carrier := {h | ApproxByGen σ K (h : ↥K → ℝ)}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

/-- The family densely approximates every continuous function on every compact set. -/
def DenselyApproximates (σ : ℝ → ℝ) : Prop :=
  ∀ {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K →
    ∀ (f : C(↥K, ℝ)) {ε : ℝ}, 0 < ε → ∃ g ∈ genSpan σ K, ∀ x : ↥K, |f x - g x| < ε

/-- `genSpan` is invariant under the reparametrisation `(w,b) ↦ (λ•w, λ•b + c)`: scaling/shifting
the pre-activation keeps a generator in the span. -/
theorem genFun_reparam_mem (σ : ℝ → ℝ) (K : Set E)
    (lam : ℝ) (w : E) (b c : ℝ) :
    (fun x : ↥K => σ (lam * (⟪w, (x : E)⟫ + b) + c)) ∈ genSpan σ K := by
  sorry

theorem T_isClosed (σ : ℝ → ℝ) (K : Set E) :
    IsClosed (T σ K : Set C(↥K, ℝ)) := by
  sorry

/-- Reduction: if the continuous-core submodule is everything, the family densely approximates. -/
theorem denselyApproximates_of_forall_T_eq_top {σ : ℝ → ℝ}
    (h : ∀ {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K → T σ K = ⊤) :
    DenselyApproximates σ := by
  sorry

end UniversalApproximation.Leshno
```

- [ ] **Step 2: Prove the `Submodule` fields of `T`.** `zero_mem'`: take `g = 0 ∈ genSpan`, `|0 - 0| = 0 < ε`. `add_mem'`: given `h₁,h₂` approximable to `ε/2`, sum the witnesses `g₁+g₂ ∈ genSpan` (`Submodule.add_mem`), triangle inequality. `smul_mem'`: scale witness by `c`; handle `c = 0` separately, else use `ε/|c|`. These are genuine, routine; prove fully.

- [ ] **Step 3: Prove `genFun_reparam_mem`.** Rewrite `lam * (⟪w,x⟫ + b) + c = ⟪lam•w, x⟫ + (lam*b + c)` via `real_inner_smul_left` (exactly the rewrite used in the Cybenko `signed_halfspace_eq_zero`), so the function equals `genFun σ (lam•w) (lam*b + c)`, which is `Submodule.subset_span ⟨(lam•w, lam*b+c), rfl⟩`.

- [ ] **Step 4: Prove `T_isClosed`.** A uniform limit (in `C(↥K,ℝ)`, i.e. sup-norm) of functions each approximable by `genSpan` is itself approximable: given `h` in the closure and `ε`, pick `h'` in `T` with `‖h - h'‖ < ε/2` (so `∀x, |h x - h' x| < ε/2` via `ContinuousMap.norm_lt_iff` / `BoundedContinuousFunction`), then `g ∈ genSpan` with `∀x, |h' x - g x| < ε/2`, triangle. Use `Metric.isClosed_iff` / `mem_closure_iff_seq_limit` or `IsClosed` via `isClosed_iff_clusterPt`. Candidate names: `ContinuousMap.norm_le`, `ContinuousMap.dist_le`, `Metric.isClosed_iff`. Genuine proof.

- [ ] **Step 5: Prove `denselyApproximates_of_forall_T_eq_top`.** Unfold `DenselyApproximates`. Given `K`, `hK`, `f`, `ε`: from `h K hK : T σ K = ⊤`, `f ∈ T σ K` (`Submodule.mem_top`), i.e. `ApproxByGen σ K f`; apply at `ε`. Direct.

- [ ] **Step 6: Verify** — `lean_diagnostic_messages`: no `error`; **no `sorry`** (all of Task 3 is glue and must be fully proved). If any sub-proof is unexpectedly hard, leave it `sorry` with a docstring and report it prominently per the contingency rule — but the target is zero sorries here.

- [ ] **Step 7: Commit**

```bash
git add LeanPlayground/UniversalApproximation/Leshno/Family.lean
git commit -m "feat(leshno): genSpan, continuous-core submodule T, reparam invariance, T=⊤ reduction

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 4: `SmoothEngine.lean` — the univariate derivative-trick engine (B)

**Files:**
- Create: `LeanPlayground/UniversalApproximation/Leshno/SmoothEngine.lean`

**Interfaces:**
- Consumes: `iteratedDeriv_eq_zero_imp_poly` (Task 1), `IsPolynomialFun` (Task 2).
- Produces: `deriv_pow_mem` (B1, leaf), `exists_deriv_ne` (B2, leaf), `smooth_engine` (B3, glue). Consumed by Task 8 (`univariate_density`).

This file works abstractly on `C(ℝ,ℝ)` with the closed span of shifts `Sg g := Submodule.span ℝ (Set.range fun lb : ℝ × ℝ => fun t => g (lb.1 * t + lb.2))` and its `topologicalClosure`, with no measure theory. The univariate target is "the closure of `Sg g` is `⊤` in `C` uniform on compacta." Because the project's compacta are `↥K` (closed intervals suffice for the univariate stage), state the engine over an arbitrary compact real set and reuse it in Task 6/8.

- [ ] **Step 1: Write statements with `sorry`:**

```lean
import Mathlib
import LeanPlayground.UniversalApproximation.Leshno.ClassM
import LeanPlayground.ForMathlib.IteratedDerivPolynomial

namespace UniversalApproximation.Leshno

open Topology

/-- The span of dilated/translated copies of `g`, inside `C(I,ℝ)` for a compact real set `I`. -/
def Sg (g : ℝ → ℝ) (I : Set ℝ) (hg : Continuous g) : Submodule ℝ C(↥I, ℝ) :=
  Submodule.span ℝ (Set.range fun lb : ℝ × ℝ =>
    (⟨fun t => g (lb.1 * (t : ℝ) + lb.2), by fun_prop⟩ : C(↥I, ℝ)))

/-- B1 (leaf). For smooth `g`, the function `t ↦ tᵏ · g⁽ᵏ⁾(λt+b)` lies in the closure of `Sg g`:
it is a uniform-on-`I` limit of iterated finite differences in `λ` of `t ↦ g(λt+b)`. -/
theorem deriv_pow_mem {g : ℝ → ℝ} (hg : ContDiff ℝ ⊤ g) (I : Set ℝ) (hI : IsCompact I)
    (k : ℕ) (lam b : ℝ) :
    (⟨fun t => (t : ℝ) ^ k * iteratedDeriv k g (lam * (t : ℝ) + b), by fun_prop⟩ : C(↥I, ℝ))
      ∈ (Sg g I hg.continuous).topologicalClosure := by
  sorry

/-- B2 (leaf). A smooth non(everywhere-)polynomial has, for every order `k`, a point where the
`k`-th derivative is nonzero. -/
theorem exists_deriv_ne {g : ℝ → ℝ} (hg : ContDiff ℝ ⊤ g)
    (hnp : ¬ IsPolynomialFun g) (k : ℕ) : ∃ b, iteratedDeriv k g b ≠ 0 := by
  sorry

/-- B3 (glue). For smooth non-polynomial `g`, the closed span of its dilations/translations is all
of `C(I,ℝ)` on every compact interval `I`. -/
theorem smooth_engine {g : ℝ → ℝ} (hg : ContDiff ℝ ⊤ g) (hnp : ¬ IsPolynomialFun g)
    (I : Set ℝ) (hI : IsCompact I) :
    (Sg g I hg.continuous).topologicalClosure = ⊤ := by
  sorry
```

- [ ] **Step 2: Leaf `deriv_pow_mem` — write docstring + `sorry` only.** Document the intended proof: `∂_λ g(λt+b) = t·g'(λt+b)` (`HasDerivAt`, chain rule), the difference quotient `(g((λ+s)t+b) - g(λt+b))/s ∈ Sg` converges uniformly on `I` to `t·g'(λt+b)` as `s→0` (uniform because `g'` is uniformly continuous on the compact image), then induct on `k`. Leave as documented `sorry` this cycle.

- [ ] **Step 3: Leaf `exists_deriv_ne` — write docstring + `sorry` only.** Document: contrapositive of `iteratedDeriv_eq_zero_imp_poly` — if `iteratedDeriv k g b = 0` for all `b`, then `g` is a polynomial of degree `< k`, contradicting `hnp`. (This one is *nearly* glue given Task 1's leaf; if `iteratedDeriv_eq_zero_imp_poly` is in hand it can be proved outright — prefer proving it. Only `sorry` if the contradiction wiring is awkward.)

- [ ] **Step 4: Prove `smooth_engine` (glue).** Strategy:
  1. From `deriv_pow_mem` at `lam = 0`: `t ↦ tᵏ · g⁽ᵏ⁾(b) ∈ closure(Sg)` for every `b` (note `0 * t + b = b`).
  2. From `exists_deriv_ne k`: pick `b_k` with `g⁽ᵏ⁾(b_k) ≠ 0`; divide ⇒ the monomial `t ↦ tᵏ ∈ closure(Sg)` (`Submodule.smul_mem` by `(g⁽ᵏ⁾(b_k))⁻¹`).
  3. All monomials ⇒ all polynomial functions ∈ `closure(Sg)` (submodule + span of monomials).
  4. Polynomials are dense in `C(↥I,ℝ)` for compact `I`: Weierstrass / Stone–Weierstrass — candidate `polynomialFunctions_closure_eq_top` (for intervals) or the subalgebra Stone–Weierstrass `ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`. Hence `closure(Sg) = ⊤`.
  Verify the polynomial-density name with `lean_leansearch`/`lean_local_search`; this is the one external dependency.

- [ ] **Step 5: Verify** — `lean_diagnostic_messages`: no `error`; `sorry` only on `deriv_pow_mem` (and `exists_deriv_ne` if not proved).

- [ ] **Step 6: Commit**

```bash
git add LeanPlayground/UniversalApproximation/Leshno/SmoothEngine.lean
git commit -m "feat(leshno): univariate smooth derivative-trick engine (B1/B2 leaves, B3 assembled)

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 5: `Mollify.lean` — convolution, smoothness, nonpoly mollifier, and the M-class membrane (A)

**Files:**
- Create: `LeanPlayground/UniversalApproximation/Leshno/Mollify.lean`

**Interfaces:**
- Consumes: `ClassM` (Task 2), `genSpan` / `T` / `ApproxByGen` (Task 3).
- Produces: `mollify`, `contDiff_mollify` (E), `exists_nonpoly_mollify` (D, leaf), `mollify_ridge_mem_T` (A, leaf). Consumed by Task 8.

- [ ] **Step 1: Write defs + statements with `sorry`:**

```lean
import Mathlib
import LeanPlayground.UniversalApproximation.Leshno.ClassM
import LeanPlayground.UniversalApproximation.Leshno.Family

namespace UniversalApproximation.Leshno

open MeasureTheory
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Mollification of `σ` by a smooth compactly-supported kernel `φ` (convolution). -/
noncomputable def mollify (σ φ : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∫ y, σ (x - y) * φ y

/-- E. The mollification of an `M`-class `σ` by a smooth compactly-supported kernel is smooth. -/
theorem contDiff_mollify {σ φ : ℝ → ℝ} (hσ : ClassM σ) (hφ : ContDiff ℝ ⊤ φ)
    (hφc : HasCompactSupport φ) : ContDiff ℝ ⊤ (mollify σ φ) := by
  sorry

/-- D (leaf). A non-a.e.-polynomial `M`-class `σ` admits a smooth compactly-supported kernel whose
mollification is not an everywhere polynomial. -/
theorem exists_nonpoly_mollify {σ : ℝ → ℝ} (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ⊤ φ ∧ HasCompactSupport φ ∧ ¬ IsPolynomialFun (mollify σ φ) := by
  sorry

/-- A (leaf, hard M-class core). For `M`-class `σ`, every dilated/translated ridge of the smooth
mollification `σ⋆φ` lies in the continuous-core submodule `T`: it is an everywhere-sup limit on `K`
of `genSpan` elements (Riemann sums of the convolution integral). -/
theorem mollify_ridge_mem_T {σ φ : ℝ → ℝ} (hσ : ClassM σ) (hφ : ContDiff ℝ ⊤ φ)
    (hφc : HasCompactSupport φ) (K : Set E) (w : E) (b lam c : ℝ)
    (hcont : Continuous fun x : ↥K => mollify σ φ (lam * (⟪w, (x : E)⟫ + b) + c)) :
    (⟨fun x : ↥K => mollify σ φ (lam * (⟪w, (x : E)⟫ + b) + c), hcont⟩
      : C(↥K, ℝ)) ∈ T σ K := by
  sorry
```

- [ ] **Step 2: Prove (or leaf) `contDiff_mollify` (E).** Try Mathlib's convolution smoothness first: search `lean_leansearch` "convolution is smooth compact support" / `lean_loogle` for `ContDiff _ _ (_ ⋆ _)`. Candidate names: `HasCompactSupport.contDiff_convolution_right`, `MeasureTheory.convolution`, `ContDiffBump`. If the project's `mollify` (written as a bare integral) doesn't line up with Mathlib's `convolution`, either restate `mollify` via `MeasureTheory.convolution … (ContinuousLinearMap.mul ℝ ℝ) …` to reuse the lemma, or leave `contDiff_mollify` as a documented `sorry` leaf (permitted). Prefer reusing Mathlib.

- [ ] **Step 3: Leaf `exists_nonpoly_mollify` (D) — docstring + `sorry`.** Document: if `mollify σ φ` were an everywhere polynomial for *every* smooth compactly-supported `φ`, then `σ` is a.e. a polynomial (standard distribution-theory fact: a distribution all of whose mollifications are polynomials of uniformly bounded degree is a polynomial; the degree bound comes from `(d/dx)^N (σ⋆φ) = σ⋆φ^(N)`). Contrapositive gives the witness. Leave as documented `sorry`.

- [ ] **Step 4: Leaf `mollify_ridge_mem_T` (A) — docstring + `sorry`.** This is THE hard analytic step. Document precisely: `(σ⋆φ)(s) = ∫ σ(s-y)φ(y) dy` is approximated uniformly for `s` in the compact image `(lam(⟪w,·⟫+b)+c)(K)` by Riemann sums `∑ᵢ σ(s - yᵢ)φ(yᵢ)Δ`; each Riemann-sum-as-a-function-of-`x` is a finite combination of `genFun σ (lam•w) (lam*b + c - yᵢ)` (reparametrisation, cf. `genFun_reparam_mem`), hence in `genSpan`; uniform convergence on the compact image (using `ClassM.locBdd` + `ClassM.discNull` for uniform control of the Riemann error of the a.e.-continuous integrand) gives membership in `ApproxByGen`, i.e. in `T`. Cross-reference the conditional `ForMathlib` row (Riemann-sum convolution approximation). Leave as documented `sorry`.

- [ ] **Step 5: Verify** — `lean_diagnostic_messages`: no `error`; `sorry` on `exists_nonpoly_mollify`, `mollify_ridge_mem_T` (and `contDiff_mollify` only if not reused from Mathlib).

- [ ] **Step 6: Commit**

```bash
git add LeanPlayground/UniversalApproximation/Leshno/Mollify.lean
git commit -m "feat(leshno): mollification — smoothness (E), nonpoly mollifier (D leaf), σ⋆φ∈T (A leaf)

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 6: `Ridge.lean` — univariate ⇒ multivariate (C)

**Files:**
- Create: `LeanPlayground/UniversalApproximation/Leshno/Ridge.lean`

**Interfaces:**
- Consumes: `genSpan`/`T`/`ApproxByGen` (Task 3), `ridgePow_span` (Task 1). Takes univariate density as a hypothesis (supplied in Task 8), so it does NOT import `SmoothEngine`/`Mollify`.
- Produces: `ridge_mem_T` (C1, glue), `ridge_density` (C, glue, parameterised by a univariate-density hypothesis). Consumed by Task 8.

- [ ] **Step 1: Write statements with `sorry`.** Express the univariate-density hypothesis in terms already available (`T` on 1-D compacta), e.g.:

```lean
import Mathlib
import LeanPlayground.UniversalApproximation.Leshno.Family
import LeanPlayground.ForMathlib.RidgePowersSpan

namespace UniversalApproximation.Leshno

open scoped RealInnerProductSpace
open Topology

variable {n : ℕ}

/-- The univariate-density hypothesis, abstracted: on every compact real interval the family of
1-D generators of `σ` reaches every continuous function. (Discharged in Task 8 from the smooth
engine + mollification.) -/
def UnivariateDense (σ : ℝ → ℝ) : Prop :=
  ∀ (I : Set ℝ), IsCompact I → T σ I = ⊤    -- 1-D instance: EuclideanSpace ℝ (Fin 1) identified with ℝ; see impl note

/-- C1 (glue). Given univariate density, every continuous ridge `x ↦ h(⟪a,x⟫)` lies in `T`. -/
theorem ridge_mem_T {σ : ℝ → ℝ} (hσu : UnivariateDense σ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (a : EuclideanSpace ℝ (Fin n)) (h : C(ℝ, ℝ)) :
    (⟨fun x : ↥K => h ⟪a, (x : EuclideanSpace ℝ (Fin n))⟫, by fun_prop⟩ : C(↥K, ℝ)) ∈ T σ K := by
  sorry

/-- C (glue). Given univariate density, the continuous-core submodule is everything. -/
theorem ridge_density {σ : ℝ → ℝ} (hσu : UnivariateDense σ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) : T σ K = ⊤ := by
  sorry
```

Impl note for `UnivariateDense`: the cleanest formalisation of the 1-D family may be on `ℝ` directly rather than `EuclideanSpace ℝ (Fin 1)`. Fix the precise encoding when writing — it must be the same object the smooth engine (Task 4) produces and the multivariate ridge (here) consumes. Resolve this so all three statements elaborate, then `sorry` the proofs.

- [ ] **Step 2: Prove `ridge_mem_T` (C1).** For `x ∈ K`, `⟪a,x⟫` ranges over the compact image `I := (⟪a,·⟫)'' K`. By `hσu I`, `h|_I ∈ T σ I`, so `h|_I` is approximable on `I` by `∑ cᵢ σ(λᵢ s + bᵢ)`; substituting `s = ⟪a,x⟫` gives `∑ cᵢ σ(⟪λᵢ•a, x⟫ + bᵢ) ∈ genSpan σ K` (reparametrisation, `genFun_reparam_mem` with `lam = λᵢ`, `w = a`, `b = 0`, `c = bᵢ`), and the sup-error transfers because `s = ⟪a,x⟫ ∈ I`. Hence `ApproxByGen σ K (ridge)`. Genuine proof.

- [ ] **Step 3: Prove `ridge_density` (C).** From C1, every continuous ridge is in `T`. In particular every ridge *power* `x ↦ (⟪a,x⟫)ᵏ` (take `h = (·)^k ∈ C(ℝ,ℝ)`) is in `T`. By `ridgePow_span`, these span the homogeneous degree-`k` polynomial functions; summing over `k` ⇒ all polynomial functions ∈ `T`. Polynomials are dense in `C(↥K,ℝ)` for compact `K ⊆ EuclideanSpace ℝ (Fin n)` (multivariate Weierstrass / Stone–Weierstrass: the polynomial functions form a point-separating subalgebra containing constants — `ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`). With `T` closed (`T_isClosed`), `T = ⊤`. Verify the Stone–Weierstrass name; this is the main external dependency.

- [ ] **Step 4: Verify** — `lean_diagnostic_messages`: no `error`; **no `sorry`** (both lemmas are glue). Contingency rule applies if a sub-step is intractable.

- [ ] **Step 5: Commit**

```bash
git add LeanPlayground/UniversalApproximation/Leshno/Ridge.lean
git commit -m "feat(leshno): ridge lift — univariate density ⇒ T=⊤ via ridge powers + Stone–Weierstrass

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 7: `Converse.lean` — a.e.-polynomial ⇒ not dense (⇒)

**Files:**
- Create: `LeanPlayground/UniversalApproximation/Leshno/Converse.lean`

**Interfaces:**
- Consumes: `ClassM`/`IsAEPolynomial` (Task 2), `genSpan`/`DenselyApproximates` (Task 3).
- Produces: `aePolynomial_not_dense`. Consumed by Task 8.

- [ ] **Step 1: Write statement with `sorry`:**

```lean
import Mathlib
import LeanPlayground.UniversalApproximation.Leshno.ClassM
import LeanPlayground.UniversalApproximation.Leshno.Family

namespace UniversalApproximation.Leshno

/-- (⇒) If `σ` is a.e. a polynomial, the family is not dense: every finite combination of
generators agrees off a null set with a polynomial of bounded degree, and continuity of the target
turns this into an everywhere obstruction on a suitable compact set. -/
theorem aePolynomial_not_dense {σ : ℝ → ℝ} (hp : IsAEPolynomial σ) :
    ¬ DenselyApproximates σ := by
  sorry
```

- [ ] **Step 2: Prove `aePolynomial_not_dense` (glue).** Strategy: let `p` have degree `d` with `σ =ᵐ p`. Work in `n = 1`, `K = Icc 0 1` (a positive-measure compact). For any `g ∈ genSpan σ K`, `g = ∑ cᵢ genFun σ wᵢ bᵢ`; each `genFun σ wᵢ bᵢ =ᵐ` a degree-`≤ d` polynomial in `x` (compose `σ =ᵐ p` with the affine map; affine pushforward of a null set is null). So `g` agrees a.e. on `K` with some `q ∈` (the `(d+1)`-dimensional) space `P_d` of degree-`≤ d` polynomial functions. Choose `f := genuinely non-polynomial continuous`, e.g. `f(x) = |x - 1/2|` or `cos(2π·(d+2)·x)` — a continuous function whose sup-distance to `P_d` on `K` is bounded below by some `δ > 0` (`P_d` is finite-dimensional ⇒ closed ⇒ positive distance from `f ∉ P_d`). Then for any `g`, since `g =ᵐ q` and both `f` and (the continuous representative issue) — handle the a.e.-vs-everywhere gap: the approximation bound `∀x, |f x - g x| < ε` holds *everywhere*, in particular a.e., giving `‖f - q‖_{L^∞(K)} ≤ ε`; but continuity of `f` and finite-dimensionality force `dist(f, P_d) ≥ δ`. Pick `ε = δ/2` to contradict `DenselyApproximates`. Candidate facts: `Submodule.finrank` / finite-dimensional subspaces are closed (`Submodule.closed_of_finiteDimensional`), distance to a closed set is positive for points outside. If the a.e.-to-sup bridge is fiddly, isolate it as a small private lemma. Genuine proof; if a measure-zero subtlety proves stubborn, the contingency rule permits a single documented `sorry` here, reported prominently.

- [ ] **Step 3: Verify** — `lean_diagnostic_messages`: no `error`; target **no `sorry`**.

- [ ] **Step 4: Commit**

```bash
git add LeanPlayground/UniversalApproximation/Leshno/Converse.lean
git commit -m "feat(leshno): converse — a.e.-polynomial activation is not dense

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 8: `Theorem.lean` — assemble `leshno_dense_iff`; root re-export

Assembles the univariate density (A+D+E+`smooth_engine`+reparam invariance), feeds it to `ridge_density`, gets `T = ⊤` for all `K`, then the forward direction via `denselyApproximates_of_forall_T_eq_top`, and pairs it with the converse. (`univariate_density` and the final `T = ⊤` live here, not in `Family.lean`, to keep imports acyclic — `Family` is imported by everything, whereas this assembly needs `Mollify`, `SmoothEngine`, `Ridge`.)

**Files:**
- Create: `LeanPlayground/UniversalApproximation/Leshno/Theorem.lean`
- Create: `LeanPlayground/UniversalApproximation/Leshno.lean` (root re-export)

**Interfaces:**
- Consumes: everything from Tasks 2–7.
- Produces: `univariate_density`, `leshno_dense` (forward), `leshno_dense_iff` (headline).

- [ ] **Step 1: Write `Theorem.lean` statements with `sorry`:**

```lean
import Mathlib
import LeanPlayground.UniversalApproximation.Leshno.ClassM
import LeanPlayground.UniversalApproximation.Leshno.Family
import LeanPlayground.UniversalApproximation.Leshno.SmoothEngine
import LeanPlayground.UniversalApproximation.Leshno.Mollify
import LeanPlayground.UniversalApproximation.Leshno.Ridge
import LeanPlayground.UniversalApproximation.Leshno.Converse

namespace UniversalApproximation.Leshno

/-- Univariate density: a non-a.e.-polynomial `M`-class `σ` reaches every continuous function on
every compact real set, through its mollification + the smooth engine. -/
theorem univariate_density {σ : ℝ → ℝ} (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ) :
    UnivariateDense σ := by
  sorry

/-- Forward direction: non-a.e.-polynomial ⇒ dense. -/
theorem leshno_dense {σ : ℝ → ℝ} (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ) :
    DenselyApproximates σ := by
  sorry

/-- **Leshno–Lin–Pinkus–Schocken (1993).** An `M`-class activation densely approximates iff it is
not (a.e.) a polynomial. -/
theorem leshno_dense_iff {σ : ℝ → ℝ} (hσ : ClassM σ) :
    DenselyApproximates σ ↔ ¬ IsAEPolynomial σ := by
  sorry
```

- [ ] **Step 2: Prove `univariate_density` (glue).** For a compact `I ⊆ ℝ`: get `φ` from `exists_nonpoly_mollify hσ hnp`; `g₀ := mollify σ φ` is smooth (`contDiff_mollify`) and not an everywhere polynomial (`exists_nonpoly_mollify`). Apply `smooth_engine hg₀ hnp₀ I hI`: `closure(Sg g₀ I) = ⊤`. Now show `Sg g₀ I ≤ T σ I`: each generator `t ↦ g₀(λt+b)` of `Sg` is a ridge of the mollification, in `T σ I` by `mollify_ridge_mem_T` instantiated at `E = ℝ`, `w = 1` (so `⟪1,t⟫ = t`), inner `b = 0`, `lam = λ`, `c = b` (giving `mollify σ φ (λ·t + b) = g₀(λt+b)`); since `T` is a submodule, `Sg g₀ I ≤ T σ I`, and since `T` is closed (`T_isClosed`), `closure(Sg g₀ I) ≤ T σ I`. With the former `= ⊤`, `T σ I = ⊤`. (This is where the `E = ℝ` instance of `T`/`genSpan` from Task 3 must line up with Task 5's `mollify_ridge_mem_T` and the `Sg` of Task 4.)

- [ ] **Step 3: Prove `leshno_dense` (glue).** `denselyApproximates_of_forall_T_eq_top` applied to `fun K hK => ridge_density (univariate_density hσ hnp) K hK`.

- [ ] **Step 4: Prove `leshno_dense_iff` (glue).** `⟨forward, backward⟩`: the `←` (mpr) is `leshno_dense hσ`; the `→` (mp) is the contrapositive `not_imp_not.mpr (aePolynomial_not_dense)` — i.e. `dense ⇒ ¬ a.e.-poly` is `(aePolynomial_not_dense)`'s contrapositive. Wire with `Iff.intro` + `not_not` as needed.

- [ ] **Step 5: Write the root re-export `Leshno.lean`:**

```lean
import LeanPlayground.UniversalApproximation.Leshno.ClassM
import LeanPlayground.UniversalApproximation.Leshno.Family
import LeanPlayground.UniversalApproximation.Leshno.SmoothEngine
import LeanPlayground.UniversalApproximation.Leshno.Mollify
import LeanPlayground.UniversalApproximation.Leshno.Ridge
import LeanPlayground.UniversalApproximation.Leshno.Converse
import LeanPlayground.UniversalApproximation.Leshno.Theorem

/-!
# Leshno Universal Approximation (M-class) — scaffold root
Re-exports the Leshno development and records the admit inventory (the analytic leaves left as
documented `sorry` this cycle): `iteratedDeriv_eq_zero_imp_poly`, `ridgePow_span`, `deriv_pow_mem`,
`exists_deriv_ne`, `exists_nonpoly_mollify`, `mollify_ridge_mem_T` (and possibly `contDiff_mollify`).
Everything else — the family/`T` infrastructure, the ridge lift, the converse, and the final
`leshno_dense_iff` assembly — is proved.
-/
```

- [ ] **Step 6: Verify the whole development.** Run `lean_diagnostic_messages` on `Theorem.lean` and `Leshno.lean`: no `error`; `sorry` warnings only on the named leaves (Tasks 1/4/5). Then `mcp__lean-lsp__lean_build` (or `lake build LeanPlayground.UniversalApproximation.Leshno`) to confirm the module and all imports compile together. Update `docs/superpowers/mathlib-contributions.md` statuses.

- [ ] **Step 7: Commit**

```bash
git add LeanPlayground/UniversalApproximation/Leshno/Theorem.lean LeanPlayground/UniversalApproximation/Leshno.lean docs/superpowers/mathlib-contributions.md
git commit -m "feat(leshno): assemble leshno_dense_iff + root re-export; full M-class scaffold compiles

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Final verification (whole branch)

- [ ] `lake build LeanPlayground.UniversalApproximation.Leshno` succeeds (and `lake build` of the existing default target still succeeds — the Cybenko files are untouched).
- [ ] `git grep -n "sorry" LeanPlayground/UniversalApproximation/Leshno LeanPlayground/ForMathlib` lists **only** the named leaves; no stray sorries in glue.
- [ ] `leshno_dense_iff`, `leshno_dense`, `univariate_density`, `ridge_density`, `denselyApproximates_of_forall_T_eq_top` are present and (apart from depending on the leaves) `sorry`-free.
- [ ] `docs/superpowers/mathlib-contributions.md` reflects final statuses.
