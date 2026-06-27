# Repository Reorg, Rename, CI, CLAUDE.md — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Rename the project `LeanPlayground` → `NeuralNetworkProofs`, restructure into
`ForMathlib/` + `NeuralNetwork/` + `UniversalApproximation/{Cybenko,Leshno}/` with namespaces aligned,
re-export both UAT roots from the package root, add CI (cache + full build + sorry-free axiom gate),
and add `CLAUDE.md`.

**Architecture:** A mechanical move/rename refactor. Each task ends build-green with the two headline
theorems still `sorryAx`-free (verified via `#print axioms` on freshly-built oleans). No proof content
changes — only file locations, module-path prefixes, namespaces, import lines, docstrings, plus two
new files (CI, CLAUDE.md). Bulk edits use `git mv` + scoped `sed`; `lake build` is the gate.

**Tech Stack:** Lean 4 + Mathlib; Lake; GitHub Actions (`leanprover/lean-action`); `gh` CLI.

## Global Constraints

- Do not change the *statement* or proof of any theorem; moves/renames/imports/docstrings only.
- Preserve git history via `git mv`.
- No new Mathlib upstream dependency.
- Line length ≤ 100 codepoints.
- A reintroduced/hidden `sorry` is never acceptable; the CI gate enforces it for the headlines.
- Commits SSH-signed (`git commit -S`).
- Math namespaces are independent of the module-path prefix: the `LeanPlayground`→`NeuralNetworkProofs`
  rename does NOT touch `UniversalApproximation.*` / per-file `ForMathlib` namespaces.
- Verification bar per code task: `lake build` green AND `#print axioms` (fresh oleans) on both
  headline theorems = `[propext, Classical.choice, Quot.sound]`.

## Baseline (branch `refactor/neural-network-proofs`, on post-#9 `main`)

```
LeanPlayground.lean                       → import LeanPlayground.UniversalApproximation(.Cybenko-root) + .Leshno + Network
LeanPlayground/
  Contrib/        (9 files, per-file namespaces, "Intended Mathlib home" headers)
  UniversalApproximation/
    Activation Discriminatory Family Network Riesz Theorem   (Cybenko, namespace UniversalApproximation)
    Leshno/ , Leshno.lean                                    (namespace UniversalApproximation.Leshno)
  UniversalApproximation.lean             (Cybenko root re-export, namespace UniversalApproximation)
lakefile.toml: name="lean_playground"; lean_lib "LeanPlayground"; defaultTargets=["LeanPlayground"]
```

Facts (verified during design): Leshno ⊥ Cybenko (no cross-refs); `Layer`/`Network` used only by
Cybenko `Family.lean`; `Contrib/TestFunctionDegreeBound.lean` imports `…Leshno.MollifyDef` (stays —
its decoupling is a separate, later PR); both headlines currently `sorryAx`-free.

---

### Task 1: Rename `LeanPlayground` → `NeuralNetworkProofs`

Pure module-path-prefix + package rename. No namespace changes, no file moves between folders.

**Files:** the whole tree (dir + root file rename; import lines; `lakefile.toml`).

**Interfaces:**
- Produces: module paths `NeuralNetworkProofs.…`; package `neural_network_proofs`; lib
  `NeuralNetworkProofs`; root file `NeuralNetworkProofs.lean`. Headline names UNCHANGED this task
  (`UniversalApproximation.universal_approximation`, `UniversalApproximation.Leshno.leshno_dense_iff`).

- [ ] **Step 1: Rename the directory and root file.**

```bash
cd /workspaces/lean-playground
git mv LeanPlayground NeuralNetworkProofs
git mv LeanPlayground.lean NeuralNetworkProofs.lean
```

- [ ] **Step 2: Rewrite all import paths.**

```bash
grep -rl 'LeanPlayground' NeuralNetworkProofs NeuralNetworkProofs.lean \
  | xargs sed -i 's/\bLeanPlayground\./NeuralNetworkProofs./g'
```
This rewrites `import LeanPlayground.X` → `import NeuralNetworkProofs.X` and any
`LeanPlayground.`-qualified mention in docstrings. (Math code uses no `LeanPlayground.`-qualified
names, so this is safe.) Verify none remain:
```bash
grep -rn 'LeanPlayground' NeuralNetworkProofs NeuralNetworkProofs.lean || echo "NONE"
```
Expected: `NONE`.

- [ ] **Step 3: Update `lakefile.toml`.**

Set `name = "neural_network_proofs"`, the `[[lean_lib]]` `name = "NeuralNetworkProofs"`, and
`defaultTargets = ["NeuralNetworkProofs"]`. (Leave `[leanOptions]` and the Mathlib `[[require]]`
untouched.) Verify:
```bash
grep -nE 'name =|defaultTargets' lakefile.toml
```
Expected: shows `neural_network_proofs`, `NeuralNetworkProofs`, `["NeuralNetworkProofs"]`.

- [ ] **Step 4: Build.**

```bash
lake build
```
Expected: `Build completed successfully`. (Our ~17 modules rebuild under the new lib name; the Mathlib
cache is unaffected.)

- [ ] **Step 5: Verify headlines still sorry-free.**

```bash
cat > /tmp/ck1.lean << 'EOF'
import NeuralNetworkProofs
open UniversalApproximation UniversalApproximation.Leshno
#print axioms universal_approximation
#print axioms leshno_dense_iff
EOF
lake env lean /tmp/ck1.lean
```
Expected: both `[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 6: Commit.**

```bash
git add -A
git commit -S -m "refactor: rename package LeanPlayground -> NeuralNetworkProofs"
```

---

### Task 2: Restructure into ForMathlib / NeuralNetwork / Cybenko, align namespaces

**Files:** `Contrib/`→`ForMathlib/`; `Network.lean`→`NeuralNetwork/`; the 5 Cybenko files +
`UniversalApproximation.lean`→`UniversalApproximation/Cybenko/` + `Cybenko.lean`; namespace edits;
import updates; root re-export `NeuralNetworkProofs.lean`.

**Interfaces:**
- Produces: headline `UniversalApproximation.Cybenko.universal_approximation` (and
  `…universal_approximation_eps`); general defs in namespace `NeuralNetwork`
  (`NeuralNetwork.Layer`, `NeuralNetwork.Network`); `ForMathlib` files unchanged in namespace.
  Leshno unchanged.

- [ ] **Step 1: Rename `Contrib` → `ForMathlib` and fix imports.**

```bash
cd /workspaces/lean-playground
git mv NeuralNetworkProofs/Contrib NeuralNetworkProofs/ForMathlib
grep -rl 'NeuralNetworkProofs.Contrib' NeuralNetworkProofs NeuralNetworkProofs.lean \
  | xargs sed -i 's/NeuralNetworkProofs\.Contrib\./NeuralNetworkProofs.ForMathlib./g'
grep -rn 'NeuralNetworkProofs.Contrib' NeuralNetworkProofs || echo "NONE"
```
Expected: `NONE`. (`ForMathlib` files keep their own per-file namespaces — no namespace edit here.)

- [ ] **Step 2: Move `Network.lean` → `NeuralNetwork/` and rename its namespace.**

```bash
mkdir -p NeuralNetworkProofs/NeuralNetwork
git mv NeuralNetworkProofs/UniversalApproximation/Network.lean \
       NeuralNetworkProofs/NeuralNetwork/Network.lean
sed -i 's/^namespace UniversalApproximation$/namespace NeuralNetwork/; \
        s/^end UniversalApproximation$/end NeuralNetwork/' \
       NeuralNetworkProofs/NeuralNetwork/Network.lean
```
Then update importers of the old path:
```bash
grep -rl 'NeuralNetworkProofs.UniversalApproximation.Network' NeuralNetworkProofs NeuralNetworkProofs.lean \
  | xargs sed -i 's/NeuralNetworkProofs\.UniversalApproximation\.Network/NeuralNetworkProofs.NeuralNetwork.Network/g'
```

- [ ] **Step 3: Move the 5 Cybenko files + root into `Cybenko/`.**

```bash
mkdir -p NeuralNetworkProofs/UniversalApproximation/Cybenko
for f in Activation Discriminatory Family Riesz Theorem; do
  git mv NeuralNetworkProofs/UniversalApproximation/$f.lean \
         NeuralNetworkProofs/UniversalApproximation/Cybenko/$f.lean
done
git mv NeuralNetworkProofs/UniversalApproximation.lean \
       NeuralNetworkProofs/UniversalApproximation/Cybenko.lean
```

- [ ] **Step 4: Rename the Cybenko namespace (exact, scoped to the 6 Cybenko files only).**

```bash
for f in Activation Discriminatory Family Riesz Theorem; do
  sed -i 's/^namespace UniversalApproximation$/namespace UniversalApproximation.Cybenko/; \
          s/^end UniversalApproximation$/end UniversalApproximation.Cybenko/' \
         NeuralNetworkProofs/UniversalApproximation/Cybenko/$f.lean
done
sed -i 's/^namespace UniversalApproximation$/namespace UniversalApproximation.Cybenko/; \
        s/^end UniversalApproximation$/end UniversalApproximation.Cybenko/' \
       NeuralNetworkProofs/UniversalApproximation/Cybenko.lean
```
NOTE: the anchored `^namespace UniversalApproximation$` pattern must NOT touch the Leshno files
(they use `namespace UniversalApproximation.Leshno`). The loop above only edits the 6 Cybenko files,
so Leshno is untouched — but double-check nothing else changed:
```bash
grep -rn '^namespace UniversalApproximation$' NeuralNetworkProofs || echo "NO BARE UA NAMESPACE LEFT"
```
Expected: `NO BARE UA NAMESPACE LEFT`.

- [ ] **Step 5: Fix Cybenko-internal imports and the `Network` open.**

Update the moved files' import paths (they import each other and `Network`):
```bash
grep -rl 'NeuralNetworkProofs.UniversalApproximation.\(Activation\|Discriminatory\|Family\|Riesz\|Theorem\)' \
     NeuralNetworkProofs \
  | xargs sed -i 's/NeuralNetworkProofs\.UniversalApproximation\.\(Activation\|Discriminatory\|Family\|Riesz\|Theorem\)/NeuralNetworkProofs.UniversalApproximation.Cybenko.\1/g'
```
In `Cybenko/Family.lean`, `Layer`/`Network` are now in namespace `NeuralNetwork` (moved out of this
file's namespace). Add `open NeuralNetwork` after the file's existing `open` lines (or qualify the
references). Confirm by building (Step 7) and, if names fail to resolve, add the `open`.

- [ ] **Step 6: Rewrite the root re-export `NeuralNetworkProofs.lean`.**

```lean
import NeuralNetworkProofs.UniversalApproximation.Cybenko
import NeuralNetworkProofs.UniversalApproximation.Leshno
import NeuralNetworkProofs.NeuralNetwork.Network

/-! # NeuralNetworkProofs — universal approximation theorems

Re-exports the formalized developments so the default `lake build` builds and verifies both headlines:

* `UniversalApproximation.Cybenko.universal_approximation` — Cybenko (1989).
* `UniversalApproximation.Leshno.leshno_dense_iff` — Leshno–Lin–Pinkus–Schocken (1993).

General neural-network infrastructure lives under `NeuralNetwork` (`NeuralNetwork.Layer`,
`NeuralNetwork.Network`); Mathlib-upstream candidates under `NeuralNetworkProofs.ForMathlib`. -/
```
(Note: `UniversalApproximation.Cybenko` is the module `…/UniversalApproximation/Cybenko.lean`.)

- [ ] **Step 7: Build and fix any unresolved references.**

```bash
lake build
```
Expected: success. If `Family.lean` reports unknown `Layer`/`Network`, add `open NeuralNetwork`. If a
Cybenko file qualified a sibling as `UniversalApproximation.Foo`, update it to
`UniversalApproximation.Cybenko.Foo`. Re-build until green.

- [ ] **Step 8: Verify headlines sorry-free (note the new Cybenko name).**

```bash
cat > /tmp/ck2.lean << 'EOF'
import NeuralNetworkProofs
open UniversalApproximation.Cybenko UniversalApproximation.Leshno
#print axioms universal_approximation
#print axioms universal_approximation_eps
#print axioms leshno_dense_iff
EOF
lake env lean /tmp/ck2.lean
```
Expected: all three `[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 9: Update the Leshno admit-inventory docstring** in
`NeuralNetworkProofs/UniversalApproximation/Leshno.lean` if it references the old Cybenko module path
or `UniversalApproximation.Network`. (Leshno's own namespaces are unchanged.) Grep and fix:
```bash
grep -n 'UniversalApproximation.Network\|UniversalApproximation\.lean' \
     NeuralNetworkProofs/UniversalApproximation/Leshno.lean || echo "none"
```

- [ ] **Step 10: Commit.**

```bash
git add -A
git commit -S -m "refactor: ForMathlib + NeuralNetwork + Cybenko/ restructure; align namespaces"
```

---

### Task 3: CI workflow with sorry-free gate

**Files:** Create `.github/workflows/ci.yml` and `scripts/check_sorry_free.lean`.

- [ ] **Step 1: Add the axiom-check Lean script.**

Create `scripts/check_sorry_free.lean`:
```lean
import NeuralNetworkProofs
open UniversalApproximation.Cybenko UniversalApproximation.Leshno
#print axioms universal_approximation
#print axioms universal_approximation_eps
#print axioms leshno_dense_iff
```

- [ ] **Step 2: Add the workflow.**

Create `.github/workflows/ci.yml`:
```yaml
name: CI
on:
  push:
    branches: [main]
  pull_request:
    branches: [main]
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Build (with Mathlib cache)
        uses: leanprover/lean-action@v1
        with:
          use-mathlib-cache: true
      - name: Sorry-free axiom gate
        run: |
          set -euo pipefail
          out=$(lake env lean scripts/check_sorry_free.lean)
          echo "$out"
          if echo "$out" | grep -q 'sorryAx'; then
            echo "::error::A headline theorem depends on sorryAx"; exit 1
          fi
```
(If `leanprover/lean-action@v1`'s input name for the cache differs, use its documented option to run
`lake exe cache get` before `lake build`; the action builds the default target, which now covers both
headlines. Confirm the action's current input names when wiring it.)

- [ ] **Step 3: Local smoke-test of the gate logic.**

```bash
out=$(lake env lean scripts/check_sorry_free.lean); echo "$out"
echo "$out" | grep -q 'sorryAx' && echo "GATE WOULD FAIL" || echo "GATE PASSES"
```
Expected: `GATE PASSES`.

- [ ] **Step 4: Commit.**

```bash
git add .github/workflows/ci.yml scripts/check_sorry_free.lean
git commit -S -m "ci: build + sorry-free axiom gate via lean-action"
```

---

### Task 4: CLAUDE.md

**Files:** Create `CLAUDE.md`.

- [ ] **Step 1: Author `CLAUDE.md`** (seed with `/init` if available, then tailor) covering:
project description (formalizing UATs for neural networks in Lean 4 + Mathlib); the folder taxonomy
and namespace map (module-path prefix `NeuralNetworkProofs` vs math namespaces
`UniversalApproximation.{Cybenko,Leshno}`, `NeuralNetwork`, `ForMathlib`); build/verify commands
(`lake build`; the `#print axioms` sorry-free check and that clean = `[propext, Classical.choice,
Quot.sound]`); conventions (lines ≤ 100 codepoints with the byte-vs-codepoint note for unicode math
glyphs; the no-`sorry`/report-blockers discipline; the `ForMathlib/` "Intended Mathlib home"
convention); and a pointer to `docs/superpowers/` for specs/plans. Keep lines ≤ 100 codepoints.

- [ ] **Step 2: Commit.**

```bash
git add CLAUDE.md
git commit -S -m "docs: add CLAUDE.md (project conventions, taxonomy, verification)"
```

---

### Task 5: Rename the GitHub repository

Controller-run (outward-facing; authorized by the maintainer). Not a subagent task.

- [ ] **Step 1: Rename on GitHub (auto-redirects; updates local `origin`).**

```bash
gh repo rename neural-network-proofs --yes
git remote -v
```
Expected: `origin` now points at `…/neural-network-proofs`.

- [ ] **Step 2: Note the manual follow-up.** The local checkout directory
`/workspaces/lean-playground` and the devcontainer mount are environment-level and are left as-is
(renaming them mid-session breaks paths); flag to the maintainer as an optional manual step.

---

## Self-Review

**Spec coverage.** Rename (pkg/lib/dir/file/imports/`defaultTargets`/repo) → Tasks 1,5. Restructure
(`ForMathlib`, `NeuralNetwork`, `Cybenko/`) + namespace alignment + root re-export → Task 2. CI with
sorry-free gate → Task 3. CLAUDE.md → Task 4. `Monotone/` reserved (not created) — honored (no task
creates it). `TestFunctionDegreeBound` Leshno wrinkle — left in place (the decoupling is a separate
parked PR). Covered.

**Placeholder scan.** No "TBD"/"implement later". The one soft spot — `lean-action`'s exact cache
input name (Task 3 Step 2) — is flagged with a concrete fallback (`lake exe cache get`), not a vague
gesture. CLAUDE.md content is enumerated explicitly.

**Type/path consistency.** Module prefix `NeuralNetworkProofs` is used uniformly after Task 1; the
restructure paths (`…ForMathlib.`, `…NeuralNetwork.Network`, `…UniversalApproximation.Cybenko.`) are
consistent across Task 2 and the CI script (Task 3) and root re-export. Headline names: Task 1 keeps
`UniversalApproximation.universal_approximation`; Task 2 onward (and Tasks 3) use
`UniversalApproximation.Cybenko.universal_approximation` — the check scripts `ck1.lean` vs
`ck2.lean`/`check_sorry_free.lean` reflect this transition correctly.
