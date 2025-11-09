# Ideal Families in Lean 4 — Average Rarity (NDS ≤ 0)

This repository contains a complete Lean 4 formalization showing that **ideal families are rare on average**, i.e. their **normalized degree sum (NDS)** is non‑positive.

> **Main theorem (informal).** For any finite ideal family \(F\) over a ground set \(U\),
> \[\mathrm{NDS}(F) := 2\,\sum_{H\in F}|H| \;\; -\;\; |U|\cdot |F| \;\;\le 0.\]
> By double counting, NDS ≤ 0 implies the existence of a **rare vertex**.

The formal statement appears in the Lean files under `IdealFamily/` (see the layout below). All proofs compile with Lean **v4.24.0** and current mathlib.

---

## Mathematical setting

- A **set family** on a finite ground set `U : Finset α` is given by a predicate `sets : Finset α → Prop` with the side condition `inc_ground : ∀ s, sets s → s ⊆ U` and `nonempty_ground : U.Nonempty`.
- An **ideal family** is a set family that (i) contains `∅`, (ii) contains `U`, and (iii) is **downward‑closed strictly below** the top element `U`:
  ```lean
  down_closed : ∀ A B, sets B → B ≠ ground → A ⊆ B → sets A
  ```
  (So every proper member generates its entire downward closure; the ground itself is included by axiom, not by closure.)
- The **normalized degree sum (NDS)** is
  ```lean
  nds(F) = 2 * totalSize(F) - numEdges(F) * |U|
  ```
  where `totalSize(F)` is the sum of sizes of all members and `numEdges(F)` is the number of members.

---

## What is formalized

1. **Exact counting identities.** Double counting of incidence (degrees vs. sizes), and clean split formulae for deletion, contraction, and trace around a vertex `v`.
2. **Trace/Contraction calculus.** When `deg(v)=1`, trace is used; otherwise contraction/deletion are combined. We prove precise relations for `numEdges`, `totalSize`, and hence NDS across these minors.
3. **Main inequality (NDS ≤ 0).** An induction on `|U|` assembles the minor relations with a case analysis on whether `{v}` and `U \ {v}` are members.
4. **Rare vertex from average rarity.** From NDS ≤ 0 and degree–size double counting, a rare vertex exists.

The formal development mirrors the paper’s natural‑language structure while adopting Lean‑friendly refactorings (short lemmas; explicit set‑theoretic partitions; one‑import‑per‑line; no `simpa using`).

---

## Repository layout

```
IdealFamily/
  Core.lean            -- basic structures (SetFamily/Ideal), degree/nds/numEdges/totalSize
  TraceGuarded.lean    -- trace on ideals; carrier decompositions and closure below top
  Contraction.lean     -- contraction and S/del/contr carriers; counting lemmas
  Minors.lean          -- uniform interface for deletion/trace/contraction on ideals
  NDS.lean             -- global double counting; helper inequalities for NDS
  NDSDiff2.lean        -- ΔNDS under trace: split lemmas and the main difference theorem
  Proofs.lean          -- induction on |U| and case splits leading to NDS ≤ 0
  Corollaries.lean     -- rare-on-average ⇒ rare-vertex; small-|U| base cases, utilities
```

> **Note.** Filenames may be slightly different if you are following earlier drafts; this README reflects the current refactored structure centered on the `IdealFamily` namespace.

---

## Building the project

This project targets **Lean v4.24.0** with `lakefile.toml`.

```bash
# 1) Clone
git clone https://github.com/kashiwabarakenji/frankl_lean.git
cd frankl_lean

# 2) Pin Lean 4.24.0 (via elan)
elan override set leanprover/lean4:v4.24.0

# 3) Fetch deps and build
lake update
lake build
```

### VS Code
Open the folder in VS Code with the Lean 4 extension. Start the Lean server; hover/`Ctrl+Click` to navigate definitions. All files should compile cleanly.

---

## How the proof is organized

1. **Incidence double counting.**
   `∑_{v∈U} deg(v) = ∑_{H∈F} |H|` (proved for finite `U`). This identity underpins NDS.
2. **Local split at a vertex `v`.** Partition the carrier into
   - `delCarrier v` (members avoiding `v`),
   - `S v` (members containing `v`),
   - and for trace/contraction, the images of `S v` under `erase v`.
   We prove disjointness and exact cardinality/sum relations between these parts.
3. **Minor relations.** Exact formulas for how `numEdges` and `totalSize` transform under deletion, contraction, and trace; when `deg(v)=1`, trace’s Δ‑form simplifies.
4. **Induction on |U|.** Combine the minor relations with a case split on membership of `{v}` and `U \ {v}`. Base cases are handled explicitly in `Corollaries.lean`.

---

## Selected formal statements (names may differ slightly)

- `IdealFamily.SetFamily.degree_eq_cardS_z`
- `IdealFamily.SetFamily.card_contr_eq_cardS`
- `IdealFamily.SetFamily.sum_card_contr_eq_sum_cardS_sub_one`
- `Ideal.Ideal.nds_diff_trace_as_normdeg`
- Main goal in `Proofs.lean`: NDS(F) ≤ 0 for all ideal families F on finite U

These lemmas encapsulate the combinatorial heart of the argument (set partitions and exact algebraic reorganizations), making the final inequality largely an assembly by `ring`.

---

## Contributing / Reproducing

- The code follows a **one‑import‑per‑line** policy and avoids `induction'` and `simpa using` to keep proofs transparent.
- If you add lemmas, prefer small local facts with explicit hypotheses (e.g. subset/erase/union/sdiff identities over `Finset`).
- All crucial calculations are stated over `ℤ` to avoid coercion noise in the final algebraic rearrangements.

---

## Acknowledgements

Development benefited from interactive assistance tools. Earlier drafts relied on Lean Copilot for small steps, but the current refactor compiles on plain Lean 4.24.0 + mathlib.

---

## License

Unless otherwise stated in the source files, this work is released under the MIT license.
