/-
  IdealFamily/Proofs.lean

  Purpose.
    Paper-facing “front door” theorems: we restate the key statements under
    names that match the prose of the manuscript, delegating proofs to the
    previously verified files (Core / TraceGuarded / Contraction / NDSDiff /
    Corollaries). This file is intended to be cited from the paper as the
    canonical reference of the main claims.

  Style policy.
    – One import per line.
    – No `induction'`, no `simpa using`.
    – Keep proofs as thin wrappers around established lemmas.
-/
import IdealFamily.Core
import IdealFamily.TraceGuarded
import IdealFamily.Contraction
import IdealFamily.NDSDiff
import IdealFamily.Corollaries
--import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic

namespace IdealFamily

/- ********************  Set-family level (no ideal closure needed)  ******************** -/

namespace SetFamily

open Finset
open scoped BigOperators

noncomputable section

variable {α : Type*} [DecidableEq α]
variable (SF :SetFamily α) [DecidablePred SF.sets]

/-- Theorem (Double counting for Frankl NDS).
    The sum of normalized degrees equals `nds`.  Matches the manuscript’s
    “Σ normalized degree = NDS” identity. -/
theorem nds_eq_sum_of_normalized_degrees :
  SF.nds = ∑ v ∈ SF.ground, SF.normalizedDegreeAt v := by
  -- Just restate `sum_normalizedDegree_over_ground_eq_nds` with sides swapped.
  have H := SetFamily.sum_normalizedDegree_over_ground_eq_nds (SF := SF)
  -- H : Σ_v nd(v) = nds
  -- We want: nds = Σ_v nd(v).
  exact H.symm

/-- Theorem (Total degree equals total size).
    `Σ_v deg(v) = totalSize`.  Paper uses it implicitly before normalizing. -/
theorem total_degree_equals_total_size :
  ∑ v ∈ SF.ground, SF.degree v = SF.totalSize := by
  exact SetFamily.sum_degree_over_ground_eq_totalSize (SF := SF)

/-- Corollary (Nat-level).
    `Σ_v degNat(v) = Σ_s |s|`. -/
theorem total_degreeNat_equals_total_sizeNat :
  ∑ v ∈ SF.ground, SF.degreeNat v = ∑ s ∈ SF.carrier, s.card := by
  exact SetFamily.sum_degreeNat_over_ground_eq_totalSizeNat (SF := SF)

end
end SetFamily

/- ********************  Ideal level (down-closed w/ ground)  ******************** -/

namespace Ideal

open Finset
open scoped BigOperators

noncomputable section

variable {α : Type*} [DecidableEq α]
variable (F : Ideal α) [DecidablePred F.sets]

--local notation "SF" => F.toSetFamily

/- Definition (rare vertex, paper wording).
    A vertex is *rare* if its normalized degree is nonpositive. -/
--def rare (v : α) : Prop := (F.toSetFamily).normalizedDegreeAt v ≤ 0

/-- Theorem (Existence of a rare vertex at nonpositive NDS).
    If `nds(F) ≤ 0` and `U ≠ ∅`, there exists `v ∈ U` with `normalizedDegreeAt v ≤ 0`. -/
theorem exists_rare_when_nds_nonpos
  (hneU : F.ground.Nonempty)
  (hN : (F.toSetFamily).nds ≤ 0) :
  ∃ v ∈ F.ground, F.rare v := by
  -- Thin wrapper of `exists_rare_of_nds_le_zero`.
  exact Ideal.exists_rare_of_nds_le_zero (F := F) hneU hN

/-- Theorem (Exact 1-step trace difference).
    For `v ∈ U` and `(U\\{v})` nonempty, the NDS difference under the trace at `v`
    equals `normalizedDegreeAt v` plus the intersection block.  This is the exact
    identity used throughout the paper. -/
theorem nds_trace_exact_difference
  (v : α)
  (hvU : v ∈ F.ground)
  (hne : (F.ground.erase v).Nonempty) :
  (F.toSetFamily).nds - (F.traceIdeal v hne).toSetFamily.nds
    =
  (F.toSetFamily).normalizedDegreeAt v
    + ∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v),
        ((2 : ℤ) * (t.card : ℤ) - ((F.ground.card : ℤ) - 1)) := by
  exact Ideal.nds_diff_trace_as_normdeg (F := F) (v := v) hvU hne

/-- Corollary (Lower bound under nonnegative intersection terms).
    If each intersection term is ≥ 0, then the trace drop is ≥ the normalized degree. -/
theorem nds_trace_drop_ge_normalized_degree
  (v : α)
  (hvU : v ∈ F.ground)
  (hne : (F.ground.erase v).Nonempty)
  (hge :
     ∀ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v),
       (2 : ℤ) * (t.card : ℤ) - ((F.ground.card : ℤ) - 1) ≥ 0) :
  (F.toSetFamily).nds - (F.traceIdeal v hne).toSetFamily.nds
    ≥ (F.toSetFamily).normalizedDegreeAt v := by
  exact Ideal.diff_ge_normdeg_if_inter_terms_nonneg
          (F := F) (v := v) hvU hne hge

/-- Theorem (Deg=1 specialization: trace equals normalized degree drop).
    If `deg(v)=1` and `U\\{v} ∉ F`, then the intersection block vanishes and
    the NDS drop under trace is exactly the normalized degree at `v`. -/
theorem nds_trace_drop_eq_normalized_degree_deg1
  (v : α)
  (hvU   : v ∈ F.ground)
  (hdeg1 : (F.toSetFamily).degreeNat v = 1)
  (hne   : (F.ground.erase v).Nonempty)
  (hnot  : ¬ F.sets (F.ground.erase v)) :
  (F.toSetFamily).nds - (F.traceIdeal v hne).toSetFamily.nds
    = (F.toSetFamily).normalizedDegreeAt v := by
  exact Ideal.nds_diff_deg1_groundErase_notin
          (F := F) (v := v) hvU hdeg1 hne hnot

/-- Corollary (Nonnegativity of NDS from nonnegative normalized degrees).
    If all normalized degrees are ≥ 0, then `nds(F) ≥ 0`. -/
theorem nds_nonneg_if_all_vertices_nonneg :
  (∀ v ∈ F.ground, 0 ≤ (F.toSetFamily).normalizedDegreeAt v) → 0 ≤ (F.toSetFamily).nds := by
  intro hAll
  -- Using `nds = Σ_v nd(v)` and termwise nonnegativity.
  have Hsum := SetFamily.sum_normalizedDegree_over_ground_eq_nds (SF := (F.toSetFamily))
  -- Σ nd(v) ≥ 0 ⇒ nds ≥ 0
  -- Formalize as: 0 ≤ Σ nd(v) = nds
  have hs :
      0 ≤ ∑ v ∈ F.ground, (F.toSetFamily).normalizedDegreeAt v := by
    -- sum of nonnegative terms ≥ 0
    -- we show `∑ 0 ≤ ∑ nd`, then evaluate LHS as 0.
    have hmono :
        ∀ v ∈ F.ground, (0 : ℤ) ≤ (F.toSetFamily).normalizedDegreeAt v := by
      intro v hv; exact hAll v hv
    -- Σ 0 = 0
    have hleft : ∑ _v ∈ F.ground, (0 : ℤ) = 0 := by simp_all only [implies_true, sum_const_zero]
    -- monotonicity gives Σ 0 ≤ Σ nd
    have : ∑ _v ∈ F.ground, (0 : ℤ)
            ≤ ∑ v ∈ F.ground, (F.toSetFamily).normalizedDegreeAt v := by
      exact Finset.sum_le_sum hmono
    -- replace LHS by 0
    exact le_trans (by exact Int.le_of_eq (id (Eq.symm hleft))) this
  -- rewrite with the identity
  simp_all only

/-- Corollary (Strict positivity of NDS from strictly positive normalized degrees).
    If all normalized degrees are ≥ 1, then `nds(F) ≥ |U|`. -/
theorem nds_ge_card_if_all_vertices_ge_one :
  (∀ v ∈ F.ground, (1 : ℤ) ≤ (F.toSetFamily).normalizedDegreeAt v) →
  (F.ground.card : ℤ) ≤ (F.toSetFamily).nds := by
  intro hAll
  have Hsum := SetFamily.sum_normalizedDegree_over_ground_eq_nds (SF := (F.toSetFamily))
  -- Σ 1 ≤ Σ nd(v) = nds ⇒ |U| ≤ nds
  -- Evaluate Σ 1 as `card • 1 = card`.
  have hsum1 :
      ∑ _v ∈ F.ground, (1 : ℤ) = F.ground.card • (1 : ℤ) := by
    exact Finset.sum_const (b := (1 : ℤ)) (s := F.ground)
  have hone : F.ground.card • (1 : ℤ) = (F.ground.card : ℤ) := by
    exact nsmul_one _
  have hmono :
      ∑ _v ∈ F.ground, (1 : ℤ) ≤ ∑ v ∈ F.ground, (F.toSetFamily).normalizedDegreeAt v := by
    exact Finset.sum_le_sum (fun v hv => hAll v hv)
  calc
    (F.ground.card : ℤ)
        = F.ground.card • (1 : ℤ) := by simp_all only [sum_const, Int.nsmul_eq_mul, mul_one]
    _   = ∑ _v ∈ F.ground, (1 : ℤ) := by simp_all only [sum_const, Int.nsmul_eq_mul, mul_one]
    _   ≤ ∑ v ∈ F.ground, (F.toSetFamily).normalizedDegreeAt v := by exact hmono
    _   = (F.toSetFamily).nds := by simp_all only [sum_const, Int.nsmul_eq_mul, mul_one]

end
end Ideal
