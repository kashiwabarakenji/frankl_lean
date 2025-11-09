/-
  IdealFamily/NDSDiff.lean

  Exact one–step difference formula for Frankl’s NDS under the trace at a vertex v.

  Policy.
    • One import per line.
    • No `induction'`, no `simpa using`.
    • Comments in English (paper-facing).

  Notation in this file (fixed `F : Ideal α`, vertex `v : α`).
    (F.toSetFamily) := F.toSetFamily
    n  := F.ground.card          -- |U|
-/

import IdealFamily.Core
import IdealFamily.TraceGuarded
import IdealFamily.Contraction
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
--import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Int.Basic

namespace IdealFamily
namespace Ideal

open Finset
open scoped BigOperators

noncomputable section

variable {α : Type*} [DecidableEq α]
variable (F : Ideal α) [DecidablePred F.sets]
variable (v : α)

-- Keep only this one abbreviation; expand A/B/C explicitly below.
--local notation "(F.toSetFamily)" => F.toSetFamily
local notation "n"  => F.ground.card

/-! *************************  Set decompositions around v  ************************* -/

/-- `carrier = (delCarrier v) ⊎ (S v)`. -/
lemma carrier_eq_del_union_S :
  (F.toSetFamily).carrier = ((F.toSetFamily).delCarrier v) ∪ ((F.toSetFamily).S v) := by
  classical
  apply Finset.ext
  intro t
  constructor
  · intro ht
    by_cases hv : v ∈ t
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨ht, hv⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨ht, hv⟩))
  · intro ht
    cases Finset.mem_union.mp ht with
    | inl hA => exact (Finset.mem_filter.mp hA).1
    | inr hB => exact (Finset.mem_filter.mp hB).1

/-- `(delCarrier v)` and `(S v)` are disjoint. -/
lemma disjoint_del_S : Disjoint ((F.toSetFamily).delCarrier v) ((F.toSetFamily).S v) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro t htA htB
  have hv_not : v ∉ t := (Finset.mem_filter.mp htA).2
  have hv_yes : v ∈ t := (Finset.mem_filter.mp htB).2
  exact (hv_not hv_yes).elim

/-- Standard disjoint splitting on `contrCarrier v`:
    `((contrCarrier v) \ (delCarrier v)) ⊎ ((contrCarrier v) ∩ (delCarrier v)) = (contrCarrier v)`. -/
lemma sdiff_union_inter_eq_self_on_contr :
  (F.toSetFamily).contrCarrier v \ (F.toSetFamily).delCarrier v ∪ (F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v
    = (F.toSetFamily).contrCarrier v := by
  classical
  apply Finset.ext
  intro t
  constructor
  · intro ht
    rcases Finset.mem_union.mp ht with hsdiff | hinter
    · exact (Finset.mem_sdiff.mp hsdiff).1
    · exact (Finset.mem_inter.mp hinter).1
  · intro htC
    by_cases htA : t ∈ (F.toSetFamily).delCarrier v
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨htC, htA⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨htC, htA⟩))

/-- Disjointness of `((contrCarrier v) \ (delCarrier v))` and `((contrCarrier v) ∩ (delCarrier v))`. -/
lemma disjoint_sdiff_inter_on_contr :
  Disjoint ((F.toSetFamily).contrCarrier v \ (F.toSetFamily).delCarrier v)
           ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro t h1 h2
  have hnot : t ∉ (F.toSetFamily).delCarrier v := (Finset.mem_sdiff.mp h1).2
  have hinA : t ∈ (F.toSetFamily).delCarrier v := (Finset.mem_inter.mp h2).2
  exact (hnot hinA).elim

/-! *******************************  Arithmetic helpers  ***************************** -/

/-- If `v∈U` then `|(U\\{v})| = n - 1` (ℤ-cast). -/
lemma card_ground_erase_z (hvU : v ∈ F.ground) :
  ((F.ground.erase v).card : ℤ) = (n : ℤ) - 1 := by
  classical
  -- Nat-level equality
  have hN : (F.ground.erase v).card = n - 1 := Finset.card_erase_of_mem hvU
  -- Cast both sides to ℤ
  have hZ : ((F.ground.erase v).card : ℤ) = ((n - 1 : ℕ) : ℤ) :=
    congrArg (fun k : ℕ => (k : ℤ)) hN
  -- Rewrite the RHS as `(n:ℤ) - 1` using `Nat.cast_sub` with `1 ≤ n`.
  have hnpos : 1 ≤ n := by
    -- ground is nonempty because hvU gives a witness
    have : 0 < F.ground.card := by
      exact Finset.card_pos.mpr ⟨v, hvU⟩
    exact Nat.succ_le_of_lt this
  have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - (1 : ℤ) :=
    (Nat.cast_sub hnpos)
  exact Eq.trans hZ hcast



end
end Ideal
end IdealFamily
