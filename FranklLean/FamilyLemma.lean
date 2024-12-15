import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset
import Init.Data.Int.Lemmas
import Init.Data.Nat.Lemmas
import FranklLean.FranklMinors
import FranklLean.BasicDefinitions
import FranklLean.BasicLemmas
import LeanCopilot

namespace Frankl

variable {α : Type} [DecidableEq α][Fintype α]

lemma setfamily_hyperedges_geq2 (F : IdealFamily α) [DecidablePred F.sets] :
  F.number_of_hyperedges >= 2 :=
by
  dsimp [IdealFamily.number_of_hyperedges]
  have h_mem: {∅,F.ground} ⊆ Finset.filter (λ s => F.sets s) F.ground.powerset := by
    simp [Finset.subset_iff]
    apply And.intro
    · exact F.has_empty
    · exact F.has_ground
  have h_card: Finset.card {∅,F.ground} ≤ Finset.card (Finset.filter (λ s => F.sets s) F.ground.powerset) := by
    apply Finset.card_le_card h_mem
  have h_card': Finset.card {∅,F.ground} = 2 := by
    have : ∅ ≠ F.ground:= by
      intro h
      have h' := F.nonempty_ground
      simp_all only [Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.singleton_subset_iff, Finset.mem_filter,
        Finset.mem_powerset, subset_refl, true_and, Finset.card_singleton, Finset.one_le_card]
      rw [← h] at h'
      simp_all only
      simp [← h] at h'
    simp_all only [Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton,
      Nat.reduceAdd, ne_eq]
  simp_all only [ge_iff_le, Nat.ofNat_le_cast]

lemma setfamily_hyperedges_total (F : IdealFamily α) [DecidablePred F.sets] :
  F.total_size_of_hyperedges >= 1 :=
by
  dsimp [IdealFamily.total_size_of_hyperedges]
  have h_mem: {F.ground} ⊆ Finset.filter (λ s => F.sets s) F.ground.powerset := by
    simp [Finset.subset_iff]
    exact F.has_ground
  have h_sum: Finset.sum {F.ground} Finset.card  ≤ Finset.sum (Finset.filter F.sets F.ground.powerset) Finset.card:= by
    rw [Finset.sum_singleton]
    exact @Finset.sum_le_sum_of_subset _ _ _ Finset.card _ _ h_mem

  have h_total : Finset.sum ({F.ground}) Finset.card = F.ground.card := by
    simp_all only [Finset.sum_singleton, Finset.card_singleton]
  have h_ground: F.ground.card >= 1 := by
    exact Finset.card_pos.mpr F.nonempty_ground
  rw [h_total] at h_sum
  have h_sum' : (Finset.filter F.sets F.ground.powerset).sum Finset.card >= F.ground.card :=
    by
      exact h_sum
  convert ge_trans h_sum' h_ground
  simp_all only [ge_iff_le, Nat.cast_sum]
  apply Iff.intro
  · intro _
    linarith
  · intro _
    linarith

end Frankl
