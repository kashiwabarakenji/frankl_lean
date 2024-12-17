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

lemma number_ground (F:SetFamily α)[DecidablePred F.sets] (v : α): Finset.filter (fun s =>F.sets s ∧ v ∉ s) F.ground.powerset = Finset.filter (fun s =>F.sets s ∧ v ∉ s) (F.ground \ {v}).powerset := by
      ext1 s
      apply Iff.intro
      · intro a
        rw [Finset.mem_filter] at a
        rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_powerset] at a
          rw [Finset.mem_powerset]
          rw [Finset.subset_sdiff]
          constructor
          · exact a.1
          · dsimp [Disjoint]
            intro b
            intro b_in_v
            let _ := a.2.2 --need to use this to get the contradiction
            intro v_in_s
            let tmp := Finset.subset_singleton_iff.mp v_in_s
            cases tmp
            case inl h => rw [h]
            case inr h =>
              rw [h] at b_in_v
              have b_in_v2: v ∈ s := by
                exact Finset.singleton_subset_iff.mp b_in_v
              contradiction
        · constructor
          · exact a.2.1
          · exact a.2.2

      · intro a
        rw [Finset.mem_filter] at a
        rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_powerset] at a
          rw [Finset.mem_powerset]
          rw [Finset.subset_sdiff] at a
          exact a.1.1
        · exact a.2

lemma family_union (F:SetFamily α)[DecidablePred F.sets] (v : α): Finset.filter (fun s => F.sets s) F.ground.powerset = Finset.filter (fun s =>F.sets s ∧ v ∈ s) (F.ground).powerset ∪ Finset.filter (fun s =>F.sets s ∧ v ∉ s) (F.ground).powerset:=
by
  ext1 a
  simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union]
  apply Iff.intro
  · intro a_1
    simp_all only [true_and]
    --obtain ⟨_, _⟩ := a_1
    tauto
  · intro a_1
    cases a_1 with
    | inl h => simp_all only [and_self]
    | inr h_1 => simp_all only [and_self]

lemma family_union_card (F:SetFamily α)[DecidablePred F.sets] (v : α): (Finset.filter (fun s => F.sets s) F.ground.powerset).card = (Finset.filter (fun s =>F.sets s ∧ v ∈ s) (F.ground).powerset).card + (Finset.filter (fun s =>F.sets s ∧ v ∉ s) (F.ground).powerset).card :=
by
  have contradict: ∀ s: Finset α, s ∈ F.ground.powerset → ¬ ((F.sets s ∧ v ∈ s) ∧ (F.sets s ∧ v ∉ s)) :=
  by
    intro s _
    simp_all only [Finset.mem_powerset, not_and, not_true_eq_false, and_false, not_false_eq_true, and_imp,
      implies_true]

  let result := filter_num F.ground.powerset contradict
  have : ∀ s : Finset α, s ∈ F.ground.powerset → (F.sets s ∧ v ∈ s ∨ F.sets s ∧ v ∉ s ↔ F.sets s) := by
    intro s _
    apply Iff.intro
    · intro a
      cases a with
      | inl h => exact h.1
      | inr h => exact h.1
    · intro a
      simp_all only [true_and]
      tauto
  simp_rw [Finset.filter_congr this] at result
  exact result




end Frankl
