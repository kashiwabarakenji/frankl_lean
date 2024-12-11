import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset
import LeanCopilot

variable {α : Type} [DecidableEq α]

theorem erase_inj_of_mem {s t : Finset α} {x : α} (hx : x ∈ s) (ht : x ∈ t) :
  Finset.erase s x = Finset.erase t x ↔ s = t :=
by
  constructor
  -- まず、Finset.erase s x = Finset.erase t x から s = t を導きます。
  · intro h
    apply Finset.ext
    intro a
    by_cases ha : a = x
    -- a が x に等しい場合
    · rw [ha]
      simp_all

    -- a が x に等しくない場合
    simp only [ha, eq_self_iff_true] at h
    · constructor
      intro h1 -- a ∈ s
      have hh: a ∈ s.erase x := Finset.mem_erase_of_ne_of_mem ha h1
      rw [h] at hh
      exact Finset.mem_of_mem_erase hh
      intro h2 -- a ∈ t
      have hh: a ∈ t.erase x := Finset.mem_erase_of_ne_of_mem ha h2
      rw [←h] at hh
      exact Finset.mem_of_mem_erase hh

  -- 次に、s = t から Finset.erase s x = Finset.erase t x を導きます。
  · intro h
    rw [h]

lemma ground_nonempty_after_minor {α : Type} [DecidableEq α] (ground : Finset α) (x : α) (hx: x ∈ ground) (ground_ge_two: ground.card ≥ 2) : (ground.erase x).Nonempty :=
  by
    rw [Finset.erase_eq]
    apply Finset.nonempty_of_ne_empty
    by_contra h_empty
    by_cases hA : ground = ∅
    rw [hA] at ground_ge_two
    contradiction
    -- ground.card = 1のケース
    have g_eq_x: ground = {x} := by
      ext y
      constructor
      intro _
      have hy' : y ∈ ground \ {x} := by
          rw [h_empty]
          simp_all only [Finset.sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, false_or,Finset.card_singleton]--
          simp_all only [ge_iff_le, Nat.reduceLeDiff]
      rw [h_empty] at hy'
      contradiction
      -- y ∈ {x}のときに、groundに属することを示す
      intro hy
      have x_eq_y : x = y := by
        rw [Finset.mem_singleton] at hy
        rw [hy]
      rw [x_eq_y] at hx
      exact hx
    rw [g_eq_x] at ground_ge_two
    rw [Finset.card_singleton] at ground_ge_two
    contradiction

omit [DecidableEq α] in
lemma decarte (A : Finset α) (B : Finset (Finset α)) (a : α) (b : Finset α)
  (ha : a ∈ A) (hb : b ∈ B) : (a, b) ∈ A.product B := by
  -- Based on the definition of `Finset.product`, if `a ∈ A` and `b ∈ B`, then `(a, b) ∈ A.product B`.
  apply Finset.mem_product.2 ⟨ha, hb⟩

omit [DecidableEq α] in
lemma decarter {α:Type}{a:α}{b:Finset α} (A : Finset α) (B : Finset (Finset α)) (h:(a, b) ∈ A.product B)
  : a ∈ A ∧ b ∈ B := by
  -- By the definition of `Finset.product`, if `(a, b)` belongs to `A.product B`,
  -- then `a ∈ A` and `b ∈ B`.
  exact Finset.mem_product.1 h

lemma sum_nonneg_of_nonneg {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℤ) (h : ∀ x ∈ s, 0 ≤ f x) :
  0 ≤ s.sum f := by
  apply Finset.sum_induction
  · intro a b ha hb
    omega
  · simp_all only [le_refl]
  intro x a
  simp_all only

lemma sum_posi_of_posi {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℤ) (nonempty: s ≠ ∅) (h : ∀ x ∈ s, 0 < f x) :
  0 < s.sum f := by
  obtain ⟨a, ha⟩ := Finset.nonempty_of_ne_empty nonempty
  -- Since s is nonempty, we have `a ∈ s`.
  have h_pos : 0 < f a := h a ha
  rw [Finset.sum_eq_add_sum_diff_singleton ha]
  apply add_pos_of_pos_of_nonneg
  · exact h_pos
  · apply sum_nonneg_of_nonneg
    intros x hx
    simp_all only [ne_eq, Finset.mem_sdiff, Finset.mem_singleton]
    obtain ⟨left, _⟩ := hx
    exact (h x left).le

lemma sum_nonpos_exists_nonpos {α : Type} [DecidableEq α] (s : Finset α)(nonempty: s ≠ ∅) (f : α → ℤ) (h : s.sum f ≤ 0) :
  ∃ x ∈ s, f x ≤ 0 := by
  by_contra h1
  -- By contradiction, assume that for all x in s, f x > 0.
  push_neg at h1

  have h_pos : 0 < s.sum f := by
    let sn := sum_posi_of_posi s (λ x => f x) nonempty (by simp_all [h1])
    apply lt_of_le_of_ne
    apply le_trans
    on_goal 2 => exact sn
    simp_all only [zero_add, Int.reduceLE]
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only [le_refl]
    simp [a] at sn
  simp_all only [ne_eq]
  exact not_le_of_lt h_pos h
