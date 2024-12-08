import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Init.Data.Nat.Lemmas
--import Mathlib.Data.Bool.Basic
--import Mathlib.Tactic
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
