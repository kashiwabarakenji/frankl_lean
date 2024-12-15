import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Init.Data.Int.Lemmas
import Init.Data.Nat.Lemmas
import FranklLean.FranklMinors
import FranklLean.BasicDefinitions
import FranklLean.BasicLemmas
import FranklLean.DegreeOneHave
import FranklLean.DegreeOneNone
import LeanCopilot

namespace Frankl

variable {α : Type} [DecidableEq α] [Fintype α]

-- For the base case when the ground set size is one
lemma nonpositive_nds_one (F : IdealFamily α)[DecidablePred F.sets] (h : F.ground.card = 1) : F.normalized_degree_sum ≤ 0 :=
by
  obtain ⟨v, hv⟩ := F.nonempty_ground
  have h' : F.ground = ({v} : Finset α) :=
  by
    have h_singleton := Finset.card_eq_one.mp h
    obtain ⟨v', hv'⟩ := h_singleton
    rw [hv'] at hv
    simp_all only [Finset.card_singleton, Finset.mem_singleton]
  let tmp_arg := F.has_ground
  rw [h'] at tmp_arg
  have hasGround:F.sets {v}:= tmp_arg
  have hasEmpty:F.sets ∅ := F.has_empty
  have h'' : F.ground.powerset = ({∅, {v}}:Finset (Finset α)) :=
  by
    simp_all only [Finset.card_singleton, Finset.mem_singleton]
    rfl
  have total: F.total_size_of_hyperedges = 1:= by
    dsimp [IdealFamily.total_size_of_hyperedges]
    rw [h'']
    simp
    rw [Finset.filter_true_of_mem]
    congr
    intro x a
    simp_all only [Finset.card_singleton, Finset.mem_singleton, Finset.mem_insert]
    cases a with
    | inl h =>
      subst h
      simp_all only
    | inr h_1 =>
      subst h_1
      simp_all only
  have h''' : F.number_of_hyperedges = 2:= by
    dsimp [IdealFamily.number_of_hyperedges]
    rw [h'']
    rw [Finset.filter_true_of_mem]
    congr
    intro x a
    simp_all only [Finset.card_singleton, Finset.mem_singleton, Finset.mem_insert]
    cases a with
    | inl h =>
      subst h
      simp_all only
    | inr h_1 =>
      subst h_1
      simp_all only
  have h'''' : F.normalized_degree_sum = 0:= by
    dsimp [IdealFamily.normalized_degree_sum]
    rw [total]
    rw [h''']
    simp
    simp_all only [Finset.card_singleton, Finset.mem_singleton, Nat.cast_one, mul_one, sub_self]
  simp_all only [Finset.card_singleton, Finset.mem_singleton, le_refl]

/-
-- Lemma for the degree-one case
lemma degree_one_haveUV (F : IdealFamily α) [DecidablePred F.sets] (v : α) (geq2: F.ground.card ≥ 2)(h_uv_have : (F.sets (F.ground \ {v})))
  (ih : ∀ (F' : IdealFamily α)[DecidablePred F'.sets], F'.ground.card < F.ground.card → F'.normalized_degree_sum ≤ 0)
  : F.normalized_degree_sum ≤ 0 :=
by
  sorry
-/



-- Lemma stating that contraction of F at v forms an ideal family
--lemma isIdealFamily_cont (F : IdealFamily α)[DecidablePred F.sets](v : α)(geq2: F.ground.card ≥ 2)(hassingleton: F.sets {v}) : isIdealFamily (F.contraction v hassingleton geq2):= sorry

-- Lemma stating that deletion of v from F forms an ideal family
--lemma isIdealFamily_del (F : IdealFamily α)[DecidablePred F.sets](v : α) (geq2: F.ground.card ≥ 2): isIdealFamily (F.deleletion v geq2):= sorry

-- Case: U\{v} is a hyperedge scenario
-- Uses induction hypothesis, and conditions on the contracted and deleted families
lemma nonpositive_nds_haveUV
  (F : IdealFamily α)[DecidablePred F.sets] (v : α) (geq2: F.ground.card ≥ 2)(hassingleton: F.sets {v}) (h_uv_have : (F.sets (F.ground \ {v})))
  (ih : ∀ (F' : IdealFamily α)[DecidablePred F'.sets], F'.ground.card = F.ground.card - 1→ F'.normalized_degree_sum ≤ 0)
  : F.normalized_degree_sum ≤ 0 := sorry

-- Case: U\{v} is not a hyperedge scenario
lemma nonpositive_nds_nothaveUV
  (F : IdealFamily α) [DecidablePred F.sets](v : α)(geq2: F.ground.card ≥ 2)(hassingleton: F.sets {v}) (h_uv_not : ¬(F.sets (F.ground \ {v})))
  (ih : ∀ (F' : IdealFamily α)[DecidablePred F'.sets], F'.ground.card = F.ground.card - 1 → F'.normalized_degree_sum  ≤ 0)
  : F.normalized_degree_sum  ≤ 0 :=  sorry

-- Main theorem skeleton
theorem ideal_average_rarity {n : Nat}(F : IdealFamily α)[DecidablePred F.sets] (hn : F.ground.card = n) :
  F.normalized_degree_sum ≤ 0 := by
  -- Induction on the size of the ground set
  cases h:F.ground.card with
  | zero =>
    -- This case should not occur since the family is over a nonempty ground set.
    -- If needed, handle or assert nonempty_ground ensures card ≥ 1.
    -- For completeness, we can put a sorry or a contradiction here.
    exfalso
    have hh := F.nonempty_ground
    have h_empty : F.ground = ∅ := by
      simp_all only [Finset.card_eq_zero, Finset.not_nonempty_empty]
      subst h
      simpa using hn.symm
    simp_all only [Finset.card_empty, Finset.not_nonempty_empty]
/-
  | succ Nat.zero =>
  --succ _root_.Nat.zero =>
    -- Base case: size of the ground set is one

    have h1: F.ground.card = 1 := by
      simp_all only [Nat.succ_eq_add_one, add_left_eq_self, zero_add]


    exact nonpositive_nds_one F h1
-/

  | succ n =>
    -- Inductive step
    if n = 0 then
      -- Base case: size of the ground set is one
      have h1: F.ground.card = 1 := by
        simp_all only [Nat.succ_eq_add_one, add_left_eq_self, zero_add]
      exact nonpositive_nds_one F h1
    else
      -- Inductive step: size of the ground set is greater than one
    have : ∃ v : α, v ∈ F.ground := by
      have h_nonempty := F.nonempty_ground
      exact h_nonempty
    obtain ⟨v, hv⟩ := this

    have geq2: F.ground.card ≥ 2 := by
      rw [h]
      omega
    have groundn: n = F.ground.card - 1 := by
      rw [h]
      omega
    -- Consider whether {v} is a hyperedge
    have ih:  (∀ (F':IdealFamily α) [DecidablePred F'.sets] , F'.ground.card = n → F'.normalized_degree_sum ≤ 0) :=
    by
      intro hh
      exact ideal_average_rarity hh
    rw [groundn] at ih
    by_cases h_v : F.sets {v}
    case pos =>
      -- Now consider whether (F.ground \ {v}) is a hyperedge
      by_cases h_uv : F.sets (F.ground \ {v})
      case pos =>
        -- If (U\{v}) is a hyperedge
        exact nonpositive_nds_haveUV F v geq2 h_v h_uv ih
      case neg =>
        -- If (U\{v}) is not a hyperedge
        exact nonpositive_nds_nothaveUV F v geq2 h_v h_uv ih
      -- If {v} is a hyperedge, we have the degree-one case
    case neg =>
      by_cases h_uv : F.sets (F.ground \ {v})
      case pos =>
        -- If (U\{v}) is a hyperedge
        exact degree_one_haveUV F v hv geq2 h_v h_uv
      case neg =>
        exact degree_one_nothaveUV F v hv geq2 h_v h_uv ih

end Frankl
