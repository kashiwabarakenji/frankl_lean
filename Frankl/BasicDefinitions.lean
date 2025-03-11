import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic
--import LeanCopilot

namespace Frankl

variable {α : Type} [DecidableEq α] [Fintype α]

structure SetFamily (α : Type) where
  (ground : Finset α)
  (sets : Finset α → Prop)
  (inc_ground : ∀ s, sets s → s ⊆ ground)
  (nonempty_ground : ground.Nonempty)

noncomputable def SetFamily.degree (F : SetFamily α)[DecidablePred F.sets]: α → Int := λ v => Int.ofNat (Finset.filter (λ s => F.sets s ∧ v ∈ s) F.ground.powerset).card  -- degreeを計算する関数を持つとする

noncomputable def SetFamily.number_of_hyperedges  (F : SetFamily α) [DecidablePred F.sets]: Int :=
  Int.ofNat ((Finset.powerset F.ground).filter F.sets).card

noncomputable def SetFamily.total_size_of_hyperedges (F : SetFamily α)  [DecidablePred F.sets] : Int :=
   Int.ofNat (((Finset.powerset F.ground).filter F.sets).sum Finset.card)

noncomputable def SetFamily.normalized_degree {α : Type} [DecidableEq α]  (F : SetFamily α) [DecidablePred F.sets] (x: α): ℤ :=
  2 * (F.degree x:Int) - (F.number_of_hyperedges:Int)

noncomputable def SetFamily.normalized_degree_sum {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) [DecidablePred F.sets]: ℤ :=
  2 * (F.total_size_of_hyperedges:Int) - (F.number_of_hyperedges:Int)*(F.ground.card:Int)

structure IdealFamily  (α : Type) [DecidableEq α] [Fintype α] extends SetFamily α where
  (has_empty : sets ∅)
  (has_ground : sets ground)
  (down_closed : ∀ (A B : Finset α), sets B → B ≠ ground → A ⊆ B → sets A)

noncomputable def IdealFamily.degree (F : IdealFamily α)[DecidablePred F.sets]: α → Int := λ v => Int.ofNat (Finset.filter (λ s => F.sets s ∧ v ∈ s) F.ground.powerset).card  -- degreeを計算する関数を持つとする

-- A predicate to check if a SetFamily is an IdealFamily.
def isIdealFamily (F: SetFamily α) : Prop :=
  (F.sets ∅) ∧                -- The empty set is included
  (F.sets F.ground) ∧         -- The ground set is included
  (∀ A B : Finset α, F.sets B → B ≠ F.ground → A ⊆ B → F.sets A)  -- Downward closure

-- A predicate to check if an IdealFamily is intersection-closed.
def isIntersectionClosedFamily  (F : SetFamily α) : Prop :=
  ∀ {s t : Finset α}, F.sets s → F.sets t → F.sets (s ∩ t)

def is_rare (F : SetFamily α) (v : α)  [DecidablePred F.sets]  : Prop :=
  2 * F.degree v - F.number_of_hyperedges <= 0

end Frankl
