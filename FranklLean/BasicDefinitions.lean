import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic
import LeanCopilot

namespace Frankl

variable {α : Type} [DecidableEq α] [Fintype α]

-- 共通インターフェースとなる型クラス
class Family (F : Type u) (α : Type) where
  degree : F → α → Int
  number_of_hyperedges : F → Int
  export Family (degree number_of_hyperedges)

-- 集合族の定義
structure SetFamily (α : Type)[DecidableEq α] [Fintype α]:=
  (ground : Finset α)
  (sets : Finset α → Prop)
  (inc_ground : ∀ s, sets s → s ⊆ ground)
  (nonempty_ground : ground.Nonempty)
  --(degree: α → Int)
  --(number_of_hyperedges : Int)

noncomputable def SetFamily.degree (F : SetFamily α): α → Int := λ v => Int.ofNat (Finset.filter (λ s => F.sets s = true ∧ v ∈ s) F.ground.powerset).card  -- degreeを計算する関数を持つとする

noncomputable def SetFamily.number_of_hyperedges (F : SetFamily α) : Int :=
  Int.ofNat (Finset.card (Finset.filter (λ s => F.sets s = true ) (F.ground.powerset)))

/-
noncomputable instance (α : Type) [DecidableEq α] [Fintype α] : Family (SetFamily α) α where
  degree F v := Int.ofNat  (Finset.card (Finset.filter (λ s => F.sets s = true ∧ v ∈ s) (F.ground.powerset)))
  number_of_hyperedges F := Int.ofNat (Finset.card (Finset.filter (λ s => F.sets s = true) (F.ground.powerset)))
-/

-- Ideal集合族の定義
structure IdealFamily  (α : Type) [DecidableEq α] [Fintype α] extends SetFamily α :=
  (has_empty : sets ∅)  -- 空集合が含まれる
  (has_ground : sets ground)  -- 全体集合が含まれる
  (down_closed : ∀ (A B : Finset α), sets B → B ≠ ground → A ⊆ B → sets A)

noncomputable def IdealFamily.degree (F : IdealFamily α): α → Int := λ v => Int.ofNat (Finset.filter (λ s => F.sets s = true ∧ v ∈ s) F.ground.powerset).card  -- degreeを計算する関数を持つとする

noncomputable def IdealFamily.number_of_hyperedges (F : IdealFamily α) : Int :=
  Int.ofNat (Finset.card (Finset.filter (λ s => F.sets s = true ) (F.ground.powerset)))

/-
-- IdealFamilyでもFamilyインスタンスを定義
noncomputable instance (α : Type) [DecidableEq α] [Fintype α] : Family (IdealFamily α) α where
  degree := (Family.degree : SetFamily α → α → Int) ∘ IdealFamily.toSetFamily
  number_of_hyperedges := (Family.number_of_hyperedges (α := α) : SetFamily α → Int) ∘ IdealFamily.toSetFamily

--noncomputable instance (α : Type) [DecidableEq α] [Fintype α] : Family (IdealFamily α) α where
--  degree F v := Finset.card (Finset.filter (λ s => F.sets s = true ∧ v ∈ s) (F.ground.powerset))
--  number_of_hyperedges F := Finset.card (Finset.filter (λ s => F.sets s = true ) (F.ground.powerset))
-/

end Frankl
