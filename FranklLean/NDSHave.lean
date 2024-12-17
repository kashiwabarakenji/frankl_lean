import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset
import Init.Data.Int.Lemmas
import Init.Data.Nat.Lemmas
import FranklLean.FranklMinors
import FranklLean.BasicDefinitions
import FranklLean.BasicLemmas
import FranklLean.FamilyLemma
import FranklLean.DegreeOneHave
import LeanCopilot

namespace Frankl

variable {α : Type} [DecidableEq α][Fintype α]

lemma number_nds_have (F: IdealFamily α) [DecidablePred F.sets] (v:α) (geq2: F.ground.card ≥ 2) (vin: v ∈ F.ground)(hs: F.sets {v})
  [DecidablePred (F.toSetFamily.deletion v vin geq2).sets] [DecidablePred (F.contraction v hs geq2).sets]:
F.number_of_hyperedges = (F.toSetFamily.deletion v vin geq2).number_of_hyperedges + (F.contraction v hs geq2).number_of_hyperedges :=
by
  dsimp [IdealFamily.number_of_hyperedges]
  rw [family_union_card F.toSetFamily v]
  rw [add_comm]
  have left_hand:  (Finset.filter (fun s => F.sets s ∧ v ∉ s) F.ground.powerset).card = (Finset.filter (fun s => (F.toSetFamily.deletion v vin geq2).sets s) (F.deletion v vin geq2).ground.powerset).card := by
    rw [ground_deletion F v vin geq2]
    dsimp [SetFamily.deletion]
    rw [number_ground F.toSetFamily v]
    congr

  have right_hand: (Finset.filter (fun s => F.sets s ∧ v ∈ s) F.ground.powerset).card = (Finset.filter (fun s => (F.contraction v hs geq2).sets s) (F.contraction v hs geq2).ground.powerset).card := by
    #check ground_contraction F v vin geq2
    dsimp [IdealFamily.contraction]



    let def_tmp := (F.deletion v vin geq2).number_of_hyperedges
    unfold IdealFamily.number_of_hyperedges at def_tmp
