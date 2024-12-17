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

def NDS (n:Nat) : Prop := n ≥ 2  ∧ ∀ (F: IdealFamily α)[DecidablePred F.sets], F.ground.card = n → F.normalized_degree_sum ≤ 0

lemma total_eq_lem_left (n : Nat) {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α)(h : DecidablePred (λ s=> F.sets s)) (v : α)
  (v_in_ground : v ∈ F.ground)
  --(ground_minus_v_none : ¬ (F.sets (F.ground \ {v})))
  (ground_ge_two : F.ground.card ≥ 2)
  (ground_card: F.ground.card = n + 1):
  ∑ x ∈ Finset.filter (fun s => (F.sets s ∧ v ∉ s) ∨ s = F.ground) (F.ground).powerset, x.card =
  ∑ x ∈ Finset.filter (fun s => F.sets s ∧ v ∉ s) (F.ground).powerset, x.card + n + 1:=
  by
    --have hv_equal: F.ground.erase v = F.ground \ {v} := by
    --  exact Finset.erase_eq F.ground v
    --let P (s : Finset α) := (F.sets s ∧ v ∉ s)
    --let Q (s: Finset α) := s = F.ground \ {v}
    let leftset := Finset.filter (fun s => F.sets s ∧ v ∉ s) (F.ground).powerset
    let rightset := Finset.filter (fun s => s = F.ground) (F.ground).powerset
    have disjoint: leftset ∩ rightset = ∅ := by
      dsimp [leftset, rightset]
      rw [Finset.eq_empty_iff_forall_not_mem]
      by_contra h_contra
      rw [not_forall] at h_contra
      push_neg at h_contra
      obtain ⟨s, hs⟩ := h_contra
      rw [Finset.mem_inter] at hs
      rw [Finset.mem_filter] at hs
      rw [Finset.mem_filter] at hs
      rw [Finset.mem_powerset] at hs
      simp_all only [ge_iff_le, Nat.reduceLeDiff]
      obtain ⟨left, right⟩ := hs
      obtain ⟨left, right_1⟩ := left
      obtain ⟨left_1, right⟩ := right
      obtain ⟨left_2, right_1⟩ := right_1
      subst right
      simp_all only

    have disjoint2: ∀ s ∈ F.ground.powerset, ¬((F.sets s ∧ v ∉ s) ∧ s = F.ground) := by
      intro s a
      simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset, not_and, and_imp, leftset, rightset]
      intro a_1 a_2
      apply Aesop.BuiltinRules.not_intro
      intro a_3
      subst a_3
      simp_all only

    have sum_lem:
      ∑ x ∈ Finset.filter (fun s => (F.sets s ∧ v ∉ s) ∨ s = F.ground) (F.ground).powerset, x.card =
      ∑ x ∈ leftset, x.card + ∑ x ∈ rightset, x.card := by
        exact filter_sum_func (F.ground).powerset (λ s => s.card) disjoint2

    have ground_card: ∑ x ∈ Finset.filter (fun s => s = F.ground) F.ground.powerset, x.card = n + 1:= by
      simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset, not_and, and_imp, leftset, rightset]
      rw [Finset.filter_eq']
      simp_all only [Finset.mem_powerset, subset_refl, ↓reduceIte, Finset.sum_singleton]

    dsimp [leftset, rightset] at sum_lem
    simp_all only [Finset.mem_filter, Finset.mem_powerset]
    rw [←ground_card] at sum_lem
    simp_all only [ge_iff_le, Nat.reduceLeDiff, not_and, and_imp, leftset, rightset]
    rfl

  lemma total_eq_lem_right (n : Nat) {α : Type} [DecidableEq α] [Fintype α]
    (F : IdealFamily α)(h : DecidablePred (λ s=> F.sets s)) (v : α)
    (v_in_ground : v ∈ F.ground)
    (ground_minus_v_none : ¬ (F.sets (F.ground \ {v})))
    (ground_ge_two : F.ground.card ≥ 2)
    (ground_card: F.ground.card = n + 1):
    ∑ x ∈ Finset.filter (fun s => (F.sets s ∧ v ∉ s) ∨ s = F.ground.erase v) (F.ground.erase v).powerset, x.card =
    ∑ x ∈ Finset.filter (fun s => F.sets s ∧ v ∉ s) (F.ground.erase v).powerset, x.card + n:=
    by
      --have hv_equal: F.ground.erase v = F.ground \ {v} := by
      --  exact Finset.erase_eq F.ground v
      --let P (s : Finset α) := (F.sets s ∧ v ∉ s)
      --let Q (s: Finset α) := s = F.ground \ {v}
      let leftset := Finset.filter (fun s => F.sets s ∧ v ∉ s) (F.ground.erase v).powerset
      let rightset := Finset.filter (fun s => s = F.ground.erase v) (F.ground.erase v).powerset
      have disjoint: leftset ∩ rightset = ∅ := by
        simp_all only [ge_iff_le, Nat.reduceLeDiff, leftset, rightset]
        ext1 a
        simp_all only [Finset.mem_inter, Finset.mem_filter, Finset.mem_powerset, Finset.not_mem_empty, iff_false,
          not_and, true_and, and_imp]
        intro a_1 a_2 a_3
        apply Aesop.BuiltinRules.not_intro
        intro a_4
        subst a_4
        simp_all only [not_true_eq_false,Finset.erase_eq]

      have disjoint2: ∀ s ∈ (F.ground.erase v).powerset, ¬((F.sets s ∧ v ∉ s) ∧ s = F.ground.erase v) := by
        intro s a
        simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset, not_and, and_imp, leftset, rightset]
        intro a_1 a_2
        apply Aesop.BuiltinRules.not_intro
        intro a_3
        subst a_3
        simp_all only [not_true_eq_false,Finset.erase_eq]

      have sum_lem:
       ∑ x ∈ Finset.filter (fun s => (F.sets s ∧ v ∉ s) ∨ s = (F.ground.erase v)) (F.ground.erase v).powerset, x.card = (∑ x ∈ leftset, x.card) + (∑ x ∈ rightset, x.card):= by
          exact filter_sum_func (F.ground.erase v).powerset (λ s => s.card) disjoint2

      have ground_card: ∑ x ∈ Finset.filter (fun s => s = (F.ground.erase v)) (F.ground.erase v).powerset, x.card = n :=
      by
        simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset, not_and, and_imp, leftset, rightset]
        rw [Finset.filter_eq']
        simp_all only [Finset.mem_powerset, subset_refl, ↓reduceIte, Finset.sum_singleton,Finset.erase_eq]
        rw [Finset.card_sdiff]
        · simp_all only [Finset.card_singleton, add_tsub_cancel_right]
        · simp_all only [Finset.singleton_subset_iff]

      dsimp [leftset, rightset] at sum_lem
      simp_all only [Finset.mem_filter, Finset.mem_powerset]

lemma total_eq_lem (n : Nat) {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α)(h : DecidablePred (λ s=> F.sets s)) (v : α)
  (v_in_ground : v ∈ F.ground)
  (ground_minus_v_none : ¬ (F.sets (F.ground \ {v})))
  (ground_ge_two : F.ground.card ≥ 2)
  (ground_card: F.ground.card = n + 1):
  ∑ x ∈ Finset.filter (fun s => (F.sets s ∧ v ∉ s) ∨ s = F.ground) (F.ground).powerset, x.card =
  ∑ x ∈ Finset.filter (fun s => (F.sets s ∧ v ∉ s) ∨ s = F.ground.erase v) (F.ground.erase v).powerset, x.card + 1:=
  by
    rw [total_eq_lem_left n F h v v_in_ground ground_ge_two ground_card]
    rw [total_eq_lem_right n F h v v_in_ground ground_minus_v_none ground_ge_two ground_card]

    have eq_lem: Finset.filter (fun s => F.sets s ∧ v ∉ s) F.ground.powerset = Finset.filter (fun s => F.sets s ∧ v ∉ s) (F.ground.erase v).powerset := by
      ext x

      simp_all only [Finset.mem_filter, Finset.mem_powerset]
      apply Iff.intro
      intro a
      simp_all only [ge_iff_le, Nat.reduceLeDiff, not_false_eq_true, and_self, and_true]
      obtain ⟨left, right⟩ := a
      obtain ⟨_, right⟩ := right
      intro y hy
      simp_all only [Finset.mem_erase, ne_eq]
      apply And.intro
      · apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        simp_all only
      · exact left hy

      intro a
      simp_all only [ge_iff_le, Nat.reduceLeDiff, not_false_eq_true, and_self, and_true]
      obtain ⟨left, right⟩ := a
      obtain ⟨left_1, right⟩ := right
      rw [Finset.subset_iff] at left
      simp_all only [Finset.mem_erase, ne_eq]
      intro y hy
      simp_all only

    simp_all only [ge_iff_le, Nat.reduceLeDiff]

lemma induction_assum_lem (n : Nat) (F: IdealFamily α) [DecidablePred F.sets] (idealDelF: IdealFamily α) [DecidablePred idealDelF.sets](v : α) (v_in_ground : v ∈ F.ground)  (ground_ge_two : F.ground.card ≥ 2) (ground_card: F.ground.card = n + 1)
  (h_ind: idealDelF.total_size_of_hyperedges * 2 ≤ idealDelF.number_of_hyperedges * idealDelF.ground.card):
  idealDelF = IdealFamily.deletion F v v_in_ground ground_ge_two → ((idealDelF.total_size_of_hyperedges: Int) + 1) * 2 ≤ (idealDelF.number_of_hyperedges: Int) * (F.ground.card: Int)
     := by

    intro h_ideal
    have h_ground: idealDelF.ground = F.ground \ {v} := by
      rw [h_ideal]
      dsimp [IdealFamily.deletion]
      rw [Finset.erase_eq]

    have h_ground_ideal: idealDelF.ground.card = n := by
      have h_assum_card: idealDelF.ground.card = F.ground.card - 1 := by
        rw [h_ground]
        rw [Finset.card_sdiff]
        simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.card_singleton, add_tsub_cancel_right]
        simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.singleton_subset_iff]
      simp_all only [ge_iff_le, Nat.reduceLeDiff, add_tsub_cancel_right]

    have h_assum_card1: idealDelF.ground.card ≥ 1 := by
      linarith

    rw [h_ground_ideal] at h_ind
    rw [ground_card]
    rw [add_mul]
    simp

    have h_ideal_total_card: idealDelF.number_of_hyperedges ≥ 2:= by
      exact setfamily_hyperedges_geq2 idealDelF

    linarith

lemma pq_transform (F : IdealFamily α) [DecidablePred F.sets] (v : α) (v_in_ground : v ∈ F.ground) (ground_ge_two : F.ground.card ≥ 2)(degone: F.degree v = 1):-- (singleton_none : ¬ (F.sets {v})) :
  ∀ s ∈ F.ground.powerset, F.sets s ↔ (F.sets s ∧ v ∉ s) ∨ s = F.ground :=
by
  intro s a
  apply Iff.intro
  intro a_1
  let hyp := hyperedges_not_through_v F.toSetFamily v v_in_ground degone (by exact F.has_ground) s a_1
  tauto

  intro a_2
  simp_all only [ge_iff_le, Finset.mem_powerset]
  cases a_2 with
  | inl h => simp_all only
  | inr h_1 =>
    subst h_1
    simp_all only [subset_refl]
    exact F.has_ground

lemma pq_transformDel (F : IdealFamily α) [DecidablePred F.sets] (v : α) (v_in_ground : v ∈ F.ground) (ground_ge_two : F.ground.card ≥ 2):
  let idealDelF := IdealFamily.deletion F v v_in_ground ground_ge_two
  ∀ s ∈ idealDelF.ground.powerset, idealDelF.sets s ↔ (idealDelF.sets s ∧ v ∉ s) ∨ s = F.ground \ {v}:=
by
  intro F' s hs
  have idealDefF_def: F' = IdealFamily.deletion F v v_in_ground ground_ge_two :=
  by
    rfl
  rw [idealDefF_def]
  dsimp [IdealFamily.deletion]
  apply Iff.intro
  intro a
  simp_all only [Finset.mem_powerset, true_and, F']
  cases a with
  | inl h => simp_all only [not_false_eq_true, true_or]
  | inr h_1 =>
    subst h_1
    simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true, true_or]

  intro a_1
  simp_all only [Finset.mem_powerset, true_and, F']
  cases a_1 with
  | inl h =>
    simp_all only [not_false_eq_true, and_true]
    obtain ⟨left, right⟩ := h
    simp_all only [not_false_eq_true, and_true]
  | inr h_1 =>
    subst h_1
    simp_all only [Finset.mem_sdiff, Finset.mem_singleton, not_true_eq_false, and_false, not_false_eq_true, and_true]
    apply Or.inr
    ext1 a
    simp_all only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_erase, ne_eq]
    apply Iff.intro
    · intro a_1
      simp_all only [not_false_eq_true, and_self]
    · intro a_1
      simp_all only [not_false_eq_true, and_self]

lemma number_lem (F : IdealFamily α) [DecidablePred F.sets] (v : α) (v_in_ground: v ∈ F.ground) (geq2: F.ground.card ≥ 2)(singleton_none: ¬F.sets {v}) (h_uv_not : ¬(F.sets (F.ground \ {v}))):
    let IdealDel := IdealFamily.deletion F v v_in_ground geq2
    haveI : DecidablePred IdealDel.sets :=
     by
       dsimp [IdealDel]
       dsimp [IdealFamily.deletion]
       intro s
       infer_instance
    IdealDel.number_of_hyperedges = F.number_of_hyperedges :=
  by
    let IdealDel := IdealFamily.deletion F v v_in_ground geq2
    haveI : DecidablePred IdealDel.sets :=
     by
       dsimp [IdealDel]
       dsimp [IdealFamily.deletion]
       intro s
       infer_instance
    have h_ground: IdealDel.ground = F.ground \ {v} := by
      dsimp [IdealDel]
      dsimp [IdealFamily.deletion]
      rw [Finset.erase_eq]
    have h_ground_card:IdealDel.ground.card = F.ground.card - 1 := by
      rw [h_ground]
      rw [Finset.card_sdiff]
      simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.card_singleton, add_tsub_cancel_right]
      simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.singleton_subset_iff]

    have degone: F.degree v = 1 := by
      exact degree_one_if_not_hyperedge F v_in_ground singleton_none

    let P (s : Finset α) := F.sets s ∧ v ∉ s
    let Q (s: Finset α) := s = F.ground
    let R (s: Finset α) := s = F.ground \ {v}

    have contradictPQ: ∀ s: Finset α, s ∈ F.ground.powerset → ¬((P s) ∧ (Q s)) := by
      intro s
      intro _
      by_contra h_contra
      obtain ⟨left, right⟩ := h_contra
      have v_in_s: v ∈ s := by
        dsimp [Q] at right
        rw [right]
        exact v_in_ground
      have v_not_in_s: v ∉ s := by
        dsimp [P] at left
        exact left.2
      contradiction

    have contradictPR: ∀ s: Finset α, s ∈ (F.ground \ {v}).powerset → ¬((P s) ∧ (R s)) := by
      intro s
      intro hs
      by_contra h_contra
      obtain ⟨left, right⟩ := h_contra
      dsimp [R] at right
      rw [←right] at h_uv_not
      exact h_uv_not left.1

    have FidealDelSets: ∀ (s : Finset α), s ∈ (F.ground \ {v}).powerset → ((F.deletion v v_in_ground geq2).sets s ↔ P s ∨ R s) := by
      intro s
      intro hs
      dsimp [P,R]
      rw [←h_ground] at hs
      rw [(pq_transformDel F v v_in_ground geq2) s hs]
      dsimp [IdealFamily.deletion]
      apply Iff.intro
      intro a
      simp at a
      rw [Finset.erase_eq] at a
      cases a
      case inl h =>
        simp at h
        cases h.1
        case inl h1 => exact Or.inl h1
        case inr h1 => exact Or.inr h1
      case inr h => exact Or.inr h

      intro a
      cases a
      case inl h =>
        exact Or.inl ⟨Or.inl h,h.2⟩
      case inr h =>
        exact Or.inr h

    have F_hand: F.number_of_hyperedges = (Finset.filter P F.ground.powerset).card + (Finset.filter Q F.ground.powerset).card:= by
      rw [IdealFamily.number_of_hyperedges]
      let result := pq_transform F v v_in_ground geq2 degone
      rw [Finset.filter_congr result]
      let result2 := filter_num F.ground.powerset contradictPQ
      rw [result2]
      congr

    have Q_card: (Finset.filter Q F.ground.powerset) = {F.ground} := by
      dsimp [Q]
      ext1 s
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      constructor
      · -- (s ∈ powerset ∧ s = F) → s = F
        intro ⟨_, h_eq⟩
        exact h_eq
      · -- s = F → (s ∈ powerset ∧ s = F)
        intro h_eq
        constructor
        · rw [h_eq]
        · exact h_eq

    have R_card: (Finset.filter R F.ground.powerset) = {F.ground \ {v}} := by
      dsimp [R]
      ext1 s
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      constructor
      · -- (s ∈ powerset ∧ s = F \ {v}) → s = F \ {v}
        intro ⟨_, h_eq⟩
        exact h_eq
      · -- s = F \ {v} → (s ∈ powerset ∧ s = F \ {v})
        intro h_eq
        constructor
        · rw [h_eq]
          rw [←Finset.erase_eq]
          exact Finset.erase_subset v F.ground
        · exact h_eq

    have number_small: Finset.filter P F.ground.powerset = Finset.filter P (F.ground \ {v}).powerset := by
      ext1 s
      apply Iff.intro
      · intro a
        dsimp [P]
        dsimp [P] at a
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
        dsimp [P]
        dsimp [P] at a
        rw [Finset.mem_filter] at a
        rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_powerset] at a
          rw [Finset.mem_powerset]
          rw [Finset.subset_sdiff] at a
          exact a.1.1
        · exact a.2

    have FDel_hand: IdealDel.number_of_hyperedges = (Finset.filter P F.ground.powerset).card + (Finset.filter R F.ground.powerset).card := by
      rw [IdealFamily.number_of_hyperedges]
      dsimp [IdealDel]
      rw [h_ground]
      rw [Finset.filter_congr FidealDelSets]
      --let result := pq_transformDel F v v_in_ground geq2
      --simp at result

      let result := filter_num (F.ground \ {v}).powerset contradictPR
      rw [result]

      dsimp [P,R]
      rw [number_small]
      simp
      have this1:(Finset.filter (fun s => s = F.ground \ {v}) (F.ground \ {v}).powerset) = {F.ground \ {v}} := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
        constructor
        · -- (s ∈ powerset ∧ s = F \ {v}) → s = F \ {v}
          intro ⟨_, h_eq⟩
          exact h_eq
        · -- s = F \ {v} → (s ∈ powerset ∧ s = F \ {v})
          intro h_eq
          constructor
          · rw [h_eq]
          · exact h_eq
      rw [this1]
      have this2:(Finset.filter (fun s => s = F.ground \ {v}) F.ground.powerset) = {F.ground \ {v}} := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
        constructor
        · -- (s ∈ powerset ∧ s = F \ {v}) → s = F \ {v}
          intro ⟨_, h_eq⟩
          exact h_eq
        · -- s = F \ {v} → (s ∈ powerset ∧ s = F \ {v})
          intro h_eq
          constructor
          · rw [h_eq]
            rw [←Finset.erase_eq]
            exact Finset.erase_subset v F.ground

          · exact h_eq
      rw [this2]

    rw [F_hand]
    simp
    simp_all only [Finset.mem_powerset, not_and, and_imp, Finset.card_singleton, Nat.cast_one, IdealDel, P, Q, R]
    convert FDel_hand

-- This likely uses the induction hypothesis 'ih', the family 'F', and the chosen vertex 'v'.
lemma degree_one_nothaveUV (F : IdealFamily α) [DecidablePred F.sets] (v : α) (v_in_ground: v ∈ F.ground) (geq2: F.ground.card ≥ 2)(singleton_none: ¬F.sets {v}) (h_uv_not : ¬(F.sets (F.ground \ {v})))
  (ih : ∀ (F' : IdealFamily α)[DecidablePred F'.sets], F'.ground.card = F.ground.card - 1 → F'.normalized_degree_sum ≤ 0)
  : F.normalized_degree_sum ≤ 0 :=
by

  let IdealDel := IdealFamily.deletion F v v_in_ground geq2
  haveI : DecidablePred IdealDel.sets :=
  by
    dsimp [IdealDel]
    dsimp [IdealFamily.deletion]
    intro s
    infer_instance

  have h_ground: IdealDel.ground = F.ground \ {v} := by
    dsimp [IdealDel]
    dsimp [IdealFamily.deletion]
    rw [Finset.erase_eq]
  have h_ground_card:IdealDel.ground.card = F.ground.card - 1 := by
    rw [h_ground]
    rw [Finset.card_sdiff]
    simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.card_singleton, add_tsub_cancel_right]
    simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.singleton_subset_iff]

  have h_card : F.ground.card = IdealDel.ground.card + 1 := by
    rw [h_ground_card]
    rw [Nat.sub_add_cancel]
    linarith

  let ihnds := ih IdealDel h_ground_card
  dsimp [IdealFamily.normalized_degree_sum] at ihnds
  have h_ind := induction_assum_lem (F.ground.card - 1) F IdealDel v v_in_ground geq2 (by linarith [h_card]) (by linarith [ihnds]) rfl

  simp [IdealFamily.normalized_degree_sum]

  have number := number_lem F v v_in_ground geq2 singleton_none h_uv_not

  have total:  F.total_size_of_hyperedges = IdealDel.total_size_of_hyperedges + 1 := by
    have degone: F.degree v = 1 := by
      exact degree_one_if_not_hyperedge F v_in_ground singleton_none
    rw [h_ground_card] at h_card
    let result:= total_eq_lem (F.ground.card - 1) F (by infer_instance) v v_in_ground h_uv_not geq2 h_card
    dsimp [IdealDel]
    dsimp [IdealFamily.deletion]
    dsimp [IdealFamily.total_size_of_hyperedges]
    have left_side: ∑ x ∈ Finset.filter (fun s => F.sets s ∧ v ∉ s ∨ s = F.ground) F.ground.powerset, x.card = ↑((Finset.filter F.sets F.ground.powerset).sum Finset.card) :=
    by
      let tmp:= pq_transform F v v_in_ground geq2 degone
      rw [Finset.filter_congr tmp]

    have right_side: ∑ x ∈ Finset.filter (fun s => F.sets s ∧ v ∉ s ∨ s = F.ground.erase v) (F.ground.erase v).powerset, x.card + 1 = ↑((Finset.filter IdealDel.sets (F.ground.erase v).powerset).sum Finset.card) + 1 :=
    by
      let result:= pq_transformDel F v v_in_ground geq2

      let result2:= Finset.filter_congr result
      dsimp [IdealFamily.deletion] at result2
      dsimp [IdealDel]
      dsimp [IdealFamily.deletion]
      rw [result2]
      congr
      rw [Finset.erase_eq]
      ext x
      apply Iff.intro
      intro a
      cases a with
      | inl h =>
        constructor
        · constructor
          · exact Or.inl h
          · exact h.2
      | inr h =>
        exact Or.inr h

      intro a
      cases a with
      | inl h =>
        exact h.1
      | inr h =>
        exact Or.inr h
    dsimp [IdealDel] at right_side
    dsimp [IdealFamily.deletion] at right_side
    simp at right_side
    rw [←right_side]
    rw [←left_side]
    rw [result]
    rfl
  rw [←total] at h_ind
  simp at number

  rw [←number]
  dsimp [IdealDel] at h_ind
  rw [mul_comm]
  convert h_ind

end Frankl
