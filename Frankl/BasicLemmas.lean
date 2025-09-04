import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
--import LeanCopilot

variable {α : Type} [DecidableEq α]

theorem erase_inj_of_mem {s t : Finset α} {x : α} (hx : x ∈ s) (ht : x ∈ t) :
  Finset.erase s x = Finset.erase t x ↔ s = t :=
by
  constructor
  · intro h
    apply Finset.ext
    intro a
    by_cases ha : a = x
    · rw [ha]
      simp_all

    simp only [ha, eq_self_iff_true] at h
    · constructor
      · intro h1 -- a ∈ s
        have hh: a ∈ s.erase x := Finset.mem_erase_of_ne_of_mem ha h1
        rw [h] at hh
        exact Finset.mem_of_mem_erase hh
      · intro h2 -- a ∈ t
        have hh: a ∈ t.erase x := Finset.mem_erase_of_ne_of_mem ha h2
        rw [←h] at hh
        exact Finset.mem_of_mem_erase hh

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
    have g_eq_x: ground = {x} := by
      ext y
      constructor
      · intro _
        have hy' : y ∈ ground \ {x} := by
            rw [h_empty]
            simp_all only [Finset.sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, false_or,Finset.card_singleton]--
            simp_all only [ge_iff_le, Nat.reduceLeDiff]
        rw [h_empty] at hy'
        contradiction

      · intro hy
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
    simp_all only [ Finset.mem_sdiff]
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

lemma filter_sum_func {α : Type} [DecidableEq α] [Fintype α]
  {P Q : Finset α → Prop} [DecidablePred P] [DecidablePred Q]
  (S : Finset (Finset α)) (g: Finset α → Nat) :
  (∀ (s : Finset α), s ∈ S → ¬ (P s ∧ Q s)) →
    (Finset.filter (λ s => P s ∨ Q s) S).sum g =
      (Finset.filter (λ s => P s) S).sum g +
      (Finset.filter (λ s => Q s) S).sum g :=
by
  intro disj
  let domain := Finset.filter (λ s => P s ∨ Q s) S
  let rangeP := Finset.filter (λ s => P s) S
  let rangeQ := Finset.filter (λ s => Q s) S

  -- domain is the union of rangeP and rangeQ. Used below implicitly.
  have d_union : domain = rangeP ∪ rangeQ := by
    apply Finset.ext
    intro x
    simp only [ Finset.mem_union]
    simp_all only [not_and, Finset.mem_filter, domain, rangeP, rangeQ]--
    apply Iff.intro
    · intro a
      simp_all only [true_and]
    · intro a
      cases a with
      | inl h => simp_all only [or_false, and_self]
      | inr h_1 => simp_all only [or_true, and_self]

  -- show the disjointness of rangeP and  rangeQ.
  have disjoint : Disjoint rangeP rangeQ := by
    simp only [Finset.disjoint_iff_inter_eq_empty]--
    ext x
    simp
    intro a
    simp_all only [not_and, Finset.mem_filter, and_false, not_false_eq_true,rangeP, rangeQ]--

  simp_all only [domain]
  rw [Finset.sum_union disjoint]

lemma filter_num {α : Type} [DecidableEq α] [Fintype α]
  {P Q : Finset α → Prop} [DecidablePred P] [DecidablePred Q]
  (S : Finset (Finset α)) :
  (∀ (s : Finset α), s ∈ S → ¬ (P s ∧ Q s)) →
    (Finset.filter (λ s => P s ∨ Q s) S).card =
      (Finset.filter (λ s => P s) S).card +
      (Finset.filter (λ s => Q s) S).card :=
by
  intro disj
  let domain := Finset.filter (λ s => P s ∨ Q s) S
  let rangeP := Finset.filter (λ s => P s) S
  let rangeQ := Finset.filter (λ s => Q s) S

  -- domain is the union of rangeP and rangeQ. Used below implicitly.
  have d_union : domain = rangeP ∪ rangeQ := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_union]
    simp_all only [not_and, Finset.mem_filter, domain, rangeP, rangeQ]--
    apply Iff.intro
    · intro a
      simp_all only [true_and]
    · intro a
      cases a with
      | inl h => simp_all only [or_false, and_self]--
      | inr h_1 => simp_all only [or_true, and_self]

  -- show the disjointness of rangeP and  rangeQ.
  have disjoint : Disjoint rangeP rangeQ := by
    simp only [Finset.disjoint_iff_inter_eq_empty]--
    ext x
    simp
    intro a
    simp_all only [not_and, Finset.mem_filter, and_false, not_false_eq_true,  rangeP, rangeQ]--

  simp_all only [ domain]
  simp_all only [Finset.card_union_of_disjoint]

  simp_all only [not_and, rangeQ, domain, rangeP]

lemma filter_union {α : Type} [DecidableEq α] [Fintype α]
  {P Q : Finset α → Prop} [DecidablePred P] [DecidablePred Q]
  (S : Finset (Finset α)) :
  (∀ (s : Finset α), s ∈ S → ¬ (P s ∧ Q s)) →
    (Finset.filter (λ s => P s ∨ Q s) S) =
      (Finset.filter (λ s => P s) S) ∪ (Finset.filter (λ s => Q s) S) :=
by
  intro a
  simp_all only [not_and]
  ext1 a_1
  simp_all only [Finset.mem_filter, Finset.mem_union]--
  apply Iff.intro
  · intro a_2
    simp_all only [true_and]
  · intro a_2
    cases a_2 with
    | inl h => simp_all only [or_false, and_self]
    | inr h_1 => simp_all only [or_true, and_self]

lemma add_compl {α : Type} [DecidableEq α] (X : Finset α) (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
  (Finset.filter P X).card =
    (Finset.filter (λ s => P s ∧ Q s) X).card +
    (Finset.filter (λ s => P s ∧ ¬Q s) X).card :=
by
  have h_disjoint : Disjoint
      (Finset.filter (λ s => P s ∧ Q s) X)
      (Finset.filter (λ s => P s ∧ ¬Q s) X) := by
    apply Finset.disjoint_filter.mpr
    intro s
    simp only [and_imp, not_and, not_not]
    intro _ _ h_not_Q
    intro _
    simp_all only

  have h_union :
    Finset.filter P X =
      Finset.filter (λ s => P s ∧ Q s) X ∪ Finset.filter (λ s => P s ∧ ¬Q s) X := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hP
      by_cases Q s
      · left; simp_all only [and_self]
      · right; simp_all only [not_false_eq_true, and_self]
    · intro hPQ
      cases hPQ with
      | inl h => simp_all only [and_self]
      | inr h => simp_all only [and_self]

  rw [h_union]
  rw [Finset.card_union_of_disjoint]
  exact h_disjoint

lemma add_compl_sum {α : Type} [DecidableEq α] (X : Finset α) (P Q : α → Prop) (c: α → Nat) [DecidablePred P] [DecidablePred Q] :
  (Finset.filter P X).sum c =
    (Finset.filter (λ s => P s ∧ Q s) X).sum c +
    (Finset.filter (λ s => P s ∧ ¬Q s) X).sum c :=
by
  have h_disjoint : Disjoint
      (Finset.filter (λ s => P s ∧ Q s) X)
      (Finset.filter (λ s => P s ∧ ¬Q s) X) := by
    apply Finset.disjoint_filter.mpr
    intro s
    simp only [and_imp, not_and, not_not]
    intro _ _ h_not_Q
    intro _
    simp_all only

  -- `filter P X` を `filter (P ∧ Q)` と `filter (P ∧ ¬Q)` に分割
  have h_union :
    Finset.filter P X =
      Finset.filter (λ s => P s ∧ Q s) X ∪ Finset.filter (λ s => P s ∧ ¬Q s) X := by
    -- `filter` の性質で示す
    ext s
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · -- 左から右
      intro hP
      by_cases Q s
      · left; simp_all only [and_self]
      · right; simp_all only [not_false_eq_true, and_self]
    · -- 右から左
      intro hPQ
      cases hPQ with
      | inl h => simp_all only [and_self]
      | inr h => simp_all only [and_self]

  rw [h_union]
  rw [Finset.sum_union h_disjoint]

lemma card_one (X : Finset α):(Finset.filter (λ (s:Finset α) => s = X) (X.powerset))= {X} :=
by
  ext s
  simp only [ Finset.mem_singleton]--
  constructor
  · intro h
    simp_all only [Finset.mem_filter, Finset.mem_powerset]
  · intro h_eq
    rw [h_eq]
    subst h_eq
    simp_all only [Finset.mem_filter, Finset.mem_powerset, subset_refl, and_self]--

lemma sum_one (X : Finset α) (c: Finset α → Nat): (Finset.filter (λ (s:Finset α) => s = X) (X.powerset)).sum c = c X :=
by
  rw [card_one]
  simp
