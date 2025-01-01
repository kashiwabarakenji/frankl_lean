import Mathlib.Data.Finset.Basic
--import Init.Data.Int.Lemmas
--import Init.Data.Nat.Lemmas
import Frankl.BasicDefinitions
import Frankl.BasicLemmas
import LeanCopilot

namespace Frankl

variable {α : Type} [DecidableEq α]



-- A theorem stating that every IdealFamily is intersection-closed.
theorem idealFamily_is_intersectionClosed {α : Type} [DecidableEq α] [Fintype α] (family : IdealFamily α) :
  isIntersectionClosedFamily family.toSetFamily := by
  unfold isIntersectionClosedFamily
  intros s t hs ht
  match Decidable.em (s = family.ground) with
  | Or.inl hsu =>
    rw [hsu]
    have tinc : t ⊆ family.ground := family.inc_ground t ht
    have h_inter_subset_t : family.ground ∩ t = t := Finset.inter_eq_right.mpr tinc
    rw [h_inter_subset_t]
    exact ht
  | Or.inr hsu =>
    match Decidable.em (t = family.ground) with
    | Or.inl htu =>
      rw [htu, Finset.inter_comm]
      have sinc : s ⊆ family.ground := family.inc_ground s hs
      have h_inter_subset_s : family.ground ∩ s = s := Finset.inter_eq_right.mpr sinc
      rw [h_inter_subset_s]
      exact hs
    | Or.inr _ =>
      have h_inter_subset_s : s ∩ t ⊆ s := @Finset.inter_subset_left _ _ s t
      have h_downward_closed := family.down_closed (s ∩ t) s hs hsu h_inter_subset_s
      exact h_downward_closed
-----------------------------------------------------------------------------------------
-- FG corresponds to the ground set (F.ground). This lemma generalizes a bit.
-- Definition: FG_product FG hyperedges is the Cartesian product of FG and hyperedges.
def FG_product (FG : Finset α) (hyperedges : Finset (Finset α)) [DecidableEq hyperedges] : Finset (α × Finset α) :=
  FG.product hyperedges

-- Definition: filtered_product is the subset of FG.product hyperedges where p.1 ∈ p.2.
def filtered_product (FG :Finset α) (hyperedges : Finset (Finset α)) [DecidableEq hyperedges]: Finset (α × Finset α) :=
  (FG_product FG hyperedges).filter (λ p => p.1 ∈ p.2)

-- Lemma: If x ⊆ FG, then FG.filter (λ a, a ∈ x ) = x. This is used immediately below.
lemma filter_eq_self_of_subset (FG : Finset α) (x : Finset α) (h_subset : x ⊆ FG) :
  FG.filter (λ a => a ∈ x) = x := by
  ext a
  constructor
  intro ha
  rw [Finset.mem_filter] at ha
  exact ha.right

  intro ha
  rw [Finset.mem_filter]
  constructor
  exact h_subset ha
  simp_all only

-- Main lemma: For any x ∈ hyperedges, after filtering, the cardinality equals x.card. Used later.
lemma filter_card_eq_x_card (FG :Finset α) (hyperedges : Finset (Finset α))
  (x : Finset α) (hx : x ∈ hyperedges)(hFG: ∀ s:Finset α, s ∈ hyperedges → s ⊆ FG) :
  ((filtered_product FG hyperedges).filter (λ ab => ab.2 = x)).card = x.card := by
    let domain := FG.filter (λ a => a ∈ x)
    let range := (filtered_product FG hyperedges).filter (λ ab => ab.2 = x )

    -- Using the lemma: x ⊆ FG
    have h_subset : x ⊆ FG := by simp_all only

    -- Using the lemma filter_eq_self_of_subset, domain = x
    have h_domain_eq : domain = x := filter_eq_self_of_subset FG x h_subset

    -- Define a mapping function f : domain → range
    let i: (a:α) → (a ∈ domain) → (α × Finset α) := fun a _ => (a, x)

    have hi: ∀ (a: α) (ha:a ∈ domain), i a ha ∈ range := by
      intros a ha
      simp only [Finset.mem_filter, and_true, i, domain, range]
      simp_all only [Finset.mem_filter]
      dsimp [filtered_product]
      dsimp [FG_product]
      simp_all only [Finset.mem_filter, and_true]
      have h1: a ∈ FG := by
        apply hFG
        on_goal 2 => exact ha
        simp_all only
      exact decarte FG hyperedges a x h1 hx

    -- Show that i is injective
    have inj : ∀ (a: α) (ha:a ∈ domain) (b: α) (hb: b ∈ domain), (i a ha = i b hb) → a = b := by
      intro a ha b hb hH
      simp_all only [Prod.mk.injEq, and_true, i, domain]

    have surj : ∀ p ∈ range, ∃ a, ∃ (h : a ∈ domain), i a h = p := by
       dsimp [range, filtered_product, FG_product, domain]
       intro p a
       simp_all only [Finset.mem_filter, exists_prop, domain, i]
       obtain ⟨fst, snd⟩ := p
       obtain ⟨left, right⟩ := a
       obtain ⟨_, right_1⟩ := left
       subst right
       simp_all only [Prod.mk.injEq, and_true, exists_eq_right]

    have bij := Finset.card_bij i hi inj surj
    rw [Finset.card_filter]
    simp [range]
    rw [← bij]
    rw [h_domain_eq]

/--- This also works, but we created a set3 version with A and B explicitly as arguments, not currently used.
lemma card_sum_over_fst_eq_card_sum_over_snd_set2 {α: Type u}[DecidableEq α][Fintype α] (C : Finset (α × (Finset α))) :
  C.card = Finset.univ.sum (fun a => (C.filter (fun ab => ab.fst = a)).card) ∧
  C.card = Finset.univ.sum (fun b => (C.filter (fun ab => ab.snd = b)).card) := by
  constructor
  · apply @Finset.card_eq_sum_card_fiberwise (α × Finset α) α _ (fun ab => ab.fst) C Finset.univ
    intro x _
    simp_all only [Finset.mem_univ]
  · apply @Finset.card_eq_sum_card_fiberwise (α × Finset α) (Finset α) _ (fun ab => ab.snd) C Finset.univ
    intros ab _
    exact Finset.mem_univ ab.snd
-/

-- A version without using univ. Used below.
lemma card_sum_over_fst_eq_card_sum_over_snd_set3 {α: Type}[DecidableEq α][Fintype α] (A: Finset α)(B:Finset (Finset α))(C : Finset (α × (Finset α))):
  C ⊆ (A.product B) →
  C.card = A.sum (fun a => (C.filter (fun ab => ab.1 = a)).card) ∧
  C.card = B.sum (fun b => (C.filter (fun ab => ab.2 = b)).card) := by
  intro hC
  constructor
  · apply @Finset.card_eq_sum_card_fiberwise (α × Finset α) α _ (fun ab => ab.fst) C A
    intro x _
    have hh: (x.1,x.2) ∈ A.product B := by
      apply hC
      simp_all only [Prod.mk.eta]
    exact (@decarter α x.1 x.2 A B hh).1

  · apply @Finset.card_eq_sum_card_fiberwise (α × Finset α) (Finset α) _ (fun ab => ab.snd) C B
    intro x a
    have hh: (x.1,x.2) ∈ A.product B := by
      apply hC
      simp_all only [Prod.mk.eta]
    exact (@decarter α x.1 x.2 A B hh).2

-- Main theorem: sum of cardinalities equals sum over hyperedges
theorem sum_cardinality_eq [Fintype α](FG : Finset α) [DecidableEq FG] (hyperedges : Finset (Finset α))(fground: ∀s:Finset α, s ∈ hyperedges → s ⊆ FG) :
  FG.sum (fun x => (FG.powerset.filter (fun s => s ∈ hyperedges ∧ x ∈ s)).card) =
  hyperedges.sum (fun s => s.card) := by

    let convert_product_to_pair (fa : Finset α) (fb : Finset (Finset α)) : Finset (α × Finset α) :=
      fa.product fb |>.map (Function.Embedding.refl (α × Finset α))

    let pairs := (convert_product_to_pair FG hyperedges) |>.filter (λ p => p.1 ∈ p.2)
    have inc: pairs ⊆ (FG.product hyperedges) := by
      simp_all only [Finset.map_refl, Finset.filter_subset, pairs, convert_product_to_pair]

    have h1 := @card_sum_over_fst_eq_card_sum_over_snd_set3 α _ _ FG hyperedges pairs inc

    have h2 := h1.1
    rw [h1.2] at h2

    dsimp [pairs] at h2
    simp at h2
    dsimp [convert_product_to_pair] at h2
    simp at h2

    -- Make the RHS and the goal's LHS match. Note that `Finset α` and `FG` differ by naming.
    have equal:  ∑ x ∈ FG, (Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product hyperedges))).card =
                 ∑ x ∈ FG, (Finset.filter (fun s => s ∈ hyperedges ∧ x ∈ s) FG.powerset).card := by
        apply Finset.sum_congr
        simp_all only [Finset.mem_univ]
        intro x _
        have equal_card :
          (Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product hyperedges))).card =
          (Finset.filter (fun s => s ∈ hyperedges ∧ x ∈ s) FG.powerset).card := by
          let i := (λ s (_ : s ∈ Finset.filter (fun s => s ∈ hyperedges ∧ x ∈ s) FG.powerset) => (x, s))

          have hi : ∀ (s : Finset α) (hs : s ∈ Finset.filter (fun s => s ∈ hyperedges ∧ x ∈ s) FG.powerset),
            i s hs ∈ Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product hyperedges)) := by
            intros s hs
            simp only [i, Finset.mem_filter, and_true, eq_self_iff_true, Prod.fst]
            simp_all only [Finset.mem_filter, pairs, convert_product_to_pair]
            obtain ⟨_, right⟩ := hs
            simp_all only [Finset.mem_powerset]
            have xinFG: x ∈ FG := by
              simp_all only
            convert decarte FG hyperedges x s xinFG right.1
            simp_all only [Finset.map_refl, Finset.filter_subset, and_self, and_true]

          -- i is injective
          have i_inj : ∀ (a₁ : Finset α) (ha₁ : a₁ ∈ Finset.filter (fun s => s ∈ hyperedges ∧ x ∈ s) FG.powerset)
            (a₂ : Finset α) (ha₂ : a₂ ∈ Finset.filter (fun s => s ∈ hyperedges ∧ x ∈ s) FG.powerset),
            i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂ := by
              intros a₁ ha₁ a₂ ha₂ h
              injection h with h1

          have i_surj : ∀ (b : α × Finset α)
            (_ : b ∈ Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product hyperedges))),
            ∃ a, ∃ (ha : a ∈ Finset.filter (fun s => s ∈ hyperedges ∧ x ∈ s) FG.powerset), i a ha = b := by
              intro b hb
              simp_all only [Finset.mem_filter, exists_prop, i, pairs,convert_product_to_pair]
              obtain ⟨fst, snd⟩ := b
              obtain ⟨left, right⟩ := hb
              obtain ⟨left_1, right_1⟩ := left
              apply Finset.mem_product.mp at left_1
              subst right
              simp_all only [Prod.mk.injEq, true_and, exists_eq_right, and_true]--
              simp_all only [Finset.mem_powerset]

          exact (Finset.card_bij i hi i_inj i_surj).symm
        exact equal_card

    rw [←equal]
    rw [←h2]

    apply Finset.sum_congr
    exact rfl
    intro x hx
    exact filter_card_eq_x_card FG hyperedges x hx fground

lemma sum_univ {α : Type} [DecidableEq α] [Fintype α] (f : α → ℕ) : ∑ x : α, f x = ∑ x in Finset.univ, f x := by
  simp_all only

-- Whether we sum over each vertex or sum the size of hyperedges, the result is the same.
-- This theorem could potentially be moved to another file.
theorem double_count {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) [DecidablePred F.sets]:
  F.total_size_of_hyperedges = ∑ x in F.ground, F.degree x := by
  rw [SetFamily.total_size_of_hyperedges]
  dsimp [SetFamily.degree]
  simp_all
  symm

  let Fsets := F.ground.powerset.filter (λ s => F.sets s)
  have ffground: (∀ s ∈ Fsets, s ⊆ F.ground) := by
    intros s hs
    dsimp [Fsets] at hs
    rw [Finset.mem_filter] at hs
    exact F.inc_ground s hs.2

  let tmp := sum_cardinality_eq F.ground Fsets ffground
  have subs: ∀ s:Finset α, s ∈ Fsets ↔ (F.sets s ∧ s ⊆ F.ground) := by
    dsimp [Fsets]
    intro s
    symm
    rw [Finset.mem_filter]
    apply Iff.intro
    intro h
    constructor
    rw [Finset.mem_powerset]
    exact h.2
    exact h.1

    intro h
    rw [Finset.mem_powerset] at h
    exact ⟨h.2, h.1⟩

  have subs2: ∑ x ∈ F.ground, (Finset.filter (fun s => s ∈ Fsets ∧ x ∈ s) F.ground.powerset).card =
               ∑ x ∈ F.ground, (Finset.filter (fun s => (F.sets s ∧ s ⊆ F.ground) ∧ x ∈ s) F.ground.powerset).card := by
    apply Finset.sum_congr
    swap
    intro x _
    simp only [subs]

    congr

  have subs3: ∑ x ∈ F.ground, (Finset.filter (fun s => (F.sets s ∧ s ⊆ F.ground) ∧ x ∈ s) F.ground.powerset).card =
               ∑ x ∈ F.ground, (Finset.filter (fun s => (F.sets s) ∧ x ∈ s) F.ground.powerset).card := by
    apply Finset.sum_congr
    swap
    intro x _
    let i := (λ s (_ : s ∈ F.ground.powerset.filter (λ s => (F.sets s ∧ s ⊆ F.ground) ∧ x ∈ s)) => s)
    have hi : ∀ s (hs : s ∈ F.ground.powerset.filter (λ s => (F.sets s ∧ s ⊆ F.ground) ∧ x ∈ s)), i s hs ∈ F.ground.powerset.filter (λ s => F.sets s ∧ x ∈ s) := by
      intros s hs
      simp_all only [i]
      rw [Finset.mem_filter] at hs
      rw [Finset.mem_filter]
      constructor
      exact hs.1
      obtain ⟨left, right⟩ := hs.2
      constructor
      exact left.1
      exact right

    have inj : ∀ (a₁ : Finset α) (ha₁:a₁ ∈ F.ground.powerset.filter (λ s => (F.sets s ∧ s ⊆ F.ground) ∧ x ∈ s))
      (a₂ : Finset α) (ha₂: a₂ ∈ F.ground.powerset.filter (λ s => (F.sets s ∧ s ⊆ F.ground) ∧ x ∈ s)), i a₁ ha₁ = i a₂ ha₂→ a₁ = a₂ := by
      intros a₁ _ a₂ _ h
      simp_all only [i]

    have surj : ∀ p ∈ F.ground.powerset.filter (λ s => F.sets s ∧ x ∈ s), ∃ a, ∃ (ha : a ∈ F.ground.powerset.filter (λ s => (F.sets s ∧ s ⊆ F.ground) ∧ x ∈ s)), i a ha = p := by
      intro p hp
      simp_all only [i]
      rw [Finset.mem_filter] at hp
      let hpp := hp.1
      rw [Finset.mem_powerset] at hpp
      use p
      constructor
      swap
      rw [Finset.mem_filter]
      constructor
      rw [Finset.mem_powerset]
      exact hpp
      constructor
      constructor
      exact hp.2.1
      exact hpp
      exact hp.2.2
      congr

    exact Finset.card_bij i hi inj surj
    congr

  rw [subs2] at tmp
  rw [subs3] at tmp

  dsimp [Fsets] at tmp

  norm_cast

set_option linter.unusedVariables false
lemma normalized_degree_sum_eq_sum_normalized_degree {α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) [DecidablePred F.sets] :
  F.normalized_degree_sum = ∑ x in F.ground, F.normalized_degree x :=
by
  calc
    F.normalized_degree_sum
    = ((∑ x in F.ground, F.degree x)) * 2 - (F.number_of_hyperedges * F.ground.card) := by
      dsimp [SetFamily.normalized_degree_sum]
      have h2 := double_count F
      rw [h2]
      simp
      ring
    _ = ((∑ x in F.ground, 2*(F.degree x)) : ℤ) - (F.ground.card * F.number_of_hyperedges : ℤ) := by
      ring_nf
      symm
      ring_nf
      simp_all only [add_right_inj]
      rw [Finset.sum_mul]
    _ = (∑ x in F.ground, (2*(F.degree x)) : Int) - ((∑ x in F.ground, 1) * (F.number_of_hyperedges : Int)) := by
      simp_all only [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (∑ x in F.ground, (2*(F.degree x)) : Int) - (∑ x in F.ground, (F.number_of_hyperedges): Int) := by
      simp_all only [Finset.sum_const]
      simp_all only [nsmul_eq_mul, mul_one]
    _ = ∑ x in F.ground, ((2*(F.degree x) : Int) - (F.number_of_hyperedges) : Int) := by
      simp_all only [Int.cast_sum, Int.cast_mul, Int.cast_ofNat, Pi.intCast_def, Int.cast_id, Finset.sum_const,
        nsmul_eq_mul, Int.cast_natCast, Pi.natCast_def, Finset.sum_sub_distrib, Int.cast_sub]
    _ = ∑ x in F.ground, F.normalized_degree x := by
      simp only [SetFamily.normalized_degree]
set_option linter.unusedVariables true
-- If the average normalized degree is rare (i.e., non-positive), then there is at least one vertex that is rare.
-- This is the main theorem of this file.
theorem average_rare_vertex [Nonempty α][Fintype α](F: SetFamily α) [DecidablePred F.sets] :
  F.normalized_degree_sum <= 0 → ∃ x ∈ F.ground, F.normalized_degree x <= 0 := by

  have ndegrees := normalized_degree_sum_eq_sum_normalized_degree F

  rw [ndegrees]
  intro h

  dsimp [SetFamily.normalized_degree] at h
  have h3 := sum_nonpos_exists_nonpos F.ground
    (by
      apply Finset.nonempty_iff_ne_empty.mp
      exact F.nonempty_ground
    )
    (fun x : α => (2 * F.degree x) - (F.number_of_hyperedges)) h

  obtain ⟨x, hx, h4⟩ := h3
  dsimp [SetFamily.normalized_degree] at h4
  use x
  constructor
  exact hx
  dsimp [SetFamily.normalized_degree]
  exact h4
-----------------------------------------------------------------------------------------
  theorem frankl_conjecture_equiv_by_contradiction :
  (∀ (F : SetFamily α) [DecidablePred F.sets],
    (F.sets ∅) →
    (F.sets F.ground) →
    isIntersectionClosedFamily F →
    ∃ (v:α), v ∈ F.ground ∧ 2 * F.degree v ≤ F.number_of_hyperedges)
  ↔
  (∀ (F : SetFamily α)[DecidablePred F.sets],
     (F.sets ∅) →
    F.number_of_hyperedges ≥ 2 →
    isIntersectionClosedFamily F →
    ∃ (v:α), v ∈ F.ground ∧ 2 * F.degree v ≤ F.number_of_hyperedges) :=
by
  constructor
  · intro h1 F deci hempty huniv hclosed
    let F' : SetFamily α :=
    {
      ground := F.ground,
      sets := fun s => (F.sets s) ∨ s = F.ground,
      inc_ground := fun s hs => by
        cases hs with
        | inl h => exact F.inc_ground s h
        | inr h => subst h; simp_all only [ge_iff_le, not_exists, not_and, not_le, subset_refl]
      nonempty_ground := F.nonempty_ground
    }
    have hempty' : F'.sets ∅ := by
      left
      exact hempty

    have hground: F'.sets F'.ground := by
      right
      rfl
    dsimp [isIntersectionClosedFamily] at hclosed
    have hclosed': isIntersectionClosedFamily F' := by
      intros s t hs ht
      dsimp [SetFamily.sets] at hs ht
      cases hs with
      | inl hs =>
        cases ht with
        | inl ht =>
          left
          exact hclosed hs ht
        | inr ht =>
          left
          subst ht
          simp_all only [Finset.inter_self]
          have: s ⊆ F.ground := F.inc_ground s hs
          have: s ∩ F.ground = s := by simp_all only [ge_iff_le, not_exists, not_and, not_le, true_or, or_true,
            Finset.inter_eq_left]
          rw [this]
          exact hs
      | inr hs => cases ht with
        | inl ht =>
          left
          subst hs
          have:t ⊆ F.ground := F.inc_ground t ht
          have: F.ground ∩ t  = t := by simp_all only [ge_iff_le, not_exists, not_and, not_le, true_or, or_true,
            Finset.inter_eq_right]
          rw [this]
          exact ht
        | inr ht =>
          right
          subst ht
          simp_all only [Finset.inter_self]
    have h := h1 F' hempty' hground hclosed'
    obtain ⟨v, vg, vineq⟩ := h
    use v
    constructor
    exact vg
    by_cases h:F.sets F.ground
    case pos =>
      have: F.degree v = F'.degree v := by
        simp only [SetFamily.degree]
        simp_all only [ge_iff_le, true_or, or_self, Int.ofNat_eq_coe, Nat.cast_inj, F']
        congr
        ext x : 2
        simp_all only [and_congr_left_iff, iff_self_or, implies_true]
      rw [this]
      have num_eq: F.number_of_hyperedges = F'.number_of_hyperedges :=
      by
        simp only [SetFamily.number_of_hyperedges]
        simp_all only [ge_iff_le, true_or, or_self, Int.ofNat_eq_coe, Nat.cast_inj, F']
        congr
        ext x : 2
        simp_all only [iff_self_or, implies_true]
      rw [num_eq]
      exact vineq

    case neg =>
      have degeq : F.degree v = F'.degree v - 1:= by
        simp only [SetFamily.degree]
        have add_comp:= add_compl F.ground.powerset (λ s => F.sets s ∧ v ∈ s ∨ s = F.ground) (λ s => s = F.ground)
        have sub1: ∀ s:Finset α, (((F.sets s  ∨ s = F.ground) ∧ s = F.ground) ∧ v ∈ s) ↔ s = F.ground :=
        by
          intro s
          constructor
          tauto
          intro hh
          rw [hh]
          constructor
          subst hh
          simp_all only [ge_iff_le, true_or, or_true, and_self, F']
          subst hh
          simp_all only [ge_iff_le, true_or, or_true, F']

        have sub2: ∀ s:Finset α, (F.sets s ∧ v ∈ s ∨ s = F.ground) ∧ s ≠ F.ground ↔ F.sets s ∧ v ∈ s:=
        by
          intro s
          apply Iff.intro
          intro a
          simp_all only [ge_iff_le, true_or, or_true, or_self_right, and_iff_right_iff_imp, implies_true, ne_eq,
            or_false]
          obtain ⟨left, right⟩ := a
          simp_all only [or_false]
          trivial

          intro hh
          constructor
          left
          simp_all only [ge_iff_le, true_or, or_true, or_self_right, and_iff_right_iff_imp, implies_true, F']
          simp
          by_contra hcontra
          rw [hcontra] at hh
          let hh1:= hh.1
          contradiction

        have sub3:  (Finset.filter (fun s => ((F.sets s ∧ v ∈ s) ∨ s = F.ground) ∧ s = F.ground) F.ground.powerset) =  (Finset.filter (fun s => s = F.ground) F.ground.powerset) :=
        by
          simp_all only [ge_iff_le, true_or, or_true, and_iff_right_iff_imp, implies_true, ne_eq, F']
          ext1 a
          simp_all only [Finset.mem_filter, Finset.mem_powerset, and_congr_right_iff, and_iff_right_iff_imp, or_true,
            implies_true]
        have sub4: (Finset.filter (fun s => ((F.sets s ∧ v ∈ s)∨ s = F.ground) ∧ s ≠ F.ground) F.ground.powerset) =  (Finset.filter (fun s => F.sets s ∧ v ∈ s) F.ground.powerset) :=
        by
          simp_all only [ge_iff_le, true_or, or_true, and_iff_right_iff_imp, implies_true, ne_eq, F']

        rw [sub3, sub4] at add_comp

        have sub5: (Finset.filter (fun s => s = F.ground) F.ground.powerset).card = 1 :=
        by
          simp_all only [ge_iff_le, true_or, or_true, and_iff_right_iff_imp, implies_true, ne_eq, F']
          rw [Finset.filter_eq']
          simp_all only [Finset.mem_powerset, subset_refl, ↓reduceIte, Finset.card_singleton]

        rw [sub5] at add_comp
        --ring_nf at add_comp
        --symm at add_comp
        rw [add_comm] at add_comp
        have :Finset.filter (fun s => F.sets s ∧ v ∈ s ∨ s = F.ground) F.ground.powerset = Finset.filter (fun s => (F.sets s ∨ s = F.ground) ∧ v ∈ s) F.ground.powerset :=
        by
          ext s
          simp_all only [Finset.mem_filter, Finset.mem_powerset, and_congr_right_iff, and_iff_right_iff_imp, or_true,
            implies_true]
          intro ss
          apply Iff.intro
          intro a
          simp_all only [ge_iff_le, true_or, ne_eq, F']
          cases a with
          | inl h_1 => simp_all only [true_or, and_self]
          | inr h_2 =>
            subst h_2
            simp_all only [subset_refl, or_true, and_self]

          intro a
          simp_all only [ge_iff_le, true_or, ne_eq, and_true, F']

        rw [this] at add_comp

        let add_comp_d:= add_compl F.ground.powerset (λ s => F.sets s∧ v ∈ s) (λ s => s = F.ground)

        have subd1: ∀ s:Finset α, ¬((F.sets s∧ v ∈ s) ∧ s = F.ground) :=
        by
          intro s
          by_contra hcontra
          let h1 := hcontra.1
          rw [hcontra.2] at h1
          let h11 := h1.1
          contradiction

        have subd2: ∀ s:Finset α, (F.sets s ∧ v ∈ s ) ∧ s ≠ F.ground ↔ F.sets s∧ v ∈ s :=
        by
          intro s
          apply Iff.intro
          intro a
          simp_all only [or_false]
          trivial

          intro hh
          constructor
          exact hh
          by_contra hcontra
          rw [hcontra] at hh
          let hh1:= hh.1
          contradiction

        have subd3:  (Finset.filter (fun s => (F.sets s ∧ v ∈ s ) ∧ s = F.ground) F.ground.powerset) =  ∅  :=
        by
          by_contra hcontra
          have :(Finset.filter (fun s => (F.sets s ∧ v ∈ s) ∧ s = F.ground) F.ground.powerset).Nonempty :=
          by
            exact Finset.nonempty_iff_ne_empty.mpr hcontra
          obtain ⟨s, hs⟩ := this
          rw [Finset.mem_filter] at hs
          let hs2 := hs.2.1
          let hs3 := hs.2.2
          rw [hs3] at hs2
          let hs21 := hs2.1
          contradiction

        have subd4: (Finset.filter (fun s => (F.sets s ∧ v ∈ s) ∧ s ≠ F.ground) F.ground.powerset) =  (Finset.filter (fun s => F.sets s ∧ v ∈ s) F.ground.powerset) :=
        by
          ext s
          apply Iff.intro
          intro hs
          rw [ Finset.mem_filter] at hs
          rw [Finset.mem_filter]
          constructor
          exact hs.1
          exact hs.2.1

          intro hs
          rw [ Finset.mem_filter] at hs
          rw [Finset.mem_filter]
          constructor
          exact hs.1
          constructor
          exact hs.2

          by_contra hcontra
          let hs2 := hs.2
          rw [hcontra] at hs2
          let hs21 := hs2.1
          contradiction

        rw [subd3, subd4] at add_comp_d

        clear subd1 subd2 subd3 subd4 sub1 sub2 sub3 sub4 sub5

        rw [add_comp]
        rw [add_comp_d]
        rw [Finset.card_empty]
        simp
        --lemma add_compl {α : Type} [DecidableEq α] (X : Finset α) (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
        --(Finset.filter P X).card = (Finset.filter (λ s => P s ∧ Q s) X).card + (Finset.filter (λ s => P s ∧ ¬Q s) X).card
      rw [degeq]
      have numeq : F.number_of_hyperedges = F'.number_of_hyperedges - 1 := by
        simp only [SetFamily.number_of_hyperedges]
        have : Finset.filter (fun s => (F.sets s ∨ s = F.ground)) F.ground.powerset = insert (F.ground: (Finset α)) (Finset.filter (fun s => F.sets s ) F.ground.powerset) := by
          simp_all only [ge_iff_le, true_or, or_true, F']
          ext1 a
          simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert]
          apply Iff.intro
          · intro a_1
            simp_all only [true_and]
            obtain ⟨left, right⟩ := a_1
            cases right with
            | inl h_1 => simp_all only [or_true]
            | inr h_2 =>
              subst h_2
              simp_all only [subset_refl, or_false]
          · intro a_1
            cases a_1 with
            | inl h_1 =>
              subst h_1
              simp_all only [subset_refl, or_true, and_self]
            | inr h_2 => simp_all only [true_or, and_self]
        rw [this]
        simp_all only [Int.ofNat_eq_coe, Finset.mem_filter,and_false, not_false_eq_true, Finset.card_insert_of_not_mem, Nat.cast_add, Nat.cast_one,add_sub_cancel_right]--
      have _: F.degree v ≤ F.number_of_hyperedges :=
      by
        rw [degeq]
        rw [numeq]
        linarith
      rw [numeq]
      linarith

  · intro h2 F deci hempty hnum hclosed
    have hnum2: F.number_of_hyperedges ≥ 2 := by
      dsimp [SetFamily.number_of_hyperedges]
      have : ∅ ∈ Finset.filter F.sets F.ground.powerset := by
        simp [hempty]
      have : F.ground ∈ Finset.filter F.sets F.ground.powerset := by
        simp [hnum]
      have : ∅ ≠ F.ground := by
        intro h
        have := F.nonempty_ground
        simp [← h] at this
      have inc_lem: {∅,F.ground} ⊆ F.ground.powerset := by
        intros x hx
        simp_all only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_powerset]--
        cases hx with
        | inl h =>
          subst h
          simp_all only [Finset.empty_subset]
        | inr h_1 =>
          subst h_1
          simp_all only [subset_refl]
      have inc2_lem: {∅,F.ground} ⊆ F.ground.powerset.filter F.sets := by
        simp_all only [Finset.subset_iff]
        intros x hx
        simp_all only [Finset.mem_insert, Finset.mem_singleton]--
        cases hx with
        | inl h =>
          subst h
          simp_all only [Finset.mem_filter]
          constructor
          simp_all only [and_self]
          simp_all only [and_self]
        | inr h_1 =>
          subst h_1
          simp_all only [Finset.mem_filter]
          constructor
          simp_all only [and_self]
          simp_all only [and_self]
      have : ({∅,F.ground}:Finset (Finset α)).card <= (F.ground.powerset.filter F.sets).card := by
        apply Finset.card_le_card
        exact inc2_lem
      simp_all only [Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton,Nat.ofNat_le_cast]--
    simp_all only [ge_iff_le]
