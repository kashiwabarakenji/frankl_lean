import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset
import Init.Data.Int.Lemmas
import Init.Data.Nat.Lemmas
import Frankl.FranklMinors
import Frankl.BasicDefinitions
import Frankl.BasicLemmas
import LeanCopilot

namespace Frankl

variable {α : Type} [DecidableEq α][Fintype α]

lemma setfamily_hyperedges_geq2 (F : IdealFamily α) [DecidablePred F.sets] :
  F.number_of_hyperedges >= 2 :=
by
  dsimp [SetFamily.number_of_hyperedges]
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
      simp_all only [Finset.one_le_card]
      rw [← h] at h'
      simp_all only
      simp [← h] at h'
    simp_all only [Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton]--
  simp_all only [ge_iff_le, Nat.ofNat_le_cast]

lemma setfamily_hyperedges_total (F : IdealFamily α) [DecidablePred F.sets] :
  F.total_size_of_hyperedges >= 1 :=
by
  dsimp [SetFamily.total_size_of_hyperedges]
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

lemma family_union (F:SetFamily α)[DecidablePred F.sets] (v : α): Finset.filter (fun s => F.sets s) F.ground.powerset = Finset.filter (fun s =>F.sets s ∧ v ∈ s) (F.ground).powerset ∪ Finset.filter (fun s =>F.sets s ∧ v ∉ s) (F.ground).powerset:=
by
  ext1 a
  simp_all only [Finset.mem_filter,  Finset.mem_union]
  apply Iff.intro
  · intro a_1
    simp_all only [true_and]
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
    simp_all only [ not_and, not_true_eq_false, not_false_eq_true, implies_true]--

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

lemma filter_sum_eq (F : SetFamily α) (x : α)  [DecidablePred F.sets] :
  (Finset.filter (λ s => F.sets s ∧ x ∉ s) F.ground.powerset).sum Finset.card =
  (Finset.filter (λ s => F.sets s ∧ x ∉ s) (F.ground.erase x).powerset).sum Finset.card :=
by
  -- We aim to show that filtering `F.ground.powerset` vs. `(F.ground.erase x).powerset` with `x ∉ s`
  -- and `F.sets s` yields sets whose sums of `Finset.card` are equal.

  -- Use `Finset.sum_congr` followed by `Finset.ext` to reduce the problem to showing the filters define
  -- the same subsets element-wise.
  apply Finset.sum_congr
  apply Finset.ext
  intro s
  simp only [Finset.mem_filter, Finset.mem_powerset]

  -- We now prove a helper fact: if `x ∉ s`, then `s ⊆ F.ground` is equivalent to `s ⊆ F.ground.erase x`.
  have lem : x ∉ s → (s ⊆ F.ground ↔ s ⊆ F.ground.erase x) := by
    intro h
    constructor
    · -- (→) If s ⊆ F.ground and x ∉ s, then s also fits inside (F.ground.erase x)
      intro a
      intro y hy_in_s
      by_cases h1 : y = x
      · -- If y = x, this contradicts x ∉ s
        rw [h1] at hy_in_s
        contradiction
      · -- Otherwise, y ≠ x, so y ∈ s implies y ∈ F.ground.erase x
        simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]--
        exact a hy_in_s
    · -- (←) If s ⊆ F.ground.erase x, then trivially s ⊆ F.ground since (F.ground.erase x) ⊆ F.ground
      intro h2
      exact h2.trans (Finset.erase_subset _ _)

  simp_all only [and_congr_left_iff, not_false_eq_true,implies_true]--

  intro x_1 _

  simp only [Finset.mem_filter, Finset.mem_powerset]

lemma filter_sum_eq_int (F : SetFamily α) (x : α)  [DecidablePred F.sets] :
  (Finset.filter (fun s => F.sets s ∧ x ∉ s) F.ground.powerset).sum (fun (s: Finset α) => Int.ofNat s.card) = (Finset.filter (fun s => F.sets s ∧ x ∉ s) (F.ground.erase x).powerset).sum (fun (s: Finset α) => Int.ofNat s.card):=
by
  have h := filter_sum_eq F x
  apply Finset.sum_congr
  ext s
  simp_all only [Finset.mem_filter, Finset.mem_powerset]
  apply Iff.intro
  · intro a
    simp_all only [true_and]
    simp_all only [not_false_eq_true, and_true]
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
  · intro a
    simp_all only [not_false_eq_true, and_self, and_true]
    obtain ⟨left, right⟩ := a
    obtain ⟨left_1, right⟩ := right
    rw [Finset.subset_erase] at left
    exact left.1
  intro x_1 _
  simp_all only [ Int.ofNat_eq_coe]

---------------------------------------------------
theorem fintype_card_eq_of_bijective {α β : Type*}
  [Fintype α] [Fintype β][DecidableEq β] (f : α → β) (h : Function.Bijective f) :
  Fintype.card α = Fintype.card β := by
  let s := (Finset.univ : Finset α)
  let t := (Finset.univ : Finset β)

  have : (s.image f).card = s.card := Finset.card_image_of_injective s h.injective
  have : s.image f = t := Finset.ext (λ b => by
    constructor
    · -- 「→」方向 : b ∈ s.image f ⇒ b ∈ t
      intro _
      exact Finset.mem_univ b
    · -- 「←」方向 : b ∈ t ⇒ b ∈ s.image f
      intro _
      obtain ⟨a, ha⟩ := h.surjective b
      rw [Finset.mem_image]
      use a
      exact ⟨Finset.mem_univ a, ha⟩
  )

  calc
    Fintype.card α
      = s.card               := by rw [Finset.card_univ]
    _ = (s.image f).card     := by simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Finset.card_univ, s, t]
    _ = t.card               := by simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Finset.card_univ, s, t]
    _ = Fintype.card β       := by rw [Finset.card_univ]


lemma ha (F:SetFamily α)[DecidablePred F.sets] (v : α):
  let range := Finset.filter (fun (s :Finset α) ↦ F.sets s ∧ v ∈ s) F.ground.powerset
  let domain := Finset.filter (fun (s :Finset α) ↦ ∃ (H:Finset α), F.sets H ∧ v ∈ H ∧ s = H.erase v) (F.ground.erase v).powerset
  ∀ s ∈ domain, s ∪ {v} ∈ range :=
by
  intro s
  simp
  intro s_1 hs_1
  intro x
  intro Fsets
  intro v_in_x
  intro sv
  rw [sv]
  rw [sv] at hs_1
  have : x.erase v ∪ {v} = x := by
    subst sv
    ext
    simp_all only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]--
    apply Iff.intro
    · intro a
      cases a with
      | inl h => simp_all only
      | inr h_1 =>
        subst h_1
        simp_all only
    · intro a
      simp_all only [and_true]
      tauto
  rw [this]
  dsimp [s]
  rw [Finset.mem_filter]
  constructor
  rw [Finset.mem_powerset]
  exact F.inc_ground x Fsets
  exact ⟨Fsets, v_in_x⟩

lemma contraction_bijective (F:SetFamily α)[DecidablePred F.sets] (v : α):
  let range:= Finset.filter (fun (s :Finset α) ↦ F.sets s ∧ v ∈ s) F.ground.powerset
  let domain := Finset.filter (fun (s :Finset α) ↦ ∃ (H:Finset α), F.sets H ∧ v ∈ H ∧ s = H.erase v) (F.ground.erase v).powerset
  let f : domain → range := fun s => ⟨s.val ∪ {v}, ha F v s s.property⟩
  Function.Bijective f:=
by
  dsimp [Function.Bijective]
  constructor
  --injection
  · intro a1 a2
    intro vals
    simp at vals

    have h1: v ∉ a1.val:= by
      intro h
      have h' := a1.property
      simp_all only [Finset.mem_filter]
      obtain ⟨val, property⟩ := a1
      obtain ⟨val_1, property_1⟩ := a2
      obtain ⟨_, right⟩ := h'
      obtain ⟨w, h_1⟩ := right
      simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false]--

    have h2: v ∉ a2.val:= by
      intro h
      have h' := a2.property
      simp_all only [Finset.mem_filter]
      obtain ⟨val, property⟩ := a1
      obtain ⟨val_1, property_1⟩ := a2
      obtain ⟨_, right⟩ := h'
      obtain ⟨w, h_1⟩ := right
      simp_all only [Finset.mem_erase, ne_eq]--

    ext x
    apply Iff.intro
    intro a
    have : x ∈ a2.val ∪ {v} := by
      rw [←vals]
      rw [Finset.mem_union]
      exact Or.inl a
    rw [Finset.mem_union] at this
    cases this with
    | inl h => exact h
    | inr h_1 =>
      simp_all only [Finset.mem_singleton]

    intro a
    have : x ∈ a1.val ∪ {v} := by
      rw [vals]
      rw [Finset.mem_union]
      exact Or.inl a
    rw [Finset.mem_union] at this
    cases this with
    | inl h => exact h
    | inr h_1 =>
      simp_all only [Finset.mem_singleton]

  --surjection
  · intro a
    simp
    have : a.val.erase v ∈ Finset.filter (fun (s :Finset α) ↦ ∃ (H:Finset α), F.sets H ∧ v ∈ H ∧ s = H.erase v) (F.ground.erase v).powerset:=
    by
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_powerset]
        obtain ⟨val, property⟩ := a
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        obtain ⟨left, _⟩ := property
        intro x hx
        simp_all only [Finset.mem_erase, ne_eq]
        obtain ⟨_, right_1⟩ := hx
        simp_all only [not_false_eq_true, true_and]
        exact left right_1

      · constructor
        apply And.intro
        obtain ⟨val, property⟩ := a
        on_goal 2 => apply And.intro
        on_goal 3 => {rfl
        }
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        · obtain ⟨val, property⟩ := a
          simp_all only
          simp_all only [Finset.mem_filter, Finset.mem_powerset]
    use a.val.erase v
    constructor
    · simp_all only [Finset.mem_filter, Finset.mem_powerset]
      ext a_1 : 2
      simp_all only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]--
      obtain ⟨val, property⟩ := a
      simp_all only
      simp_all only [Finset.mem_filter]
      apply Iff.intro
      · intro a
        cases a with
        | inl h => simp_all only
        | inr h_1 =>
          subst h_1
          simp_all only
      · intro a
        simp_all only [and_true]
        tauto

    · simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self]--

lemma contraction_eq_card (F:SetFamily α)[DecidablePred F.sets] (v : α):
  let range:= Finset.filter (fun (s :Finset α) ↦ F.sets s ∧ v ∈ s) F.ground.powerset
  let domain := Finset.filter (fun (s :Finset α) ↦ ∃ (H:Finset α), F.sets H ∧ v ∈ H ∧ s = H.erase v) (F.ground.erase v).powerset
  range.card = domain.card :=
by
  let range:= Finset.filter (fun (s :Finset α) ↦ F.sets s ∧ v ∈ s) F.ground.powerset
  let domain := Finset.filter (fun (s :Finset α) ↦ ∃ (H:Finset α), F.sets H ∧ v ∈ H ∧ s = H.erase v) (F.ground.erase v).powerset
  simp
  have h := contraction_bijective F v
  let f : domain → range := fun s => ⟨s.val ∪ {v}, ha F v s s.property⟩
  let result := fintype_card_eq_of_bijective f h
  rw [Fintype.card_coe domain] at result
  rw [Fintype.card_coe range] at result
  simp_all only [domain, range]

/--
A small lemma that splits the sum over a union of two disjoint finsets.
-/
lemma sum_union_disjoint {α β : Type*} [AddCommMonoid β] [DecidableEq α]
  {s₁ s₂ : Finset α} (f : α → β) (h : Disjoint s₁ s₂) :
  (s₁ ∪ s₂).sum f = s₁.sum f + s₂.sum f :=
Finset.sum_union h

/--
This lemma partitions the hyperedges of `F` by whether they contain `v` or not, and shows that
the total size of hyperedges is preserved after this partition.
-/
lemma sum_partition_by_v (F : SetFamily α) (v : α) [DecidablePred F.sets] :
  {F with sets := λ s => F.sets s ∧ v ∈ s, inc_ground := λ s hs => F.inc_ground s hs.1 }.total_size_of_hyperedges  +
  {F with sets := λ s => F.sets s ∧ v ∉ s, inc_ground := λ s hs => F.inc_ground s hs.1 }.total_size_of_hyperedges  =
  F.total_size_of_hyperedges :=
by
  -- Expand each total_size_of_hyperedges definition
  rw [SetFamily.total_size_of_hyperedges,SetFamily.total_size_of_hyperedges,SetFamily.total_size_of_hyperedges]

  -- Define Fv and Fnv as the sets partitioned by v ∈ s or v ∉ s
  let Fv := (Finset.powerset F.ground).filter (λ s => F.sets s ∧ v ∈ s)
  let Fnv := (Finset.powerset F.ground).filter (λ s => F.sets s ∧ v ∉ s)
  let Fsets := (Finset.powerset F.ground).filter F.sets

  /- Show that Fsets = Fv ∪ Fnv. In other words, any set in Fsets either contains v or not. -/
  have disjoint_v : Fsets = Fv ∪ Fnv := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_powerset]
    apply Iff.intro
    · -- Forward direction
      intro a
      simp_all only [Finset.mem_filter, true_and, Fsets, Fv, Fnv]--
      obtain ⟨_, right⟩ := a
      contrapose! right
      simp_all only [not_and_self]
    · -- Backward direction
      intro a
      simp_all only [Finset.mem_filter, Fv, Fnv, Fsets]--
      cases a with
      | inl h => simp_all only [and_self]
      | inr h_1 => simp_all only [and_self]

  /- We now use the sum over the union to split total_size_of_hyperedges
     into two parts: one where v ∈ s and one where v ∉ s. -/
  have union_card_sum : (Fv ∪ Fnv).sum Finset.card = Fv.sum Finset.card + Fnv.sum Finset.card :=
  by
    -- We just apply our separate lemma for sum over a union of disjoint sets.
    apply sum_union_disjoint Finset.card
    -- Prove Fv and Fnv are disjoint: if a set is in Fv (v ∈ s) it can't be in Fnv (v ∉ s).
    rw [Finset.disjoint_left]
    intros a ha
    simp_all only [Finset.mem_filter,not_true_eq_false, and_false, not_false_eq_true,  Fv,   Fnv]--

  -- Combine everything
  simp_all only [Int.ofNat_eq_coe,  Nat.cast_add, Fsets]--

lemma number_eq_card (F : IdealFamily α) [DecidablePred F.sets] :
  F.number_of_hyperedges = F.toSetFamily.number_of_hyperedges :=
by
    rfl

lemma total_eq_card (F : IdealFamily α) [DecidablePred F.sets] :
  F.total_size_of_hyperedges = F.toSetFamily.total_size_of_hyperedges :=
by
    rfl

lemma nds_eq_card (F : IdealFamily α) [DecidablePred F.sets] :
  F.normalized_degree_sum = F.toSetFamily.normalized_degree_sum :=
by
    rfl

end Frankl
