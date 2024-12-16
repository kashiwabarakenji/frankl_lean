import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.Bool.Basic
import Init.SimpLemmas
import Mathlib.Tactic
import FranklLean.BasicDefinitions
import FranklLean.BasicLemmas

namespace Frankl

variable {α : Type} [DecidableEq α]

/-- A hyperedge `H` in an ideal family `F` is maximal if it is included in no strictly larger set,
    except for the ground set itself. -/
def is_maximal_hyperedge [Fintype α] (F : IdealFamily α) (H : Finset α): Prop :=
  F.sets H ∧ H ≠ F.ground ∧ (∀ (A: Finset α), F.sets A → H ⊂ A → A = F.ground)

omit [DecidableEq α]  in
lemma exists_max_card (F : Finset (Finset α)) (hF : F.Nonempty) :
  ∃ H ∈ F, ∀ s ∈ F, s.card ≤ H.card := by
  have nonempty_image : (F.image Finset.card).Nonempty := Finset.Nonempty.image hF Finset.card
  --let M := (F.image Finset.card).max' nonempty_image
  have M_in := (F.image Finset.card).max'_mem nonempty_image
  obtain ⟨H, H_in, H_eq⟩ := Finset.mem_image.mp M_in
  exists H
  apply And.intro H_in
  intro s s_in
  have : s.card ∈ F.image Finset.card := Finset.mem_image_of_mem Finset.card s_in
  rw [H_eq]
  exact (F.image Finset.card).le_max' s.card this

/-- If there is an ideal family, then there exists a maximal hyperedge. -/
theorem exists_maximal_hyperedge [Fintype α] (F : IdealFamily α) :
  ∃ H : Finset α, H ≠ F.ground ∧ F.sets H ∧ ∀ ⦃A : Finset α⦄, F.sets A → H ⊂  A → A = F.ground :=
by
  let elements := Finset.filter (λ s => (F.sets s = true && s ≠ F.ground : Prop)) (F.ground.powerset)
  have hne : elements.Nonempty :=
    by
      -- Since sf.has_empty, ∅ is in sf.sets, and ∅ ≠ sf.ground, so elements is nonempty.
      have : F.sets ∅ ∧ ∅ ≠ F.ground := ⟨F.has_empty, F.nonempty_ground.ne_empty.symm⟩
      rw [Finset.nonempty_iff_ne_empty]
      intro h_empty
      have : ∅ ∈ elements :=
        by
          rw [Finset.mem_filter, eq_self_iff_true]
          simp_all only [ne_eq, Bool.and_eq_true, decide_eq_true_eq,
              Finset.mem_powerset, Finset.empty_subset, not_false_eq_true, and_self]--
      simp_all only [Finset.not_mem_empty]

  obtain ⟨H, H_mem⟩ := exists_max_card elements hne
  use H
  obtain ⟨H_in_sets, H_le_card⟩ := H_mem
  constructor
  dsimp [elements] at H_in_sets
  rw [Finset.mem_filter] at H_in_sets

  simp_all only [  ne_eq,  Bool.and_eq_true, decide_eq_true_eq,not_false_eq_true]--

  constructor
  · simp_all only [ Bool.and_eq_true, decide_eq_true_eq,  Finset.mem_filter,  elements]

  · intros A hA hHA
    by_cases Aeq : A = F.ground
    case pos =>
      simp [Aeq]
    case neg =>
      by_cases AeqH : A = H
      case pos =>
        exfalso
        have H_ssub_A := hHA
        rw [Finset.ssubset_iff_subset_ne] at H_ssub_A
        exact H_ssub_A.2 AeqH.symm
      case neg =>
        have H_card_lt : H.card < A.card := Finset.card_lt_card hHA
        -- Use maximality contradiction
        have A_in_elem: A ∈ elements := by
          rw [Finset.mem_filter]
          dsimp [elements]
          simp_all only [ Finset.mem_powerset]
          constructor
          exact F.inc_ground A hA
          tauto
        let HLC := H_le_card A A_in_elem
        exfalso
        linarith

/-- Mapping a hyperedge by removing a certain element (or replacing it with G if the set is ground). -/
def map_hyperedge [Fintype α] (sf : IdealFamily α) (x : α) (G: Finset α)(H : Finset α) : Finset α :=
  if H = sf.ground then G else Finset.erase H x

/-- If `H` is a hyperedge, removing `x` (if `H` is not the ground) remains a hyperedge,
    provided `x ∉ G`. -/
theorem map_hyperedge_is_hyperedge [Fintype α]  (sf : IdealFamily α) (x : α) (G : Finset α) (gsets : sf.sets G) (H : Finset α) :
  sf.sets H → x ∉ G → sf.sets (map_hyperedge sf x G H) :=
by
  intros hH _
  unfold map_hyperedge
  by_cases H_univ : H = sf.ground
  · rw [if_pos H_univ]; exact gsets
  · rw [if_neg H_univ]
    have h_subset : (Finset.erase H x) ⊆ H := Finset.erase_subset x H
    exact sf.down_closed (H.erase x) H hH H_univ h_subset

/-- If two mapped hyperedges are equal and both sets are not the ground, then their originals
    differ only by erasing `x`. -/
lemma map_hyperedge_nonuniv_eq [Fintype α] (sf : IdealFamily α) (x : α) (G : Finset α) (H1 H2 : Finset α) :
  x ∈ H1 → x ∈ H2 → x ∉ G → H1 ≠ sf.ground → H2 ≠ sf.ground →
  map_hyperedge sf x G H1 = map_hyperedge sf x G H2 → Finset.erase H1 x = Finset.erase H2 x :=
by
  intros _ _ _ hH1 hH2 h_map
  unfold map_hyperedge at h_map
  rw [if_neg hH1, if_neg hH2] at h_map
  exact h_map

/- If two subtypes mapping to the same image, they must be equal. -/
theorem subtype_eq_of_val_eq [Fintype α] (sf : IdealFamily α) (x : α) (H1 H2 : { H // sf.sets H ∧ x ∈ H }) :
  H1.1 = H2.1 → H1 = H2 :=
by
  intro a
  obtain ⟨val, property⟩ := H1
  obtain ⟨val_1, property_1⟩ := H2
  simp_all only

/-- `map_hyperedge` is injective on the collection of hyperedges containing `x` if `x ∉ G`. -/
lemma map_hyperedge_injective [Fintype α] (F : IdealFamily α) (x : α) (G: Finset α) (imh : is_maximal_hyperedge F G)  :
  x ∉ G → Function.Injective (λ H : {H // F.sets H ∧ x ∈ H} => map_hyperedge F x G H.1):=
by
  intro hxG
  intros H1 H2 h_map
  by_cases h_univ1 : H1.1 = F.ground
  case pos =>
    have h_univ2 : H2.1 = F.ground :=
      by
        dsimp [map_hyperedge] at h_map
        simp [h_univ1] at h_map
        by_contra h_map2
        simp [h_map2] at h_map
        dsimp [is_maximal_hyperedge] at imh
        have h_map3: G ⊂ H2.1 := by
          rw [Finset.ssubset_iff_subset_ne]
          subst h_map
          simp_all only [ ne_eq,Finset.erase_eq_self, Decidable.not_not]
          obtain ⟨val, property⟩ := H1
          obtain ⟨val_1, property_1⟩ := H2
          simp_all only [and_true]
          subst h_univ1
          intro y hy
          simp_all only [Finset.mem_erase]
        exfalso
        have H2set: F.sets H2.1 := by
          subst h_map
          simp_all only [Finset.mem_erase]
          obtain ⟨val, property⟩ := H1
          obtain ⟨val_1, property_1⟩ := H2
          simp_all only
        let tmp:= imh.2.2 H2.1 H2set h_map3
        exact h_map2 tmp
    simp_all only
    obtain ⟨val, property⟩ := H1
    obtain ⟨val_1, property_1⟩ := H2
    simp_all only
  case neg =>
    by_cases h_univ2 : H2.1 = F.ground
    case pos =>
      have h_univ1 : H1.1 = F.ground :=
        by
          dsimp [map_hyperedge] at h_map
          simp [h_univ2] at h_map
          by_contra h_map2
          simp [h_map2] at h_map
          dsimp [is_maximal_hyperedge] at imh
          have h_map3: G ⊂ H1.1 := by
            rw [Finset.ssubset_iff_subset_ne]
            subst h_map
            simp_all only [ ne_eq, not_false_eq_true, Finset.erase_eq_self, Decidable.not_not]
            obtain ⟨val, property⟩ := H1
            obtain ⟨val_1, property_1⟩ := H2
            simp_all only [and_true]
            intro y hy
            simp_all only [Finset.mem_erase]
          exfalso
          have H1set: F.sets H1.1 := by
            subst h_map
            obtain ⟨val, property⟩ := H1
            simp_all only
          let tmp:= imh.2.2 H1.1 H1set h_map3
          exact h_map2 tmp
      simp_all only
    case neg =>
      have h_map2 := map_hyperedge_nonuniv_eq F x G H1.1 H2.1 H1.2.2 H2.2.2 hxG h_univ1 h_univ2 h_map
      dsimp [map_hyperedge] at h_map
      simp_all only [if_neg h_univ1, if_neg h_univ2]
      have H1x: x ∈ H1.1 := by
        obtain ⟨val, property⟩ := H1
        obtain ⟨left, right⟩ := property
        simp_all only
      have H2x: x ∈ H2.1 := by
        obtain ⟨val, property⟩ := H2
        obtain ⟨left, right⟩ := property
        simp_all only
      exact Subtype.eq ((erase_inj_of_mem H1x H2x).mp h_map2)

/-- Counting arguments: card(filter with v) + card(filter without v) = card(all sets). -/
lemma card_filter_add_card_filter_compl [Fintype α]  (F : SetFamily α) (v : α) [DecidablePred F.sets]  :
  (Finset.filter (λ H=> F.sets H ∧ v ∈ H) (F.ground.powerset)).card +
  (Finset.filter (λ H=> F.sets H ∧ v ∉ H) (F.ground.powerset)).card =
  (Finset.filter (λ H=> F.sets H) (F.ground.powerset)).card :=
by
  let with_v := Finset.filter (λ H => F.sets H ∧ v ∈ H) (F.ground.powerset)
  let without_v := Finset.filter (λ H => F.sets H ∧ v ∉ H) (F.ground.powerset)
  let all := Finset.filter (λ H => F.sets H) (F.ground.powerset)
  have h_disjoint : Disjoint with_v without_v :=
    by
      rw [Finset.disjoint_left]
      intro a a_1 a_2
      simp_all only [Finset.mem_filter,  not_true_eq_false, and_false, with_v, without_v]
  have h_union : with_v ∪ without_v = all :=
    by
      ext H
      simp
      constructor
      · intro h
        cases h
        case inl hl =>
          simp_all only [Finset.mem_filter, and_self, with_v, without_v, all]
        case inr hr =>
          simp_all only [Finset.mem_filter,  and_self, with_v, without_v, all]
      · intro h
        simp at h
        by_cases hv : v ∈ H
        simp_all only [Finset.mem_filter,  and_self, not_true_eq_false, and_false, or_false, with_v,
          without_v, all]

        simp_all only [Finset.mem_filter,  not_false_eq_true, and_self, or_true, without_v, all]
  have h_card_union : (with_v ∪ without_v).card = with_v.card + without_v.card := Finset.card_union_of_disjoint h_disjoint
  rw [h_union] at h_card_union
  simp_all only [with_v, without_v, all]

/-- Counting argument: the size of hyperedges without v is family_size - degree v. -/
lemma card_hyperedges_without_v [Fintype α] (F : SetFamily α) (v : α) [DecidablePred F.sets]:
  (Finset.card ((F.ground.powerset).filter (λ H => F.sets H ∧ v ∉ H))) =
  (F.number_of_hyperedges - F.degree v) :=
by
  rw [SetFamily.degree]
  unfold SetFamily.number_of_hyperedges

  let with_v := Finset.filter (λ H => F.sets H ∧ v ∈ H) (F.ground.powerset)
  let without_v := Finset.filter (λ H => F.sets H ∧ v ∉ H) (F.ground.powerset)
  let all := Finset.filter (λ H => F.sets H) (F.ground.powerset)

  have h_card_add : with_v.card + without_v.card = all.card := card_filter_add_card_filter_compl F v
  have h_card_with : with_v.card= F.degree v :=
    by
      simp_all only [eq_iff_iff, iff_true, with_v,all]
      dsimp [SetFamily.degree]
      --rw [Finset.card_filter]
      --simp_all only [Finset.sum_boole, Nat.cast_id, eq_iff_iff, iff_true, without_v]

  have h_card_all : all.card = F.number_of_hyperedges:=
    by
     dsimp [SetFamily.number_of_hyperedges]

  simp_all
  linarith

/-- If H ⊂ U and H ≠ U, there exists an element in U not in H. -/
lemma exists_element_not_in_univ (H U : Finset α) :
  H ⊆ U → H ≠ U → ∃ x ∈ U, x ∉ H :=
by
  intros h hne
  by_contra h'
  push_neg at h'
  have h_forall : ∀ x : α, x ∈ U → x ∈ H := λ x hx => h' x hx
  have U_sub_H : U ⊆ H := λ x hx => h_forall x hx
  have h_eq : H = U := Finset.Subset.antisymm h U_sub_H
  contradiction

omit [DecidableEq α] in
lemma fintypecoe (A : Finset α) : Fintype.card {x // x ∈ A} = A.card :=
by
  simp_all only [Fintype.card_coe]

omit [DecidableEq α] in
lemma fintypecard [Fintype α] (A : Finset α) : A.card ≤ Fintype.card α :=
by
  rw [Fintype.card, Finset.card_univ]
  exact Finset.card_le_card (Finset.subset_univ A)

/-- Ideal version of Frankl's conjecture (for an ideal family):
    There exists an element `v` in the ground set such that `2 * ideal_degree sf v ≤ ideal_family_size sf`. -/

theorem ideal_version_of_frankl_conjecture [Fintype α] (F : IdealFamily α) [DecidablePred F.sets] :
  ∃ (v : α), v ∈ F.ground ∧ 2 * F.degree v ≤ F.number_of_hyperedges :=
by
  obtain ⟨G, G_ne_univ, G_in_sf, G_max⟩ := exists_maximal_hyperedge F
  have G_maximal : is_maximal_hyperedge F G := ⟨G_in_sf, G_ne_univ, G_max⟩

  obtain ⟨v, v_in_ground, v_not_in_G⟩ := exists_element_not_in_univ G F.ground (F.inc_ground G G_in_sf) G_ne_univ

  set hyperedges_with_v := (F.ground.powerset).filter (λ H => F.sets H = true && v ∈ H) with hyperedge_with_v
  set hyperedges_without_v := (F.ground.powerset).filter (λ H => F.sets H = true && v ∉ H) with hyperedge_without_v

  let f: {H // F.sets H ∧ v ∈ H} → Finset α := λ H => map_hyperedge F v G H.1

  have map_range_in : ∀ H : {H // F.sets H ∧ v ∈ H}, f H ∈ hyperedges_without_v :=
    by
      intro H
      dsimp [hyperedges_without_v]
      dsimp [f]
      have h_map := map_hyperedge_is_hyperedge F v G G_in_sf H.1 H.2.1 v_not_in_G
      simp only [hyperedges_with_v, G_max]
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_powerset]
        by_cases H_eq_ground : H.1 = F.ground
        case pos =>
          have image_eq_G : map_hyperedge F v G H.1 = G := by
            unfold map_hyperedge
            rw [if_pos H_eq_ground]
          rw [image_eq_G]
          exact F.inc_ground G G_in_sf
        case neg =>
          exact F.inc_ground (map_hyperedge F v G H.1) h_map

      · -- goal
        have : (decide (F.sets (map_hyperedge F v G ↑H) = True) && decide (v ∉ map_hyperedge F v G ↑H)) :=
        by
          simp_all
          --goal v ∉ map_hyperedge F v G ↑H
          by_cases H_eq_ground : H.1 = F.ground
          case pos =>
            unfold map_hyperedge
            rw [if_pos H_eq_ground]
            exact v_not_in_G
          case neg =>
            unfold map_hyperedge
            rw [if_neg H_eq_ground]
            simp_all only [ Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
        exact this

  let ff : {H // F.sets H ∧ v ∈ H} → hyperedges_without_v := λ H => ⟨map_hyperedge F v G H.1, map_range_in H⟩
  have map_injective : Function.Injective (λ H : {H // F.sets H ∧ v ∈ H} => map_hyperedge F v G H.1) :=
    map_hyperedge_injective F v G G_maximal v_not_in_G

  have : Function.Injective f := by
    intro H1 H2 h
    dsimp [f] at h
    apply subtype_eq_of_val_eq F v H1 H2
    let tmp := map_injective h
    simp_all only [tmp]

  have ff_inj : Function.Injective ff := by
    intro H1 H2 h
    dsimp [ff] at h
    apply this
    dsimp [f]
    simp at h
    exact h

  have h_size_with_v : hyperedges_with_v.card = F.degree v := by
    rw [hyperedge_with_v]
    dsimp [IdealFamily.degree]
    simp_all only [ Bool.and_eq_true, decide_eq_true_eq]
    simp_all only [ne_eq, eq_iff_iff, iff_true, Bool.and_eq_true, decide_eq_true_eq, decide_not, Bool.not_eq_true',
      decide_eq_false_iff_not, hyperedges_with_v, hyperedges_without_v, f, ff]
  have h_size_ineq: hyperedges_with_v.card <= hyperedges_without_v.card := by
    let tmp := Fintype.card_le_of_injective ff ff_inj
    have cardsub1 :hyperedges_with_v = { H // F.sets H ∧ v ∈ H } := by
      simp_all
      congr
      ext x
      apply Iff.intro
      · intro h
        simp_all
      · intro h
        simp_all
        exact F.inc_ground x h.1

    have cardsub2:hyperedges_without_v = { H // F.sets H ∧ v ∉ H } := by
      simp_all
      congr
      ext x
      apply Iff.intro
      · intro h
        simp_all
      · intro h
        simp_all
        exact F.inc_ground x h.1

    have lem1: Fintype.card { x // x ∈ hyperedges_with_v} = Fintype.card { H // F.sets H ∧ v ∈ H } := by
      simp_all only [ hyperedges_without_v]
    have lem2: Fintype.card { x // x ∈ hyperedges_with_v} = hyperedges_with_v.card := by
      exact fintypecoe hyperedges_with_v
    have : Fintype.card { H // F.sets H ∧ v ∈ H } = hyperedges_with_v.card := by
      rw [←lem1, lem2]
    dsimp [hyperedges_with_v, hyperedges_without_v]
    simp_all
    have lem3: Fintype.card { x // x ∈ hyperedges_without_v} = Fintype.card { H // F.sets H ∧ v ∉ H } := by
      simp_all only [ Finset.mem_filter, Finset.mem_powerset]
    rw [this] at tmp
    have lem4: Fintype.card { H // F.sets H ∧ v ∉ H } = (Finset.filter (fun H => F.sets H ∧ v ∉ H) F.ground.powerset).card := by
      let tmp0 := @Fintype.card_ofFinset  _ (fun H => F.sets H ∧ v ∉ H ) (Finset.filter (fun H => F.sets H ∧ v ∉ H) F.ground.powerset)
      convert (tmp0 _)
      simp_all
      intro x
      apply Iff.intro
      · intro h
        tauto

      · intro h
        --simp_all only [f]
        constructor
        · exact F.inc_ground x h.1
        · tauto
    simp_all only [eq_iff_iff, iff_true, Bool.and_eq_true, decide_eq_true_eq]

  have h_family_size : hyperedges_with_v.card + hyperedges_without_v.card = F.number_of_hyperedges := by
    unfold IdealFamily.number_of_hyperedges
    let tmp := card_filter_add_card_filter_compl F.toSetFamily v
    simp_all
    linarith

  have h_degree_le_size : 2 *F.degree v ≤ F.number_of_hyperedges :=
    by
      rw [←h_size_with_v, ←h_family_size]
      linarith

  exact ⟨v, v_in_ground, h_degree_le_size⟩

end Frankl


/- `x` is not in `map_hyperedge sf x G H` by construction.
lemma map_hyperedge_excludes_x [Fintype α] (sf : IdealFamily α) (x : α) (G : Finset α) (H : Finset α) :
  sf.sets H → x ∉ G → x ∈ H → x ∉ map_hyperedge sf x G H :=
by
  intros _ hxG _
  unfold map_hyperedge
  by_cases H_eq_univ : H = sf.ground
  { rw [if_pos H_eq_univ]; simp [hxG] }
  { rw [if_neg H_eq_univ]; simp }
-/

/- If `G` is a maximal hyperedge, then adding a new element `x` not in `G`
    either does not produce a hyperedge or produces the ground set.
lemma G_union_x_hyperedge_or_univ [Fintype α] (sf : IdealFamily α) (x : α) (G : Finset α)
  (imh : is_maximal_hyperedge sf G) : x ∉ G → ¬sf.sets (G ∪ {x}) ∨ G ∪ {x} = sf.ground :=
by
  intro hxG
  by_cases h : sf.sets (G ∪ {x})
  { right
    obtain ⟨_, _ , G_max⟩ := imh
    have G_subset : G ⊂ G ∪ {x} := by
      rw [Finset.union_comm]
      rw [←Finset.insert_eq]
      exact Finset.ssubset_insert hxG

    specialize G_max (G ∪ {x}) h G_subset
    simp [G_max] }
  { left; exact h }
-/
/- This lemma helps in a more complex argument involving `map_hyperedge_injective`.
lemma map_hyperedge_univ_eq [Fintype α] (sf : IdealFamily α) (x : α) (G : Finset α) (imh : is_maximal_hyperedge sf G) (H : Finset α) :
  x ∈ H → sf.sets H → x ∉ G → H ≠ sf.ground → map_hyperedge sf x G H ≠ G :=
by
  intros hxH hsxH hxG hH
  unfold map_hyperedge
  by_cases h : H = sf.ground
  { simp [h]; contradiction }
  { rw [if_neg h]
    intro h_eq
    have H_eq : H = G ∪ {x} := by
      rw [←Finset.insert_erase hxH]
      subst h_eq
      simp_all only [Finset.insert_erase]
      ext1 a
      simp_all only [Finset.mem_union, Finset.mem_erase,  Finset.mem_singleton]
      apply Iff.intro
      · intro a_1
        simp_all only [and_true]
        tauto
      · intro a_1
        cases a_1 with
        | inl h_1 => simp_all only
        | inr h_2 =>
          subst h_2
          simp_all only
    have H_hyp_univ := G_union_x_hyperedge_or_univ sf x G imh hxG
    cases H_hyp_univ with
    | inl h_not_hyp => rw [←H_eq] at h_not_hyp; contradiction
    | inr h_univ => rw [←H_eq] at h_univ; contradiction }
-/

/- Strict subset characterization lemma.
lemma strict_subset_implies_univ (H A U: Finset α):
  ((H ⊂ A → A = U) ↔ (H ⊆ A → A = H ∨ A = U)) :=
by
  constructor
  { intro h H_sub_A
    by_cases h_eq : A = H
    { left; exact h_eq }
    { right
      have : H ⊂ A := by
        rw [Finset.ssubset_iff_subset_ne]
        simp_all only [ne_eq, true_and]
        apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        simp_all only [subset_refl, not_true_eq_false]
      exact h this } }
  { intro h H_ssub_A
    have H_sub_A := H_ssub_A.subset
    cases h H_sub_A with
    | inl hH =>
    subst hH
    simp_all only [subset_refl, true_or, imp_self]
    simpa using H_ssub_A.2
    | inr hU => exact hU }
-/

/- The size of hyperedges containing v is exactly the degree of v.
lemma card_hyperedges_with_v [Fintype α] (F : IdealFamily α) (v : α) [DecidablePred (λ H => F.sets H ∧ v ∈ H)] :
  Finset.card ((F.ground.powerset).filter (λ H => F.sets H ∧ v ∈ H)) = F.degree v :=
by
  rw [IdealFamily.degree]
  simp

-/
