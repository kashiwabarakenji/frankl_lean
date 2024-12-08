import FranklLean.BasicDefinitions
import FranklLean.BasicLemmas

namespace Frankl

variable {α : Type} [DecidableEq α] [Fintype α]

def deletion {α : Type} [DecidableEq α] [Fintype α](F : SetFamily α) (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2): SetFamily α :=
  { ground := F.ground.erase x,

    -- In the deletion operation, sets are those that belong to the original family but do not contain x.
    sets := λ s => F.sets s ∧ ¬ x ∈ s,
    nonempty_ground := ground_nonempty_after_minor F.ground x hx ground_ge_two,

    inc_ground :=
      λ s hs => by
        simp_all only [decide_eq_false_iff_not]
        obtain ⟨left, right⟩ := hs
        -- Since s ∈ F.sets and s ⊆ F.ground, and also x ∉ s,
        -- we can show s ⊆ F.ground.erase x.
        have hs' : s ⊆ F.ground := F.inc_ground s left
        exact Finset.subset_erase.2 ⟨hs', right⟩
  }

infixl:65 " ∖ " => deletion

-- Proving that the deletion operation on an IdealFamily produces another IdealFamily.
-- The definition includes the proof inline.
def idealdeletion {α : Type} [DecidableEq α] [Fintype α] (F : IdealFamily α) (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2): IdealFamily α :=
{
    ground := F.ground.erase x,

    -- For idealdeletion, sets are either those from the original family that don't contain x,
    -- or the set that equals F.ground.erase x.
    sets := λ s => (F.sets s ∧ ¬ x ∈ s) ∨ s = F.ground.erase x,

    -- down_closed: If B is in the new family and A ⊆ B, then A is also in the new family,
    -- unless B was the ground set. We use the down_closed property of F to prove this.
    down_closed := λ A B hB hB_ne_ground hAB => by
      unfold SetFamily.sets at hB

      have hBor: (F.sets B ∧ ¬ x ∈ B) ∨ B = F.ground.erase x := by
        simpa using hB
      simp only [decide_eq_false_iff_not]
      match hBor with
      | Or.inl ⟨hB_set, hB_not_in_x⟩ =>
          -- Case 1: B is a set from F that does not contain x
          left
          -- Goal: F.sets A ∧ x ∉ A
          have B_neq_ground: B ≠ F.ground := by
            -- Since x ∈ F.ground and x ∉ B, B cannot be F.ground
            by_contra hB_eq_ground
            rw [hB_eq_ground] at hB_not_in_x
            contradiction

          have FsetsA: F.sets A := by
            exact F.down_closed A B hB_set B_neq_ground hAB
          have hA_not_in_x: ¬ x ∈ A := λ hA_mem_x => hB_not_in_x (Finset.mem_of_subset hAB hA_mem_x)
          exact ⟨FsetsA, hA_not_in_x⟩

      | Or.inr hB_eq =>
          -- Case 2: B = F.ground.erase x
          right
          contradiction

    inc_ground := λ s hs => by
        simp_all only [decide_eq_false_iff_not]
        cases hs with
        | inl hl =>
          -- If s is from F and doesn't contain x, then s ⊆ F.ground.erase x
          have hs'' : s ⊆ F.ground := F.inc_ground s hl.1
          exact Finset.subset_erase.2 ⟨hs'', hl.2⟩
        | inr hr =>
          -- If s = F.ground.erase x, then clearly s ⊆ F.ground.erase x
          rw [hr],

    has_empty := by
        -- Even after deletion, the empty set remains.
        have emp: F.sets ∅ := F.has_empty
        unfold SetFamily.sets at emp
        simp_all only [decide_eq_false_iff_not]
        rw [IdealFamily.toSetFamily] at emp
        simp,

    has_ground := by
        -- The "ground" set for this new family is F.ground.erase x,
        -- which by definition is included as a set in the family.
        let newsets := λ s => (F.sets s ∧ ¬ x ∈ s) ∨ s = F.ground.erase x
        have ss: newsets (F.ground.erase x) := by
          right
          rfl
        unfold SetFamily.sets at ss
        simp_all only [decide_eq_false_iff_not]
        rw [IdealFamily.toSetFamily]
        simp,

    nonempty_ground := ground_nonempty_after_minor F.ground x hx ground_ge_two,
}

def contraction (F : SetFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2): SetFamily α :=
  { ground := F.ground.erase x,

    -- For sets s in the contracted family, s corresponds to a set H in the original family that contained x,
    -- and s is obtained by erasing x from H.
    sets := λ (s: Finset α) => ∃ (H :Finset α), F.sets H ∧ x ∈ H ∧ s = H.erase x,

    inc_ground := by
      intros s hs
      rcases hs with ⟨H, hH_sets, _, hs_eq⟩
      rw [hs_eq]
      -- Goal: H.erase x ⊆ F.ground.erase x
      intro y hy -- hy: y ∈ H.erase x
      rw [Finset.mem_erase] at hy
      rw [Finset.mem_erase]
      -- We need to show: y ≠ x ∧ y ∈ F.ground
      constructor
      exact hy.1   -- y ≠ x
      apply F.inc_ground H hH_sets  -- Since H ⊆ F.ground
      exact hy.2   -- y ∈ H

    -- After removing x, the ground set is still nonempty because the original ground had at least two elements.
    nonempty_ground := ground_nonempty_after_minor F.ground x hx ground_ge_two
  }

-- Proving that if we contract an IdealFamily, we still get an IdealFamily.
instance contraction_ideal_family (F : IdealFamily α) (x : α) (hx : F.sets {x} ) (ground_ge_two: F.ground.card ≥ 2): IdealFamily α :=
{
  contraction (F.toSetFamily) x (by exact F.inc_ground {x} hx (by simp)) ground_ge_two with

  has_empty := by
    -- We must show that the empty set is in the contracted family.
    use {x}
    constructor
    exact hx       -- Show F.sets {x}
    constructor
    simp           -- Show x ∈ {x}
    simp

  has_ground := by
    -- Show that the new family still contains its "ground" set (after contraction).
    use F.ground
    constructor
    exact F.has_ground
    constructor
    -- We need to show x ∈ F.ground
    exact F.inc_ground {x} hx (by simp)
    rfl

  down_closed := by
    let thisF := contraction (F.toSetFamily) x (by exact F.inc_ground {x} hx (by simp)) ground_ge_two
    have thisg : thisF.ground = F.ground.erase x := by rfl
    have thisinc: thisF.ground ⊆ F.ground := by
      rw [thisg]
      apply Finset.erase_subset

    have groundx: F.ground = thisF.ground ∪ {x} := by
      ext y
      constructor
      -- If y ∈ F.ground:
      intro hy
      by_cases hxy: x = y
      -- If x = y, then obviously y ∈ thisF.ground ∪ {x}.
      rw [hxy]
      simp
      -- If x ≠ y:
      rw [Finset.mem_union, Finset.mem_singleton]
      left
      rw [thisg]
      rw [Finset.mem_erase]
      simp
      constructor
      tauto
      exact hy

      -- If y ∈ thisF.ground ∪ {x}, then y ∈ F.ground
      intro hy
      rw [Finset.mem_union, Finset.mem_singleton] at hy
      by_cases hy' : x = y
      case pos =>
        rw [←hy']
        exact F.inc_ground {x} hx (by simp)
      case neg =>
        have hinThis: y ∈ thisF.ground := by tauto
        have y_in_F_ground : y ∈ F.ground := by
          apply Finset.mem_of_subset thisinc hinThis
        exact y_in_F_ground

    intros A B hB hB_ne_ground hAB
    have thisF_sets: thisF.sets B := hB
    obtain ⟨H, _, _, hB_eq⟩ := hB

    have nxB: x ∉ B := by
      rw [hB_eq]
      exact Finset.not_mem_erase x H

    have nxA: x ∉ A := by
      by_contra h
      have hxB: x ∈ B := by apply hAB; exact h
      contradiction

    -- If thisF.sets B, then F.sets (B ∪ {x})
    have sets_imp: thisF.sets B → F.sets (B ∪ {x}) := by
      intro hB_sets
      obtain ⟨H, hH_sets, hxH, hB_eq⟩ := hB_sets
      have h_union : H = (B ∪ {x}) := by
        rw [hB_eq]
        rw [Finset.union_comm]
        rw [←Finset.insert_eq]
        rw [Finset.insert_erase]
        exact hxH
      rwa [← h_union]

    have Fsets: F.sets (B ∪ {x}) := by
      apply sets_imp
      exact thisF_sets

    have Fsets_down: F.sets (A ∪ {x}) := by
      apply F.down_closed (A ∪ {x}) (B ∪ {x})
      exact Fsets
      intro h
      -- If B ∪ {x} = F.ground:
      rw [groundx] at h
      -- Now B ∪ {x} = thisF.ground ∪ {x}
      apply hB_ne_ground
      -- Goal: B = thisF.ground
      have nthisF: x ∉ thisF.ground := by
        dsimp [thisF]
        dsimp [contraction]
        rw [Finset.erase_eq]
        simp
      have hB_eq2: B = thisF.ground := by
        ext y
        constructor
        -- y ∈ B → y ∈ thisF.ground
        intro hy
        have xneqy: x ≠ y := by
          intro hxy
          rw [←hxy] at hy
          contradiction
        have hyy: y ∈ thisF.ground ∪ {x} := by
          rw [←h]
          apply Finset.mem_union_left
          exact hy
        rw [Finset.mem_union] at hyy
        cases hyy with
        | inl hyy' => exact hyy'
        | inr hyy' =>
          rw [Finset.mem_singleton] at hyy'
          rw [hyy'] at xneqy
          contradiction
        -- y ∈ thisF.ground → y ∈ B
        intro hy
        have hyy: y ∈ thisF.ground ∪ {x} := by
          apply Finset.mem_union_left
          exact hy
        rw [←h] at hyy
        rw [Finset.mem_union] at hyy
        cases hyy with
        | inl hyy' => exact hyy'
        | inr hyy' =>
          rw [Finset.mem_singleton] at hyy'
          rw [hyy'] at hy
          contradiction

      rw [hB_eq2]
      exact Finset.union_subset_union hAB (by simp)

    have thisF_setsA: thisF.sets A := by
      dsimp [thisF]
      unfold contraction
      unfold SetFamily.sets

      have thisFset: (s : Finset α) → thisF.sets s ↔ ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x := by
        unfold SetFamily.sets
        dsimp [thisF]
        rw [contraction]
        simp

      have existsH: ∃ H, F.sets H ∧ x ∈ H ∧ A = H.erase x := by
        use A ∪ {x}
        constructor
        exact Fsets_down
        simp
        show A = (A ∪ {x}).erase x
        rw [Finset.union_comm]
        rw [←Finset.insert_eq]
        rw [Finset.erase_insert nxA]

      exact (thisFset A).mpr existsH

    exact thisF_setsA
}

lemma ground_deletion  (F : IdealFamily α) (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2):
  (idealdeletion F x hx ground_ge_two).ground.card = F.ground.card - 1 :=

  by
    rw [idealdeletion]
    rw [Finset.card_erase_of_mem hx]

lemma ground_contraction  (F : IdealFamily α) (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2):
  (contraction F.toSetFamily x hx ground_ge_two).ground.card = F.ground.card - 1 :=
  by
    rw [contraction]
    rw [Finset.card_erase_of_mem hx]

lemma ground_contraction_family  (F : IdealFamily α) (x : α) (ground_ge_two: F.ground.card ≥ 2)(singleton_have: F.sets {x}):
  (contraction_ideal_family F x singleton_have ground_ge_two).ground.card = F.ground.card - 1 :=
  by
    rw [contraction_ideal_family]
    rw [ground_contraction]

end Frankl