import FranklLean.BasicDefinitions
import FranklLean.BasicLemmas
import LeanCopilot

namespace Frankl

variable {α : Type} [DecidableEq α] [Fintype α]

def SetFamily.deletion {α : Type} [DecidableEq α] [Fintype α](F : SetFamily α) (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2): SetFamily α :=
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

/-
noncomputable instance deletionDecidablePred (F : SetFamily α) [DecidablePred F.sets] (x : α)
  (hx : x ∈ F.ground) (ground_ge_two : F.ground.card ≥ 2) :
  DecidablePred (SetFamily.deletion F x hx ground_ge_two).sets :=
λ s => by
  apply Classical.propDecidable
-/

instance (F : SetFamily α) [d: DecidablePred F.sets] (x : α)
  (hx : x ∈ F.ground) (ground_ge_two : F.ground.card ≥ 2) :
  DecidablePred (SetFamily.deletion F x hx ground_ge_two).sets := by
  dsimp [SetFamily.deletion]
  simp_all only [ge_iff_le]
  infer_instance


--infixl:65 " ∖ " => SetFamily.deletion

-- Proving that the deletion operation on an IdealFamily produces another IdealFamily.
-- The definition includes the proof inline.
def IdealFamily.deletion {α : Type} [DecidableEq α] [Fintype α] (F : IdealFamily α) (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2): IdealFamily α :=
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

instance (F : IdealFamily α) [d: DecidablePred F.sets] (x : α)
  (hx : x ∈ F.ground) (ground_ge_two : F.ground.card ≥ 2) :
  DecidablePred (IdealFamily.deletion F x hx ground_ge_two).sets :=
  by
    dsimp [IdealFamily.deletion]
    simp_all only [ge_iff_le]
    infer_instance

def SetFamily.contraction (F : SetFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2): SetFamily α :=
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

instance (F : SetFamily α) [d: DecidablePred F.sets] (x : α)
  (hx : x ∈ F.ground) (ground_ge_two : F.ground.card ≥ 2) :
  DecidablePred (SetFamily.contraction F x hx ground_ge_two).sets := by
  dsimp [SetFamily.contraction]
  simp_all only [ge_iff_le]
  infer_instance
/-
noncomputable instance contractionDecidablePred (F : SetFamily α) [DecidablePred F.sets] (x : α)
  (hx : x ∈ F.ground) (ground_ge_two : F.ground.card ≥ 2) :
  DecidablePred (SetFamily.contraction F x hx ground_ge_two).sets :=
λ s => by
  apply Classical.propDecidable
-/

-- Proving that if we contract an IdealFamily, we still get an IdealFamily.
instance IdealFamily.contraction (F : IdealFamily α) (x : α) (hs : F.sets {x} ) (ground_ge_two: F.ground.card ≥ 2): IdealFamily α :=
{
  SetFamily.contraction (F.toSetFamily) x (by exact F.inc_ground {x} hs (by simp)) ground_ge_two with

  has_empty := by
    -- We must show that the empty set is in the contracted family.
    use {x}
    constructor
    exact hs      -- Show F.sets {x}
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
    exact F.inc_ground {x} hs (by simp)
    rfl

  down_closed := by
    let thisF := SetFamily.contraction (F.toSetFamily) x (by exact F.inc_ground {x} hs (by simp)) ground_ge_two
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
        exact F.inc_ground {x} hs (by simp)
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
        dsimp [SetFamily.contraction]
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
      unfold SetFamily.contraction
      unfold SetFamily.sets

      have thisFset: (s : Finset α) → thisF.sets s ↔ ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x := by
        unfold SetFamily.sets
        dsimp [thisF]
        rw [SetFamily.contraction]
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

instance (F : IdealFamily α) [d: DecidablePred F.sets] (x : α)
  (hs : F.sets {x}) (ground_ge_two : F.ground.card ≥ 2) :
  DecidablePred (IdealFamily.contraction F x hs ground_ge_two).sets := by
    dsimp [IdealFamily.contraction]
    infer_instance

lemma set_ideal_contraction (F : IdealFamily α) (x : α) (hs: F.sets {x})(ground_ge_two: F.ground.card ≥ 2):--(h_uv_have : (F.sets (F.ground \ {x}))) :
  ∀ s : Finset α , ((F.contraction x hs ground_ge_two).sets s ↔ (F.toSetFamily.contraction x (by exact F.toSetFamily.inc_ground {x} hs (by simp)) ground_ge_two).sets s) :=
  by
   intro s
   rfl

lemma set_ideal_contraction_num  (F : IdealFamily α) (x : α) (hs: F.sets {x})(ground_ge_two: F.ground.card ≥ 2)
  [DecidablePred (F.contraction x hs ground_ge_two).sets]:
  (F.contraction x hs ground_ge_two).number_of_hyperedges = (F.toSetFamily.contraction x (by exact F.toSetFamily.inc_ground {x} hs (by simp)) ground_ge_two).number_of_hyperedges :=
  by
    dsimp [IdealFamily.contraction]
    --dsimp [SetFamily.contraction]
    --rfl

lemma set_ideal_contraction_total (F : IdealFamily α) (x : α) (hs: F.sets {x})(ground_ge_two: F.ground.card ≥ 2)
  [DecidablePred (F.contraction x hs ground_ge_two).sets]:
  (F.contraction x hs ground_ge_two).total_size_of_hyperedges = (F.toSetFamily.contraction x (by exact F.toSetFamily.inc_ground {x} hs (by simp)) ground_ge_two).total_size_of_hyperedges :=
  by
    dsimp [IdealFamily.contraction]
    --dsimp [SetFamily.contraction]
    --rfl


lemma ideal_deletion_haveuv (F : IdealFamily α) (x : α) (hs: F.sets {x})(ground_ge_two: F.ground.card ≥ 2) (h_uv_have : (F.sets (F.ground \ {x}))) :
  ∀ s : Finset α , ((F.deletion x (by exact F.toSetFamily.inc_ground {x} hs (by simp)) ground_ge_two).sets s ↔ (F.toSetFamily.deletion x (by exact F.toSetFamily.inc_ground {x} hs (by simp)) ground_ge_two).sets s) :=
  by
   intro s
   dsimp [IdealFamily.deletion]
   dsimp [SetFamily.deletion]
   simp_all only [ge_iff_le, or_iff_left_iff_imp, Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
     not_false_eq_true, and_true]
   intro a
   subst a
   convert h_uv_have
   ext1 a
   simp_all only [Finset.mem_erase, ne_eq, Finset.mem_sdiff, Finset.mem_singleton]
   apply Iff.intro
   · intro a_1
     simp_all only [not_false_eq_true, and_self]
   · intro a_1
     simp_all only [not_false_eq_true, and_self]

lemma ideal_deletion_noneuv (F : IdealFamily α) (x : α) (hs: F.sets {x})(ground_ge_two: F.ground.card ≥ 2) (h_uv_none : ¬(F.sets (F.ground \ {x}))) :
  ∀ s : Finset α , s ≠ F.ground \ {x} → ((F.deletion x (by exact F.toSetFamily.inc_ground {x} hs (by simp)) ground_ge_two).sets s ↔ (F.toSetFamily.deletion x (by exact F.toSetFamily.inc_ground {x} hs (by simp)) ground_ge_two).sets s) :=
by
  intro s hns
  dsimp [IdealFamily.deletion]
  dsimp [SetFamily.deletion]
  apply Iff.intro
  · intro h
    constructor
    · cases h with
        | inl h1 =>
          simp_all only [and_self, decide_eq_false_iff_not]
        | inr h1 =>
          simp_all only [and_self, decide_eq_false_iff_not]
          rw [Finset.erase_eq] at hns
          subst h1
          simp_all only [ge_iff_le, ne_eq, not_true_eq_false]
    · simp_all only [ge_iff_le, ne_eq]
      apply Aesop.BuiltinRules.not_intro
      intro a
      simp_all only [not_true_eq_false, and_false, false_or, Finset.mem_erase, ne_eq, false_and]
  · intro h
    constructor
    · exact h


lemma ideal_deletion_haveuv_num (F : IdealFamily α) (x : α)(hx:x ∈ F.ground)(ground_ge_two: F.ground.card ≥ 2) (h_uv_have : (F.sets (F.ground \ {x})))
  [DecidablePred (F.deletion x hx ground_ge_two).sets][DecidablePred (F.toSetFamily.deletion x hx ground_ge_two).sets]:
  (F.deletion x hx ground_ge_two).number_of_hyperedges = (F.toSetFamily.deletion x hx ground_ge_two).number_of_hyperedges :=
  by
    dsimp [IdealFamily.deletion]
    dsimp [SetFamily.deletion]
    --dsimp [IdealFamily.number_of_hyperedges]
    dsimp [SetFamily.number_of_hyperedges]
    simp_all only [Nat.cast_inj]
    congr
    ext X
    apply Iff.intro
    intro a
    cases a with
    | inl h => simp_all only [not_false_eq_true, and_self]
    | inr h_1 =>
      subst h_1
      simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true]
      convert h_uv_have
      ext1 a
      simp_all only [Finset.mem_erase, ne_eq, Finset.mem_sdiff, Finset.mem_singleton]
      apply Iff.intro
      · intro a_1
        simp_all only [not_false_eq_true, and_self]
      · intro a_1
        simp_all only [not_false_eq_true, and_self]

    intro a
    simp_all only [not_false_eq_true, and_self, true_or]


lemma ideal_deletion_haveuv_total (F : IdealFamily α) (x : α)(hx:x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2) (h_uv_have : (F.sets (F.ground \ {x})))
  [DecidablePred (F.deletion x hx ground_ge_two).sets][DecidablePred (F.toSetFamily.deletion x hx ground_ge_two).sets]:
  (F.deletion x hx ground_ge_two).total_size_of_hyperedges = (F.toSetFamily.deletion x hx ground_ge_two).total_size_of_hyperedges :=
by
  dsimp [IdealFamily.deletion]
  dsimp [SetFamily.deletion]
  --dsimp [IdealFamily.total_size_of_hyperedges]
  dsimp [SetFamily.total_size_of_hyperedges]
  simp_all only [Nat.cast_inj]
  congr
  ext x
  apply Iff.intro
  intro a
  cases a with
  | inl h => simp_all only [not_false_eq_true, and_self]
  | inr h_1 =>
    subst h_1
    simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true]
    convert h_uv_have
    ext1 a
    simp_all only [Finset.mem_erase, ne_eq, Finset.mem_sdiff, Finset.mem_singleton]
    apply Iff.intro
    · intro a_1
      simp_all only [not_false_eq_true, and_self]
    · intro a_1
      simp_all only [not_false_eq_true, and_self]
  intro a
  simp_all only [not_false_eq_true, and_self, true_or]


lemma ideal_deletion_noneuv_num (F : IdealFamily α)[DecidablePred F.sets] (x : α)(hx:x ∈ F.ground)(ground_ge_two: F.ground.card ≥ 2) (h_uv_none : ¬(F.sets (F.ground \ {x})))
  [DecidablePred (F.deletion x hx ground_ge_two).sets][DecidablePred (F.toSetFamily.deletion x hx ground_ge_two).sets]:
  (F.deletion x hx ground_ge_two).number_of_hyperedges = (F.toSetFamily.deletion x hx ground_ge_two).number_of_hyperedges + 1 :=
  by
    dsimp [IdealFamily.deletion]
    dsimp [SetFamily.deletion]
    --dsimp [IdealFamily.number_of_hyperedges]
    dsimp [SetFamily.number_of_hyperedges]
    --simp_all only [Nat.cast_inj]
    let P (s:Finset α) := (F.sets s ∧ ¬ x ∈ s) ∨ s = F.ground.erase x
    haveI : DecidablePred P := by
      rename_i inst_2 inst_3
      simp_all only [P]
      exact inst_2
    let Q (s:Finset α) := s = F.ground.erase x
    haveI : DecidablePred Q := by
      rename_i inst_2 inst_3
      simp_all only [Q]
      infer_instance

    have left_hand: (Finset.filter P (F.ground.erase x).powerset).card = (Finset.filter (λ s => P s ∧ Q s) (F.ground.erase x).powerset).card + (Finset.filter (λ s => P s ∧ ¬ Q s) (F.ground.erase x).powerset).card :=
    by
      exact add_compl (F.ground.erase x).powerset (λ s => P s) (λ s => Q s)
    have eqn1: ∀ s, (P s ∧ Q s) ↔ (s = F.ground.erase x) := by
      intro s
      simp_all only [and_iff_right_iff_imp,  or_true, implies_true, P, Q]

    have eqn1': ∀ s ∈ (F.ground.erase x).powerset, (P s ∧ Q s) ↔ (s = F.ground.erase x) := by
      intro s
      simp_all only [implies_true, P, Q]

    have eqn2 : ∀ s, (P s ∧ ¬ Q s) ↔ (F.sets s ∧ ¬ x ∈ s) := by
      intro s
      simp_all only [P, Q]
      apply Iff.intro
      · intro a
        cases a.1 with
        | inl h => simp_all only [not_false_eq_true, and_self, true_or, true_and]
        | inr h =>
        subst h
        simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true, or_true, and_false]
      · intro a
        constructor
        · simp_all only [not_false_eq_true, and_self, true_or]
        · intro h_eq
          rw [h_eq] at a
          rw [Finset.erase_eq] at a
          exact h_uv_none a.1
    haveI : DecidablePred (λ s => P s ∧ Q s) := by
      intro s
      exact And.decidable

    haveI : DecidablePred (λ s => P s ∧ ¬ Q s) := by
      intro s
      exact And.decidable

    have left_hand': (Finset.filter (fun s => F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) (F.ground.erase x).powerset).card =
    (Finset.filter (fun s => (s = F.ground.erase x) )  (F.ground.erase x).powerset).card +
    (Finset.filter (fun s => F.sets s ∧ x ∉ s) (F.ground.erase x).powerset).card := by
      simp_all

    have :  (Finset.filter (fun s => (s = F.ground.erase x)) (F.ground.erase x).powerset).card = 1 := by
      simp_all only [Finset.card_eq_one]
      use F.ground.erase x
      convert card_one (F.ground.erase x)

    rw [this] at left_hand'

    ring_nf
    norm_cast
    convert left_hand'

lemma ideal_deletion_noneuv_total (F : IdealFamily α) [DecidablePred F.sets](x : α)(hx:x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2) (h_uv_none : ¬(F.sets (F.ground \ {x})))
  [DecidablePred (F.deletion x hx ground_ge_two).sets][DecidablePred (F.toSetFamily.deletion x hx ground_ge_two).sets]:
  (F.deletion x hx ground_ge_two).total_size_of_hyperedges = (F.toSetFamily.deletion x hx ground_ge_two).total_size_of_hyperedges + (F.ground.card - 1) :=
by
  dsimp [IdealFamily.deletion]
  dsimp [SetFamily.deletion]
  --dsimp [IdealFamily.total_size_of_hyperedges]
  dsimp [SetFamily.total_size_of_hyperedges]
  --simp_all only [Nat.cast_inj]
  let P (s:Finset α) := (F.sets s ∧ ¬ x ∈ s) ∨ s = F.ground.erase x
  haveI : DecidablePred P := by
    rename_i inst_2 inst_3
    simp_all only [P]
    exact inst_2
  let Q (s:Finset α) := s = F.ground.erase x
  haveI : DecidablePred Q := by
    rename_i inst_2 inst_3
    simp_all only [Q]
    infer_instance
  have left_hand: ((Finset.filter (fun s => P s) (F.ground.erase x).powerset).sum Finset.card) = (Finset.filter (λ s => P s ∧ Q s) (F.ground.erase x).powerset).sum Finset.card + (Finset.filter (λ s => P s ∧ ¬ Q s) (F.ground.erase x).powerset).sum Finset.card  :=
  by
    exact add_compl_sum (F.ground.erase x).powerset (λ s => P s) (λ s => Q s)  (λ s => s.card)

  have eqn1: ∀ s, (P s ∧ Q s) ↔ (s = F.ground.erase x) := by
    intro s
    simp_all only [and_iff_right_iff_imp, or_true, implies_true, P]
  have eqn1': ∀ s ∈ (F.ground.erase x).powerset, (P s ∧ Q s) ↔ (s = F.ground.erase x) := by
    intro s
    simp_all only [not_false_eq_true,or_true, implies_true, P, Q]

  have eqn2 : ∀ s, (P s ∧ ¬ Q s) ↔ (F.sets s ∧ ¬ x ∈ s) := by
    intro s
    simp_all only [  not_false_eq_true, or_true, implies_true, P, Q]
    apply Iff.intro
    · intro a
      cases a.1 with
      | inl h => simp_all only [not_false_eq_true, and_self, true_or, true_and]
      | inr h =>
      subst h
      simp_all only [ not_true_eq_false, and_true, not_false_eq_true, or_true, and_false]
    · intro a
      constructor
      · simp_all only [not_false_eq_true, and_self, true_or]
      · intro h_eq
        rw [h_eq] at a
        rw [Finset.erase_eq] at a
        exact h_uv_none a.1

  haveI : DecidablePred (λ s => P s ∧ Q s) := by
    intro s
    exact And.decidable

  haveI : DecidablePred (λ s => P s ∧ ¬ Q s) := by
    intro s
    exact And.decidable

  have left_hand': (Finset.filter (fun s => F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) (F.ground.erase x).powerset).sum Finset.card =
    (Finset.filter (fun s => (s = F.ground.erase x) )  (F.ground.erase x).powerset).sum Finset.card +
    (Finset.filter (fun s => F.sets s ∧ x ∉ s) (F.ground.erase x).powerset).sum Finset.card := by
      haveI : DecidablePred (fun s => F.sets s ∧ x ∉ s) := by
        intro s
        exact And.decidable
      simp_all
      simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true, or_true, P, Q]
      congr

  have :  (Finset.filter (fun s => (s = F.ground.erase x)) (F.ground.erase x).powerset).sum Finset.card = F.ground.card - 1 := by
    have lem: (F.ground \ {x}).card = F.ground.card - 1 := by
      simp_all only [add_right_inj, and_iff_right_iff_imp, Finset.mem_erase, ne_eq, not_true_eq_false, and_true,
        not_false_eq_true, or_true, implies_true, Finset.mem_powerset, P, Q]
      rw [Finset.card_sdiff]
      · simp_all only [Finset.card_singleton]
      · simp_all only [Finset.singleton_subset_iff]
    rw [←lem]
    rw [←Finset.erase_eq]

    let co_sum:=  sum_one (F.ground.erase x) (λ s => s.card)
    calc
    (Finset.filter (fun s => s = F.ground.erase x) (F.ground.erase x).powerset).sum Finset.card
      = (Finset.filter (fun s => s = F.ground.erase x) (F.ground.erase x).powerset).sum (λ s => s.card) := by simp_all only [add_right_inj,
        and_iff_right_iff_imp, Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true, or_true,
        implies_true, Finset.mem_powerset, P, Q]
   _  = (Finset.filter (λ s => s = F.ground.erase x) (F.ground.erase x).powerset).sum (λ s => s.card) := by simp_all only [Finset.sum_filter]
   _  = Finset.sum {F.ground.erase x} (λ s => s.card) := by convert co_sum
   _  = Finset.card (F.ground.erase x) := by simp_all only [Finset.sum_singleton, Finset.card_erase_of_mem, P, Q]

  rw [this] at left_hand'

  have : Int.ofNat (F.ground.card - 1)= (F.ground.card : ℤ) - 1 := by
      simp
      omega

  have h_cast : ∑ x ∈ Finset.filter (fun s => F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) (F.ground.erase x).powerset, ↑x.card =
  -1 + (F.ground.card : ℤ) + ∑ x ∈ Finset.filter (fun s => F.sets s ∧ x ∉ s) (F.ground.erase x).powerset, (x.card : ℤ) :=
  by
    simp_all only [Int.ofNat_eq_coe]
    norm_cast
    rw [left_hand']
    simp_all only [Nat.cast_add]
    rfl

  rw [Int.add_comm]
  norm_cast
  simp_all
  convert h_cast

lemma nds_deletion_haveuv (F : IdealFamily α) [DecidablePred F.sets] (x : α) (hx : x ∈ F.ground) (geq2: F.ground.card ≥ 2)
  [DecidablePred F.sets](hx_hyperedge : F.sets (F.ground \ {x})) :
  (F.deletion x hx geq2).normalized_degree_sum = (F.toSetFamily.deletion x hx geq2).normalized_degree_sum :=
by
  calc
    (F.deletion x hx geq2).normalized_degree_sum
        = 2 * (F.deletion x hx geq2).total_size_of_hyperedges - (F.deletion x hx geq2).number_of_hyperedges * Int.ofNat (F.deletion x hx geq2).ground.card := by
          dsimp [SetFamily.normalized_degree_sum]
      _ = 2 * (F.toSetFamily.deletion x hx geq2).total_size_of_hyperedges - (F.toSetFamily.deletion x hx geq2).number_of_hyperedges * Int.ofNat (F.toSetFamily.deletion x hx geq2).ground.card := by
        rw [ideal_deletion_haveuv_num F x hx geq2 hx_hyperedge]
        rw [ideal_deletion_haveuv_total F x hx geq2 hx_hyperedge]
        simp_all only [Int.ofNat_eq_coe, sub_right_inj, mul_eq_mul_left_iff, Nat.cast_inj]
        tauto
      _ = (F.toSetFamily.deletion x hx geq2).normalized_degree_sum := by
          simp_all only [Int.ofNat_eq_coe]
          rfl

lemma nds_contraction_haveuv (F : IdealFamily α) [DecidablePred F.sets] (x : α) (hs : F.sets {x}) (geq2: F.ground.card ≥ 2)
  [DecidablePred F.sets] :
  (F.contraction x hs geq2).normalized_degree_sum = (F.toSetFamily.contraction x (by exact F.toSetFamily.inc_ground {x} hs (by simp)) geq2).normalized_degree_sum :=
by
  calc
    (F.contraction x hs geq2).normalized_degree_sum
        = 2 * (F.contraction x hs geq2).total_size_of_hyperedges - (F.contraction x hs geq2).number_of_hyperedges * Int.ofNat (F.contraction x hs geq2).ground.card := by
          dsimp [SetFamily.normalized_degree_sum]
      _ = 2 * (F.toSetFamily.contraction x (by exact F.toSetFamily.inc_ground {x} hs (by simp)) geq2).total_size_of_hyperedges - (F.toSetFamily.contraction x (by exact F.toSetFamily.inc_ground {x} hs (by simp)) geq2).number_of_hyperedges * Int.ofNat (F.toSetFamily.contraction x (by exact F.toSetFamily.inc_ground {x} hs (by simp)) geq2).ground.card := by
        rw [set_ideal_contraction_num F x hs geq2]
        rw [set_ideal_contraction_total F x hs geq2]
        simp_all only [Int.ofNat_eq_coe, sub_right_inj, mul_eq_mul_left_iff, Nat.cast_inj]
        tauto
      _ = (F.toSetFamily.contraction x (by exact F.toSetFamily.inc_ground {x} hs (by simp)) geq2).normalized_degree_sum := by
          simp_all only [Int.ofNat_eq_coe]
          rfl

lemma ground_deletion_ideal_card  (F : IdealFamily α) (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2):
  (IdealFamily.deletion F x hx ground_ge_two).ground.card = Int.ofNat  F.ground.card - 1 :=
  by
    rw [IdealFamily.deletion]
    rw [Finset.card_erase_of_mem hx]
    simp_all only [ge_iff_le, Int.ofNat_eq_coe]
    omega

lemma nds_deletion_noneuv (F : IdealFamily α) [DecidablePred F.sets] (x : α) (hx : x ∈ F.ground) (geq2: F.ground.card ≥ 2)
  [DecidablePred F.sets](hx_hyperedge : ¬F.sets (F.ground \ {x})) :
  (F.deletion x hx geq2).normalized_degree_sum = (F.toSetFamily.deletion x hx geq2).normalized_degree_sum + Int.ofNat F.ground.card - 1:=
by
  calc
    (F.deletion x hx geq2).normalized_degree_sum
        = 2 * (F.deletion x hx geq2).total_size_of_hyperedges - (F.deletion x hx geq2).number_of_hyperedges * Int.ofNat (F.deletion x hx geq2).ground.card := by
          dsimp [SetFamily.normalized_degree_sum]
      _ = 2 * ((F.toSetFamily.deletion x hx geq2).total_size_of_hyperedges + (F.ground.card - 1)) - ((F.toSetFamily.deletion x hx geq2).number_of_hyperedges + 1)* Int.ofNat (F.toSetFamily.deletion x hx geq2).ground.card:= by
        rw [ideal_deletion_noneuv_num F x hx geq2 hx_hyperedge]
        rw [ideal_deletion_noneuv_total F x hx geq2 hx_hyperedge]
        simp_all only [Int.ofNat_eq_coe, sub_right_inj, mul_eq_mul_left_iff, Nat.cast_inj]
        apply Or.inl
        rfl
      _ = 2 * (F.toSetFamily.deletion x hx geq2).total_size_of_hyperedges - (F.toSetFamily.deletion x hx geq2).number_of_hyperedges * Int.ofNat (F.toSetFamily.deletion x hx geq2).ground.card +  2* (Int.ofNat F.ground.card) - 2 - Int.ofNat (F.toSetFamily.deletion x hx geq2).ground.card:= by
        simp_all only [Int.ofNat_eq_coe, sub_right_inj, mul_eq_mul_left_iff, Nat.cast_inj]
        ring_nf
      _ = (F.toSetFamily.deletion x hx geq2).normalized_degree_sum + 2* (Int.ofNat F.ground.card) - 2 - (Int.ofNat F.ground.card - 1) := by
        --simp_all only [Int.ofNat_eq_coe]
        dsimp [SetFamily.normalized_degree_sum]
        simp [ground_deletion_ideal_card F x hx geq2]
        ring_nf
        exact ground_deletion_ideal_card F x hx geq2
      _ = (F.toSetFamily.deletion x hx geq2).normalized_degree_sum + Int.ofNat F.ground.card - 1:= by
        simp_all only [Int.ofNat_eq_coe]
        ring_nf

lemma ground_deletion_card  (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2):
  (SetFamily.deletion F x hx ground_ge_two).ground.card = Int.ofNat F.ground.card - 1 :=
  by
    rw [SetFamily.deletion]
    rw [Finset.card_erase_of_mem hx]
    simp_all only [ge_iff_le, Int.ofNat_eq_coe]
    rw [Nat.cast_sub]
    · simp_all only [Nat.cast_one]
    · simp_all only [Finset.one_le_card]
      use x


lemma ground_deletion_ideal  (F : IdealFamily α) (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2):
  (IdealFamily.deletion F x hx ground_ge_two).ground = F.ground \ {x} :=
by
  rw [IdealFamily.deletion]
  simp_all only
  simp_all only [ge_iff_le]
  ext1 a
  simp_all only [Finset.mem_erase, ne_eq, Finset.mem_sdiff, Finset.mem_singleton]
  apply Iff.intro
  · intro a_1
    simp_all only [not_false_eq_true, and_self]
  · intro a_1
    simp_all only [not_false_eq_true, and_self]

lemma ground_contraction_card  (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2):
  (SetFamily.contraction F x hx ground_ge_two).ground.card = Int.ofNat F.ground.card - 1 :=
  by
    rw [SetFamily.contraction]
    rw [Finset.card_erase_of_mem hx]
    simp_all only [ge_iff_le, Int.ofNat_eq_coe]
    rw [Nat.cast_sub]
    · simp_all only [Nat.cast_one]
    · simp_all only [Finset.one_le_card]
      use x

lemma ground_contraction  (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2):
  (SetFamily.contraction F x hx ground_ge_two).ground = F.ground \ {x} :=
by
  rw [SetFamily.contraction]
  simp_all only
  simp_all only [ge_iff_le]
  ext1 a
  simp_all only [Finset.mem_erase, ne_eq, Finset.mem_sdiff, Finset.mem_singleton]
  apply Iff.intro
  · intro a_1
    simp_all only [not_false_eq_true, and_self]
  · intro a_1
    simp_all only [not_false_eq_true, and_self]

lemma ground_contraction_ideal  (F : IdealFamily α) (x : α) (hs: F.sets {x}) (ground_ge_two: F.ground.card ≥ 2):
  (IdealFamily.contraction F x hs ground_ge_two).ground = F.ground \ {x} :=
by
  rw [IdealFamily.contraction]
  simp
  rw [SetFamily.contraction]
  simp
  rw [Finset.erase_eq]

lemma ground_contraction_ideal_card  (F : IdealFamily α) (x : α)(singleton_have: F.sets {x}) (ground_ge_two: F.ground.card ≥ 2):
  Int.ofNat (IdealFamily.contraction F x singleton_have ground_ge_two).ground.card = Int.ofNat F.ground.card - 1 :=
  by
    rw [IdealFamily.contraction]
    simp
    rw [ground_contraction_card]
    rfl

lemma nds_contraction_noneuv_lem (CT CN n: ℤ) : CT *2 - CN*(n-1) = -2 + (CT * 2  - CN*(n-1) + n * 2 - (n - 1) - (n - 1)):= by
  ring_nf

lemma nds_contraction_noneuv (F : IdealFamily α) [DecidablePred F.sets] (x : α) (hs: F.sets {x}) (geq2: F.ground.card ≥ 2)
  [DecidablePred F.sets]: --(hx_hyperedge : ¬F.sets (F.ground \ {x})) :
  (F.contraction x hs geq2).normalized_degree_sum = (F.toSetFamily.contraction x  (by exact F.toSetFamily.inc_ground {x} hs (by simp)) geq2).normalized_degree_sum:=
by
  calc
    (F.contraction x hs geq2).normalized_degree_sum
        = 2 * (F.contraction x hs geq2).total_size_of_hyperedges - (F.contraction x hs geq2).number_of_hyperedges * Int.ofNat (F.contraction x hs geq2).ground.card := by
          dsimp [SetFamily.normalized_degree_sum]
      _ = 2 * (F.contraction x hs geq2).total_size_of_hyperedges - (F.contraction x hs geq2).number_of_hyperedges * Int.ofNat (F.toSetFamily.contraction x (by exact F.toSetFamily.inc_ground {x} hs (by simp))  geq2).ground.card:= by
        rw [ground_contraction_ideal_card F x hs geq2]
        rw [←ground_contraction_card F.toSetFamily x (by exact F.toSetFamily.inc_ground {x} hs (by simp)) geq2]
        simp_all only [Int.ofNat_eq_coe]
      _ = 2 * (F.toSetFamily.contraction x (by exact F.toSetFamily.inc_ground {x} hs (by simp)) geq2).total_size_of_hyperedges - (F.toSetFamily.contraction x (by exact F.toSetFamily.inc_ground {x} hs (by simp)) geq2).number_of_hyperedges * Int.ofNat (F.toSetFamily.contraction x (by exact F.toSetFamily.inc_ground {x} hs (by simp))  geq2).ground.card:= by
        rw [set_ideal_contraction_num F x hs geq2]
        rw [set_ideal_contraction_total F x hs geq2]
      _ = (F.toSetFamily.contraction x (by exact F.toSetFamily.inc_ground {x} hs (by simp)) geq2).normalized_degree_sum := by
          simp_all only [Int.ofNat_eq_coe]
          rfl

end Frankl
