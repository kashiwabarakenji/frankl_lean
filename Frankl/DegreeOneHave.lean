import Frankl.FranklMinors
import Frankl.BasicDefinitions
import Frankl.BasicLemmas
--import LeanCopilot

--set_option maxHeartbeats 5000000

namespace Frankl

variable {α : Type} [DecidableEq α][Fintype α]


-- Proof that if {x} is not a hyperedge, then the degree of x is 1.
-- This is used below.
lemma degree_one_if_not_hyperedge {α : Type} {x : α} [DecidableEq α] [Fintype α]
  (F : IdealFamily α)[DecidablePred F.sets]  (hx: x ∈ F.ground) (h_not_hyperedge : ¬ F.sets {x}) :
  F.degree x = 1 := by
    -- Compute the degree based on the definition
    unfold IdealFamily.degree

    -- Consider all subsets that include x and are hyperedges
    set relevant_sets := Finset.filter (λ s => F.sets s ∧ x ∈ s) (Finset.powerset F.ground)

    -- Show that relevant_sets only contains F.ground
    have h_relevant_sets : relevant_sets = {F.ground} := by
      apply Finset.ext
      intros s
      dsimp [relevant_sets]
      rw [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · intro hs
        by_contra h_s_ne_ground
        have h_s_ne_ground' : s ≠ F.ground := by
          intro h
          apply h_s_ne_ground
          rw [h]
          subst h
          rw [Finset.mem_singleton]

        -- Using down_closed to derive a contradiction by making {x} a hyperedge
        -- s is not ground but F.sets s and x ∈ s. From these we can derive that {x} is a hyperedge, contradicting the assumption.
        have h_s_hyperedge : F.sets {x} := by
          apply F.down_closed
          exact hs.2.1
          exact h_s_ne_ground'
          rw [Finset.singleton_subset_iff]
          exact hs.2.2
        apply h_not_hyperedge
        exact h_s_hyperedge
      · intro hs
        rw [Finset.mem_singleton] at hs
        subst hs
        constructor
        exact Finset.Subset.refl F.ground
        constructor
        have h1 : F.sets F.ground := F.has_ground
        exact h1
        trivial
    --simp only [eq_iff_iff, iff_true]
    simp_all only [Finset.card_singleton, relevant_sets]--
    simp_all only [Int.ofNat_eq_coe, Nat.cast_one]

-- If the degree of v is 1, then there are no hyperedges other than the ground set that contain v.
-- A similar proof appears in IdealSimple.lean.
-- This lemma is used multiple times in this file.
lemma hyperedges_not_through_v {α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) [DecidablePred F.sets]  (v : α) (hv: v ∈ F.ground) (deg1: F.degree v = 1) (hasGround: F.sets F.ground) :
  ∀ s, F.sets s → s ≠ F.ground → v ∉ s := by
  intros ss hs hneq
  by_contra h
  have h_deg1 := deg1
  unfold SetFamily.degree at h_deg1
  have h_deg1_card := h_deg1
  simp at h_deg1_card
  rw [Finset.card_eq_one] at h_deg1_card
  obtain ⟨t, ht⟩ := h_deg1_card
  -- Finset.filter (fun s => F.sets s = true ∧ v ∈ s) (F.ground.powerset) = {t}

  apply hneq
  have set2inc1: F.ground ∈ (Finset.filter (fun s => F.sets s = true ∧ v ∈ s) (F.ground.powerset)) := by
    simp
    constructor
    exact hasGround
    exact hv

  have set2inc2: ss ∈ (Finset.filter (fun s => F.sets s = true ∧ v ∈ s) (F.ground.powerset)) := by
    simp
    constructor
    have ssground: ss ⊆ F.ground := F.inc_ground ss hs
    exact ssground
    constructor
    exact hs
    exact h

  have set2card: ({F.ground, ss}:Finset (Finset α)).card = 2 := by
    rw [Finset.card_insert_of_not_mem]
    simp_all only [Finset.card_singleton]
    simp_all only [ne_eq, eq_iff_iff, iff_true,Finset.mem_singleton, Finset.mem_filter]--
    subst set2inc1
    apply Aesop.BuiltinRules.not_intro
    intro a
    subst a
    simp_all only [not_true_eq_false]

  let degset := Finset.filter (fun s => F.sets s = true ∧ v ∈ s) (F.ground.powerset)
  have set2card2: ({F.ground, ss}:Finset (Finset α)) ⊆ degset := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    cases hz with
    | inl hzx => rw [hzx]; exact set2inc1
    | inr hzy => rw [hzy]; exact set2inc2

  have set2card3: 2 ≤ degset.card := by
    rw [←set2card]
    exact Finset.card_le_card set2card2

  have deg2: F.degree v >= 2 := by
    dsimp [SetFamily.degree]
    simp [set2card3]
    simp_all only [eq_iff_iff, iff_true,  degset]--

  rw [deg1] at deg2
  contradiction

lemma total_degone_card {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) [DecidablePred F.sets] (v : α) (hv: v ∈ F.ground) (deg1: F.degree v = 1) (hasGround: F.sets F.ground):--(ground_ge_two: F.ground.card ≥ 2) :
  F.total_size_of_hyperedges = (F.ground.powerset.filter (λ s => F.sets s ∧ v ∉ s )).sum Finset.card + F.ground.card := by
  rw [SetFamily.total_size_of_hyperedges]
  simp

  have union_lem: Finset.filter (λ s => F.sets s ∧ v ∉ s ) (F.ground.powerset) ∪ {F.ground} = Finset.filter (λ s => F.sets s) (F.ground.powerset) := by
    ext1 a
    rw [Finset.mem_filter, Finset.mem_powerset]
    apply Iff.intro
    intro a_1
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton] at a_1
    cases a_1 with
    | inl h => simp_all only [and_self]
    | inr h_1 =>
      rw [h_1]
      constructor
      exact Finset.Subset.refl F.ground
      exact hasGround
    intro a_1
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]--
    obtain ⟨_, right⟩ := a_1
    let assum := (hyperedges_not_through_v F v hv deg1 hasGround) a right
    simp at assum
    tauto

  have card_sum: (Finset.filter (λ s => F.sets s) (F.ground.powerset)).sum Finset.card = (Finset.filter (λ s => F.sets s ∧ v ∉ s ) (F.ground.powerset)).sum Finset.card + F.ground.card := by
    --simp_all only [ge_iff_le, Finset.disjoint_singleton_right]
    symm
    rw [← union_lem, Finset.sum_union]--
    · rw [Finset.sum_singleton]
    · simp_all only [Finset.disjoint_singleton_right, Finset.mem_filter, not_true_eq_false, and_false, not_false_eq_true]--

  simp only [Finset.mem_filter, Finset.empty_mem_powerset] at card_sum
  norm_cast


lemma ground_minus_v_ideal_sets {α : Type} [DecidableEq α] [Fintype α] (F : IdealFamily α) [DecidablePred F.sets] (v : α) (hv: v ∈ F.ground) (hv_singleton: ¬F.sets {v}) (hv_hyperedge:F.sets (F.ground \ {v})):
  ∀ s ∈ F.ground.powerset, F.sets s ↔ v ∉ s ∨ s = F.ground := by
  have degree_one: F.degree v = 1 := by
    exact degree_one_if_not_hyperedge F hv hv_singleton
  intro s hs
  simp only [Finset.mem_powerset] at hs
  apply Iff.intro
  · intro a
    let ground_assum := (hyperedges_not_through_v F.toSetFamily v hv degree_one F.has_ground) s a
    tauto
  · intro a
    cases a with
    | inl h =>
      have sinc: s ⊆ F.ground.erase v := by
        intro x hx
        simp only [Finset.mem_erase]
        apply And.intro
        · rw [ne_eq]
          intro a
          subst a
          contradiction
        · exact hs hx
      have FsetG: F.sets (F.ground.erase v) := by
        convert hv_hyperedge
        ext1 a
        simp only [Finset.mem_erase, ne_eq, Finset.mem_sdiff, Finset.mem_singleton]--
        apply Iff.intro
        · intro a_1; symm; exact a_1
        · intro a_1; symm; exact a_1
      have hsng: F.ground.erase v ≠ F.ground := by
        intro a
        simp [Finset.erase_eq_self] at a
        contradiction

      exact F.down_closed s (F.ground.erase v) FsetG hsng sinc
    | inr h_1 =>
      subst h_1
      exact F.has_ground

lemma ground_minus_v_ideal_number {α : Type} [DecidableEq α] [Fintype α] (F : IdealFamily α)[DecidablePred F.sets] (v : α) (hv: v ∈ F.ground)  (hv_hyperedge:F.sets (F.ground \ {v}))(hv_singleton:  ¬F.sets {v}):
    F.number_of_hyperedges = 2^(F.ground.card - 1) + 1 := by
  rw [SetFamily.number_of_hyperedges]

  let A := Finset.filter (λ s=> v ∉ s) F.ground.powerset
  let B : Finset (Finset α) := {F.ground}

  have h_disjoint : Disjoint A B := by
    rw [Finset.disjoint_iff_ne]
    intros s₁ hs₁ s₂ hs₂ h_eq
    rw [Finset.mem_filter] at hs₁
    have h₁ : v ∉ s₁ := hs₁.2
    rw [Finset.mem_singleton] at hs₂
    subst hs₂
    subst h_eq
    contradiction

  have h_union : A ∪ B = Finset.filter F.sets F.ground.powerset := by
    apply Finset.ext
    intro s
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_singleton]--
    constructor
    · --goal s ∈ F.ground.powerset ∧ v ∉ s ∨ s = F.ground → s ∈ F.ground.powerset ∧ F.sets s
      intro h
      cases h
      have s_in_hyperedges: F.sets s := by
        apply F.down_closed s (F.ground \ {v}) hv_hyperedge
        simp_all only [Finset.disjoint_singleton_right,not_true_eq_false,  not_false_eq_true, ne_eq, sdiff_eq_left]--
        rename_i h
        simp_all only [Finset.mem_powerset]
        obtain ⟨left, right⟩ := h
        intro x hx
        simp_all only [Finset.mem_sdiff, Finset.mem_singleton]--
        apply And.intro
        · exact left hx
        · apply Aesop.BuiltinRules.not_intro
          intro a
          subst a
          simp_all only

      constructor
      swap
      exact s_in_hyperedges
      simp_all only [B]
      simp_all only [B]
      constructor
      rename_i h
      subst h
      simp_all only [ Finset.mem_powerset, subset_refl]--
      exact F.has_ground

    · intro hs
      rw [Finset.mem_powerset] at hs ⊢
      obtain ⟨left, right⟩ := hs
      have left0: s ∈ F.ground.powerset := by
        rw [Finset.mem_powerset]
        exact left

      let tmp:= (ground_minus_v_ideal_sets F v hv hv_singleton hv_hyperedge s left0).mp right
      cases tmp
      · simp_all only [not_false_eq_true, and_self, true_or]--
      · rename_i h
        subst h
        simp_all only [or_true, B]


  have h_A_card : A.card = 2 ^ (F.ground.card - 1) := by
    dsimp [A]
    have sub_lem: ∀ s : Finset α, s ∈ (Finset.filter (fun s => v ∉ s) F.ground.powerset) ↔ s ⊆ F.ground.erase v := by
      intro s
      rw [Finset.mem_filter, Finset.mem_powerset]
      apply Iff.intro
      intro a
      obtain ⟨left, right⟩ := a
      intro x hx
      simp_all only [Finset.mem_erase, ne_eq]
      apply And.intro
      · apply Aesop.BuiltinRules.not_intro
        intro h
        subst h
        contradiction
      · exact left hx
      · intro h
        exact Finset.subset_erase.mp h

    have sub_lem2: (Finset.filter (fun s => v ∉ s) F.ground.powerset).card = (Finset.filter (fun s => s ⊆ F.ground.erase v) F.ground.powerset).card := by
      simp_all only [Finset.mem_powerset, Finset.mem_filter]
      apply Finset.card_bij (fun s _ => s)
        (by
          intro s hs
          simp only [Finset.mem_powerset, Finset.mem_filter]
          constructor
          rw [Finset.mem_filter] at hs
          rw [Finset.mem_powerset] at hs
          exact hs.1
          rw [Finset.mem_filter] at hs
          rw [Finset.mem_powerset] at hs
          rw [Finset.subset_erase]
          exact hs
        )
        (by
          intro s hs
          simp only [Finset.mem_powerset]
          intro a₂ ha₂ a
          subst a
          trivial
        )
        (by
          intro s hs
          simp_all only [Finset.mem_powerset,Finset.mem_filter]
          constructor
          simp_all only [exists_prop]
          apply And.intro
          --simp_all only [B]
          simpa using hs.2
          simp_all only [B]
        )

    rw [sub_lem2]

    have h_eq : Finset.filter (fun s => s ⊆ F.ground.erase v) F.ground.powerset = (F.ground.erase v).powerset := by
      apply Finset.ext
      intro s
      constructor
      { intro hs
        simp_all only [Finset.mem_powerset, Finset.mem_filter]
      }
      { intro hs
        rw [Finset.mem_powerset] at hs
        rw [Finset.mem_filter]
        constructor
        { rw [Finset.mem_powerset]
          exact (Finset.subset_erase.mp hs).1
        }
        { exact hs } }

    rw [h_eq]
    rw [Finset.card_powerset]
    have h_card : (F.ground.erase v).card = F.ground.card - 1 := Finset.card_erase_of_mem hv
    rw [h_card]

  have h_B_card : B.card = 1 := Finset.card_singleton F.ground
  --goal nt.ofNat (Finset.filter (fun s => F.sets s = (true = true)) F.ground.powerset).card = 2 ^ (F.ground.card - 1) + 1
  simp_all
  rw [←h_union]
  rw [Finset.card_union_of_disjoint h_disjoint]
  rw [h_A_card,h_B_card]

  simp_all only [ Nat.cast_add, Nat.cast_pow,Nat.cast_ofNat, Nat.cast_one]--

lemma powerset_bij {α : Type} [DecidableEq α][Fintype α]  (FG : Finset α) (a : α) (h : a ∈ FG) :
  (FG.powerset.filter (fun S => a ∈ S)).card = (FG.erase a).powerset.card := by
  let ss := FG.powerset.filter (fun S => a ∈ S)
  let tt := (FG.erase a).powerset
  let i := fun (S : Finset α) (_ : S ∈ ss) => S.erase a
  apply @Finset.card_bij (Finset α) (Finset α) ss tt i
    (by
      intro S hS
      simp_all only [Finset.mem_powerset, i, ss, tt]
      simp_all only [Finset.mem_filter, Finset.mem_powerset, ss]
      obtain ⟨left, _⟩ := hS
      intro x hx
      simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]--
      obtain ⟨_, right_1⟩ := hx
      exact left right_1
    )
    (λ S₁ hS₁ S₂ hS₂ h_eq => by
      simp_all only [Finset.mem_powerset, i, ss, tt, Finset.mem_filter]
      simp_all only [Finset.mem_filter, Finset.mem_powerset, ss]
      obtain ⟨_, right⟩ := hS₁
      obtain ⟨_, right_1⟩ := hS₂
      rw [← Finset.insert_erase right, h_eq]
      simp_all only [Finset.insert_erase]
    )
    (by
      intro T hT
      have goal: ∃ a, ∃ (ha : a ∈ ss), i a ha = T := by
        use insert a T
        dsimp [tt] at hT
        simp_all only [Finset.mem_powerset, i, ss, tt]
        rw [Finset.subset_erase] at hT
        have tmp_goal: insert a T ⊆ FG:= by
          obtain ⟨left, _⟩ := hT
          rw [Finset.insert_subset_iff]
          simp_all only [and_self]
        have tmp_goal2: a ∈ insert a T := by
          simp_all only [Finset.mem_insert_self]
        use Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr tmp_goal, tmp_goal2⟩
        simp only [Finset.erase_insert_eq_erase, not_false_eq_true, Finset.erase_eq_of_not_mem]--
        simp [i, hT.2]
      exact goal
    )

-- Used below:
-- For any a ∈ FG, the number of subsets containing a is 2^(n-1).
lemma count_subsets_containing_a {α : Type} [DecidableEq α][Fintype α]
  (FG : Finset α) (n : ℕ) (h_n : FG.card = n) (a : α) (ha : a ∈ FG) :
  (FG.powerset.filter (fun S => a ∈ S)).card = 2 ^ (n - 1) := by
  have h_erase_card : (FG.erase a).card = n - 1 := by
    rw [Finset.card_erase_of_mem ha]
    subst h_n
    simp_all only

  have h_powerset_eq : (FG.powerset.filter (fun S => a ∈ S)).card = (FG.erase a).powerset.card := by
    exact (powerset_bij FG a ha)

  rw [h_powerset_eq]
  rw [Finset.card_powerset]
  rw [h_erase_card]

-- Lemma to swap the order of summation.
lemma sum_card_powerset_eq_sum_subsets_containing {α : Type} [DecidableEq α] [Fintype α] {FG : Finset α} :
  FG.powerset.sum (λ s => ∑ _ ∈ s, 1) = FG.sum (λ a => (FG.powerset.filter (λ S => a ∈ S)).card) := by
  let fn (a : α) (s : Finset α): Nat := if a ∈ s then 1 else 0

  have rewrite : ∑ a ∈ FG, (Finset.filter (fun S => a ∈ S) FG.powerset).card = ∑ a ∈ FG, ∑ x ∈ (Finset.filter (fun S => a ∈ S) FG.powerset), 1 := by
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
  rw [rewrite]

  have rewrite2 : ∑ a ∈ FG, ∑ x ∈ (Finset.filter (fun S => a ∈ S) FG.powerset), 1 = ∑ a ∈ FG, ∑ x ∈ FG.powerset, fn a x := by
    have rewrite3:  ∀ a, ∑ x ∈ (Finset.filter (fun S => a ∈ S) FG.powerset), 1 = ∑ x ∈ FG.powerset, fn a x :=
      by intro a; simp [Finset.sum_congr rfl]; dsimp [fn]; simp
    congr
    ext a : 2
    simp_all

  rw [rewrite2]

  have rewrite4: ∑ s ∈ FG.powerset, ∑ a ∈ s, 1 = ∑ s ∈ FG.powerset, ∑ a ∈ FG, fn a s := by
    dsimp [fn]
    apply Finset.sum_congr rfl
    intro x a
    rw [Finset.mem_powerset] at a
    rw [Finset.sum_ite_mem]
    congr
    exact (Finset.inter_eq_right.mpr a).symm

  rw [rewrite4]
  rw [Finset.sum_comm]

-- Main theorem: FG.powerset.sum Finset.card = FG.card * 2 ^ (FG.card - 1)
theorem powerset_sum_card_eq_card_mul_pow {α : Type} [DecidableEq α][Fintype α]
  (FG : Finset α)
  (h_nonempty : FG.card ≥ 1) :
  FG.powerset.sum Finset.card = FG.card * 2 ^ (FG.card - 1) := by
  let n := FG.card
  have h_n : n ≥ 1 := h_nonempty

  have sum_eq_sum : FG.powerset.sum Finset.card = (FG.sum (fun a => (FG.powerset.filter (fun S => a ∈ S)).card)) := by
    --let scp := @sum_card_powerset_eq_sum_subsets_containing _ _ _ FG
    convert sum_card_powerset_eq_sum_subsets_containing
    simp_all
    rename_i inst_1
    simp_all only [ge_iff_le, Finset.one_le_card, n]
    exact inst_1

  have sum_contrib : FG.sum (fun a => (FG.powerset.filter (fun S => a ∈ S)).card) = FG.card * 2 ^ (n - 1) := by
    rw [Finset.sum_congr rfl (fun a ha => by rw [count_subsets_containing_a FG n rfl a ha])]
    rw [Finset.sum_const, mul_comm]
    ring

  rw [sum_eq_sum, sum_contrib]

-- Important lemma about total size when {v} is not a single hyperedge and ground - v is a hyperedge.
lemma ground_minus_v_ideal_total {α : Type} [DecidableEq α] [Fintype α] (F : IdealFamily α) [DecidablePred F.sets] (v : α) (hv: v ∈ F.ground)  (hv_hyperedge:F.sets (F.ground \ {v}))(hv_singleton:  ¬F.sets {v})(hcard0: F.ground.card ≥ 2):
  F.total_size_of_hyperedges = ((F.ground.card:Int) - 1) * (2^ (F.ground.card - 2):Int) + (F.ground.card:Int) := by
        have degree_one: F.degree v = 1 := by
            exact degree_one_if_not_hyperedge F hv hv_singleton
        have total_lem2: F.total_size_of_hyperedges = (F.ground.powerset.filter (λ s => F.sets s ∧ v ∉ s )).sum Finset.card + F.ground.card := by
          exact total_degone_card F.toSetFamily v hv degree_one F.has_ground
        rw [total_lem2]

        simp_all only [add_left_inj]
        -- Goal: (Finset.filter (fun s => F.sets s ∧ v ∉ s) F.ground.powerset).sum Finset.card = n * 2 ^ (n - 1)
        have total_lem: (Finset.filter (fun s => F.sets s ∧ v ∉ s) F.ground.powerset) = (F.ground.erase v).powerset := by
          apply Finset.ext
          intro s
          constructor
          { intro hs
            simp_all only [Finset.mem_powerset, Finset.mem_filter]--
            obtain ⟨left, right⟩ := hs
            obtain ⟨_, right⟩ := right
            intro x hx
            simp_all only [Finset.mem_erase, ne_eq]
            apply And.intro
            · apply Aesop.BuiltinRules.not_intro
              intro a
              subst a
              simp_all only
            · exact left hx
          }
          { intro hs
            rw [Finset.mem_powerset] at hs
            rw [Finset.mem_filter]
            constructor
            { rw [Finset.mem_powerset]
              exact (Finset.subset_erase.mp hs).1
            }
            {
              let hxg := (Finset.subset_erase.mp hs).1
              rw [←Finset.mem_powerset] at hxg
              let Fsets:= ground_minus_v_ideal_sets F v hv hv_singleton hv_hyperedge
              let fx := Fsets s hxg
              let hxs := (Finset.subset_erase.mp hs).2
              constructor
              exact fx.mpr (Or.inl hxs)
              exact hxs
            }
          }
        rw [total_lem]

        have formula :(F.ground.erase v).powerset.sum Finset.card = (F.ground.erase v).card * 2 ^ ((F.ground.erase v).card - 1) :=
          by
            have f_geq: (F.ground.erase v).card >= 1 := by
              rw [Finset.card_erase_of_mem hv]
              simp_all only [ge_iff_le]
              omega
            exact powerset_sum_card_eq_card_mul_pow (F.ground.erase v) f_geq
        rw [formula]
        simp_all only [Finset.card_erase_of_mem]

        have ground_eq: F.ground.card -1 -1 = F.ground.card - 2 := by
          rfl
        rw [ground_eq]
        ring_nf
        --used below.
        have hX1: Int.ofNat (F.ground.card - 1) = (F.ground.card:Int) - 1 := by
          simp_all only [Int.ofNat_eq_coe]
          omega
        simp_all only [Nat.cast_mul, Nat.cast_pow,  Int.ofNat_eq_coe]--
        ring_nf

lemma  basic_ineq (n : ℕ) (h : 0 ≤ n) : 2^n ≥ n + 1 := by
  induction n with
  | zero =>
    -- Base case: n = 0 does not apply because we assume n ≥ 1
    by_contra
    norm_num
    simp_all only [nonpos_iff_eq_zero, one_ne_zero]
    simp_all only [pow_zero, zero_add,  le_refl, not_true_eq_false]--

  | succ k ih =>
    -- Inductive step: show 2^(k+1) ≥ k+2
    have k_geq_0 : k ≥ 0 := by exact Nat.zero_le k

    rw [pow_succ 2 k]

    by_cases h1: k = 0
    case pos =>
      rw [h1]
      simp_all only [Nat.one_pow]
      omega
    case neg =>
      have hh1: k ≥ 1 := by
        simp_all only [ge_iff_le]
        omega
      -- 2^(k+1) = 2 * 2^k
      have : 2 * 2^k ≥ 2 * (k + 1) := mul_le_mul_of_nonneg_left (ih (Nat.zero_le k)) (by norm_num)

      -- 2 * (k + 1) = 2k + 2 ≥ k + 2 for k ≥ 0
      have : 2 * (k + 1) ≥ k + 2 := by
        calc
          2 * (k + 1) = k + 1 + k + 1 := by ring
          _ = (k + k) + (1 + 1) := by simp_all only [le_add_iff_nonneg_left]; omega
          _ ≥ k + 2 := by simp_all only [le_add_iff_nonneg_left]; omega

      simp_all only [true_implies]
      omega


lemma X_lemma {n:Int}{X:Nat}(hX: X = 2^(n-2).toNat)(assum: n <= 2 * X): 2*((n-1)*X+n) <= (2*X+1)*n :=
by
    have left_side: 2 * ((n - 1) * X + n) = 2 * (n - 1) * X + 2 * n := by ring
    have right_side: (2 * X + 1) * n = 2 * n * X + n := by ring
    rw [left_side, right_side]
    simp

    ring_nf
    norm_cast
    subst hX
    omega

lemma lem_nat {n:Int} (h: n >= 1): ((n-1).toNat) + 1 = n.toNat := by --↑
      simp_all only [ge_iff_le, Int.pred_toNat]
      cases n
      · simp_all only [Int.ofNat_eq_coe, Nat.one_le_cast, Int.toNat_ofNat, Nat.sub_add_cancel]--
      · norm_cast

lemma transform_inequality {n : Int} (h : 2 ≤ n) :
    2 * ((n - 1) * 2 ^ ((n - 2).toNat) + n) ≤ ((2 ^ (n - 1).toNat + 1) * n) := by
  -- Introduce X = 2^(n-2)
  let X := 2^(n-2).toNat
  have hX: X = 2^(n-2).toNat := by rfl
  have oneshift: (-2+n).toNat.succ = (n - 1).toNat := by
    let n' := (n - 2).toNat
    have hn : n = n' + 2 := by
      simp_all only [sub_nonneg, Int.toNat_of_nonneg, sub_add_cancel, n']
    rw [hn]
    simp
    norm_cast
  have hX2: 2 * X = 2^(n-1).toNat := by
    rw [hX]
    ring_nf
    simp_all
    rw [←Nat.pow_succ]
    have succ_lem:(-2 + n).toNat.succ = (-2 + n ).toNat + 1:= by
      simp
    rw [succ_lem]
    rw [oneshift]

    have succ_lem2: (n.toNat - 1) = (n-1).toNat := by
      simp_all only [Int.pred_toNat]

    have :(-1+n) = (n-1) := by
      ring_nf

    rw [←this] at succ_lem2

    rw [succ_lem2]
  have geq0 : n >= 0 := by
    linarith

  have geq1 : n ≥ 1 := by
      linarith

  have geq1' : (n - 1).toNat ≥ 0 := by
      simp_all only [ zero_le]

  have geq1n: n.toNat >= 1:= by
    simp_all only [ Int.pred_toNat]
    omega

  have succ_lem2: (n.toNat - 1) = (n-1).toNat := by
      simp_all only [ Int.pred_toNat]

  let arg := basic_ineq (n-1).toNat (geq1')
  rw [ge_iff_le] at arg

  have result_ineq : n ≤ 2 * X := by
    norm_cast
    rw [hX2]

    rw [lem_nat geq1] at arg

    norm_cast
    have goal0:n ≤ Int.ofNat (2 ^ (n - 1).toNat) := by
      simp_all only [Int.ofNat_eq_coe]
      have eq_nat: n.toNat = n := by
        rw [Int.toNat_of_nonneg geq0]
      rw [←eq_nat]
      norm_cast
      convert arg
      rw [←eq_nat]
      norm_cast

    exact goal0

  let result := X_lemma hX result_ineq
  norm_cast at result
  rw [hX] at result
  clear result_ineq oneshift succ_lem2 geq0 geq1 geq1' geq1n
  have sub1: 2*2 ^ (n - 2).toNat = 2^(n-1).toNat := by
    rw [←hX]
    rw [hX2]
  simp_all only [ Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]--

lemma case_degone_haveUV (F : IdealFamily α) [DecidablePred F.sets] (v : α) (v_in_ground: v ∈ F.ground) (geq2: F.ground.card ≥ 2)(singleton_hyperedge_none: ¬F.sets {v})(h_uv_have : (F.sets (F.ground \ {v})))
  --(ih : ∀ (F' : IdealFamily α)[DecidablePred F'.sets], F'.ground.card < F.ground.card → F'.normalized_degree_sum ≤ 0)
  : F.normalized_degree_sum ≤ 0 :=
by
  have total := ground_minus_v_ideal_total F v v_in_ground h_uv_have singleton_hyperedge_none geq2
  have number := ground_minus_v_ideal_number F v v_in_ground h_uv_have singleton_hyperedge_none
  dsimp [SetFamily.normalized_degree_sum]
  rw [total, number]
  -- Using `simp_all` to simplify. Without it, an error occurs.
  simp_all

  -- This lemma shows that for n ≥ 1, 2^n ≥ n + 1.
  have basic_ineq (n : Nat) (h : 1 ≤ n) : 2^n ≥ n + 1 := by
    induction n with
    | zero =>
      -- Base case: n = 0 does not apply here.
      by_contra _
      simp_all only [nonpos_iff_eq_zero]
      simp_all only [tsub_zero, one_ne_zero]
    | succ k ih =>
      rw [pow_succ 2 k]
      simp_all
      by_cases h1: k = 0
      · -- If k = 0
        rw [h1]
        simp only [pow_zero, mul_one]
        norm_num
      · -- If k ≥ 1
        have k_ge_1 : k ≥ 1 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h1)

        -- Apply the induction hypothesis
        have ih_applied := ih k_ge_1
        apply ge_iff_le.mp

        calc
          2 ^ k * 2 = 2 * 2^k := by ring
          _ ≥ 2 * (k + 1) := mul_le_mul_left' ih_applied 2
          _ = k + k + 2 := by ring
          _ ≥ k + 1 + 2 := by
            apply add_le_add_right
            simp_all only [add_le_add_iff_left]
          _ ≥ (k + 1) + 1 := by
            simp only [add_le_add_iff_left, Nat.one_le_ofNat]

  convert transform_inequality (Nat.cast_le.mpr geq2)
  simp_all only [ge_iff_le]
  norm_cast
  simp_all only [ Int.pred_toNat, Int.toNat_ofNat]--

end Frankl
