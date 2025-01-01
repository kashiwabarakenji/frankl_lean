import Mathlib.Data.Finset.Basic
--import Mathlib.Data.Finset.Card
--import Mathlib.Algebra.BigOperators.Group.Finset
--import Init.Data.Int.Lemmas
--import Init.Data.Nat.Lemmas
import Frankl.FranklMinors
import Frankl.BasicDefinitions
import Frankl.BasicLemmas
import Frankl.FamilyLemma
import Frankl.DegreeOneHave
import LeanCopilot

--set_option maxHeartbeats 1000000

namespace Frankl

variable {α : Type} [DecidableEq α][Fintype α]

lemma number_have (F: IdealFamily α) [DecidablePred F.sets] (v:α) (geq2: F.ground.card ≥ 2) (vin: v ∈ F.ground)(hs: F.sets {v})
  [DecidablePred (F.toSetFamily.deletion v vin geq2).sets] [DecidablePred (F.contraction v hs geq2).sets]:
F.number_of_hyperedges = (F.toSetFamily.deletion v vin geq2).number_of_hyperedges + (F.contraction v hs geq2).number_of_hyperedges :=
by
  dsimp [SetFamily.number_of_hyperedges]
  rw [family_union_card F.toSetFamily v]
  rw [add_comm]
  have left_hand:  (Finset.filter (fun s => F.sets s ∧ v ∉ s) F.ground.powerset).card = (Finset.filter (fun s => (F.toSetFamily.deletion v vin geq2).sets s) (F.deletion v vin geq2).ground.powerset).card := by
    rw [ground_deletion_ideal F v vin geq2]
    dsimp [SetFamily.deletion]
    rw [number_ground F.toSetFamily v]
    congr

  have right_hand: (Finset.filter (fun s => F.sets s ∧ v ∈ s) F.ground.powerset).card = (Finset.filter (fun s => (F.contraction v hs geq2).sets s) (F.contraction v hs geq2).ground.powerset).card := by
    rw [ground_contraction_ideal F v  hs geq2]
    dsimp [IdealFamily.contraction]
    dsimp [SetFamily.contraction]
    let tmp := contraction_eq_card F.toSetFamily v
    simp at tmp
    rw [←Finset.erase_eq]
    rw [tmp]
    congr

  rw [left_hand]
  rw [right_hand]
  simp_all only [Nat.cast_add]
  rfl

lemma sumbij (F : SetFamily α) [DecidablePred F.sets] (x : α)  :
  let domain00 := (Finset.powerset F.ground).filter (λ s => F.sets s ∧ x ∈ s)
  let range00  := (Finset.powerset (F.ground.erase x)).filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x)
  domain00.sum Finset.card = range00.sum Finset.card + range00.card :=
by
  let domain0 := (Finset.powerset F.ground).filter (λ s => F.sets s ∧ x ∈ s)
  let range0  := (Finset.powerset (F.ground.erase x)).filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x)

  -- Define f and g for sum_bij
  let f := λ (s : Finset α) => s.card
  let g := λ (s : Finset α) => s.card + 1

  -- Define the function i : domain0 -> range0
  let i := λ (s : Finset α) (_ : s ∈ domain0) => s.erase x

  /- If you already have a lemma `contraction_bijective` that ensures:
       (1) i lands in range0,
       (2) i is injective,
       (3) i is surjective onto range0,
       (4) f s = g (i s _)
     then you can replace the next 4 subproofs by referencing that lemma. -/

  have h_mem : ∀ s (hs : s ∈ domain0), i s hs ∈ range0 := by
    intros s hs
    simp_all only [ i,  range0]--
    simp_all only [Finset.mem_filter, Finset.mem_powerset, domain0]
    obtain ⟨left, right⟩ := hs
    obtain ⟨left_1, right⟩ := right
    apply And.intro
    · intro y hy
      simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]--
      obtain ⟨_, right_1⟩ := hy
      exact left right_1
    · apply Exists.intro
      · apply And.intro
        on_goal 2 => apply And.intro
        on_goal 3 => {rfl
        }
        · simp_all only
        · simp_all only

  have h_inj : ∀ s₁ (hs₁ : s₁ ∈ domain0) s₂ (hs₂ : s₂ ∈ domain0),
    i s₁ hs₁ = i s₂ hs₂ → s₁ = s₂ := by
      --let tmp := (contraction_bijective F x).injective
      --simp at tmp
      intros s₁ hs₁ s₂ hs₂ h_eq
      dsimp [domain0] at hs₁ hs₂
      simp only [Finset.mem_filter, Finset.mem_powerset] at hs₁ hs₂
      -- From hs₁, hs₂ we know x ∈ s₁, x ∈ s₂
      -- heq: s₁.erase x = s₂.erase x
      exact (erase_inj_of_mem hs₁.2.2 hs₂.2.2).mp h_eq

  have h_surj : ∀ b ∈ range0, ∃ a, ∃(ha:a ∈ domain0), i a ha = b := by
    intros b hb
    /-
      By the definition of `range0`, an element `b ∈ range0` means:
        b ⊆ (F.ground.erase x)
        and there exists some `H` such that F.sets H, x ∈ H, and b = H.erase x.
    -/
    simp only [Finset.mem_filter, Finset.mem_powerset,range0] at hb
    obtain ⟨H, hH_sets, hH_x, hH_eq⟩ := hb.2
    -- Here, b = H.erase x.

    /- We claim that `a = H` is our desired preimage. -/
    have Hd : H ∈ domain0 := by
      dsimp [domain0]
      simp only [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · -- Show `H ⊆ F.ground`
        -- From the definition of `domain0`, we know F.sets H and x ∈ H.
        -- We need to show H ⊆ F.ground.
        exact F.inc_ground H hH_sets
        -- H = (H.erase x) ∪ {x}, both subsets reflect that H is subset of F.ground
      · -- Show `x ∈ H`
        exact ⟨hH_sets,hH_x⟩
    use H ,Hd
    subst hH_eq
    simp_all only [  range0]

  have h_val : ∀ s (hs : s ∈ domain0), f s = g (i s hs) := by
    -- here we show: card(s) = (card (s.erase x)) + 1
    intros s hs
    have hx_in_s : x ∈ s := by
      simp_all only [Finset.mem_filter, domain0]
    simp_all only [ Finset.card_erase_add_one, i,  g]--

  /- 1) Use sum_bij to get the sum equality *without* rewriting yet -/
  have eq_sum : ∑ s in domain0, f s = ∑ s in range0, g s :=
    @Finset.sum_bij _ _ _ _ domain0 range0 f g i (λ s hs => h_mem s hs) (λ s₁ hs₁ s₂ hs₂ h_eq => h_inj s₁ hs₁ s₂ hs₂ h_eq) (λ b hb => h_surj b hb) (λ s hs => h_val s hs)

  /- 2) Now rewrite the RHS from ∑ s in range0, (s.card + 1)
         into ∑ s in range0, s.card + range0.card -/
  simp
  dsimp [domain0,range0,f,g] at eq_sum
  rw [eq_sum]
  rw [Finset.sum_add_distrib]
  simp_all [domain0, i, range0, f, g]

-- Main lemma: contraction_total_size
lemma contraction_total_size (F : SetFamily α) [DecidablePred F.sets] (x : α)
  (hx : x ∈ F.ground) (geq2 : F.ground.card ≥ 2)
  [DecidablePred (F.contraction x hx geq2).sets] :
  (F.contraction x hx geq2).total_size_of_hyperedges =
    ((Finset.powerset F.ground).filter (λ s => F.sets s ∧ x ∈ s)).sum (λ s => Int.ofNat (Finset.card s) - 1) :=
by
  -- Step 1: Use the sumbij lemma
  have sumbij_result := sumbij F x

  -- Step 2: Expand total_size_of_hyperedges for the contraction
  rw [SetFamily.total_size_of_hyperedges]
  simp only [SetFamily.contraction, SetFamily.total_size_of_hyperedges]

  simp at sumbij_result
  simp

  have eq_card: (Finset.filter (fun s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (F.ground.erase x).powerset).card = (Finset.filter (fun s => F.sets s ∧ x ∈ s) F.ground.powerset).card :=
  by
    let tmp:= contraction_eq_card F x
    simp at tmp
    exact tmp.symm

  have nonneg: ∑ x ∈ Finset.filter (fun s => F.sets s ∧ x ∈ s) F.ground.powerset, (Int.ofNat x.card -1) >= 0 :=
  by
    have h_nonneg : ∀ s ∈ Finset.filter (λ s => F.sets s ∧ x ∈ s) F.ground.powerset,
    0 ≤ (Int.ofNat s.card - 1) := by
      intro s hs
      simp only [Finset.mem_filter] at hs
      have h_card : s.card ≥ 1 := by
        simp_all only [Finset.one_le_card]
        obtain ⟨_, right⟩ := hs
        obtain ⟨_, right⟩ := right
        exact ⟨x, right⟩
      -- To show Int.ofNat s.card - 1 ≥ 0
      simp_all only [Int.ofNat_eq_coe, sub_nonneg, Nat.one_le_cast]--

    exact Finset.sum_nonneg h_nonneg

  --use implicitly
  have nonneg2: ∑ x ∈ Finset.filter (fun s => F.sets s ∧ x ∈ s) F.ground.powerset, ↑x.card >= (Finset.filter (fun s => F.sets s ∧ x ∈ s) F.ground.powerset).card :=
  by
    simp only [Finset.sum_sub_distrib] at nonneg
    simp at nonneg
    linarith

  have sumbij_result_int_combined :
  ∑ x ∈ Finset.filter (λ s => F.sets s ∧ x ∈ s) F.ground.powerset, (↑x.card : Int) -
    (Finset.filter (λ s => F.sets s ∧ x ∈ s) F.ground.powerset).card =
  ∑ x ∈ Finset.filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (F.ground.erase x).powerset, (↑x.card : Int) :=
  by
  -- First, simplify the left-hand side to use sumbij_result_int
    have sumbij_result_int : ∑ x ∈ Finset.filter (λ s => F.sets s ∧ x ∈ s) F.ground.powerset, (↑x.card) -
          ↑(Finset.filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (F.ground.erase x).powerset).card =
        ∑ x ∈ Finset.filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (F.ground.erase x).powerset, (↑x.card) :=
      by
        simp_all only [add_sub_cancel_right]
        simp_all only [add_tsub_cancel_right]
    rw [eq_card] at sumbij_result_int

    -- Apply congr_arg to lift sumbij_result_int to the final form
    exact congr_arg (λ z => (↑z : Int)) (by exact_mod_cast sumbij_result_int)

  rw [sumbij_result_int_combined]
  congr

--essentially the same as the previous lemma, but with a different filter
lemma sum_of_size_eq_degree_plus_contraction_sum (F : SetFamily α) [DecidablePred F.sets] (x : α) (hx : x ∈ F.ground) (geq2 : F.ground.card ≥ 2)
  [DecidablePred (F.contraction x hx geq2).sets]:
 (Finset.filter (λ s => F.sets s ∧ x ∈ s) (Finset.powerset F.ground)).sum Finset.card = F.degree x + (Finset.filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (Finset.powerset (F.ground.erase x))).sum Finset.card :=
by
  let previous := contraction_total_size F x hx geq2
  dsimp [SetFamily.total_size_of_hyperedges] at previous
  dsimp [SetFamily.contraction] at previous
  simp at previous
  simp_all only [Int.ofNat_eq_coe, Nat.cast_sum]
  ring_nf at previous
  symm
  have :∑ x ∈ Finset.filter (fun s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (F.ground.erase x).powerset, ↑x.card =
  ∑ x ∈ Finset.filter (fun s => F.sets s ∧ x ∈ s) F.ground.powerset, ↑x.card - F.degree x :=
  by
    convert previous
  linarith

lemma total_have{α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) (x : α) (hx : x ∈ F.ground) (geq2: F.ground.card ≥ 2)
  [DecidablePred F.sets] (singleton_have :F.sets {x}) :
  haveI : DecidablePred (F.deletion x hx geq2).sets := by
    dsimp[SetFamily.deletion]
    simp_all only [ge_iff_le]
    infer_instance
  haveI : DecidablePred (F.contraction x hx geq2).sets := by
    dsimp [SetFamily.contraction]
    infer_instance
  F.total_size_of_hyperedges = (F.deletion x hx geq2).total_size_of_hyperedges + (F.contraction x hx geq2).total_size_of_hyperedges +  F.degree x:=
by
  haveI : DecidablePred (F.contraction x hx geq2).sets := by
    dsimp [SetFamily.contraction]
    infer_instance
  haveI : DecidablePred (F.deletion x hx geq2).sets := by
    dsimp [SetFamily.deletion]
    infer_instance

  have sub1 : {F with sets := λ s => F.sets s ∧ x ∈ s, inc_ground := λ s hs => F.inc_ground s (hs.1) }.total_size_of_hyperedges  =
    (((Finset.filter (λ s => F.sets s ∧ x ∈ s) (Finset.powerset F.ground)).sum (λ s => Int.ofNat (Finset.card s))):Int) := by
      dsimp [SetFamily.total_size_of_hyperedges]
      simp_all only [ge_iff_le, Nat.cast_sum]

  have sub2: { F with sets := λ s => F.sets s ∧ x ∉ s, inc_ground := λ s hs => F.inc_ground s (hs.1) }.total_size_of_hyperedges  =
  (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum (λ s => Int.ofNat (Finset.card s)) := by
    dsimp [SetFamily.total_size_of_hyperedges]
    simp_all only [ge_iff_le, Nat.cast_sum]


  have sub3: (Finset.filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (Finset.powerset (F.ground.erase x))).sum  (λ s => Int.ofNat (Finset.card s)) =
     (F.contraction x hx geq2).total_size_of_hyperedges  := by
    dsimp [SetFamily.total_size_of_hyperedges]
    dsimp [SetFamily.contraction]
    simp
    congr

  haveI : DecidablePred (F.deletion x hx geq2).sets := by
    dsimp [SetFamily.deletion]
    infer_instance
  have sub4: (Finset.filter (λ s => F.sets s ∧ x  ∉ s) (Finset.powerset F.ground)).sum (λ s => Int.ofNat (Finset.card s))= (F.deletion x hx geq2).total_size_of_hyperedges := by
    dsimp [SetFamily.total_size_of_hyperedges]
    dsimp [SetFamily.deletion]
    simp
    --goal ∑ s ∈ Finset.filter (fun s => F.sets s ∧ x ∉ s) F.ground.powerset, ↑s.card = ∑ x ∈ Finset.filter (fun s => F.sets s ∧ x ∉ s) (F.ground.erase x).powerset, ↑x.card
    let tmp:= filter_sum_eq_int F x
    simp at tmp
    rw [tmp]
    congr

  calc
    F.total_size_of_hyperedges
        = { F with sets := λ s => F.sets s ∧ x ∈ s, inc_ground := λ s hs => F.inc_ground s (hs.1) }.total_size_of_hyperedges +
          { F with sets := λ s => F.sets s ∧ x ∉ s, inc_ground := λ s hs => F.inc_ground s (hs.1) }.total_size_of_hyperedges := by
            rw [←(sum_partition_by_v F x)]
      _  = (Finset.filter (λ s => F.sets s ∧ x ∈ s) (Finset.powerset F.ground)).sum Finset.card +
          (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by
            rw [sub1]
            rw [sub2]
            simp_all only [Int.ofNat_eq_coe, Nat.cast_sum]
      _  = F.degree x + (Finset.filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (Finset.powerset (F.ground.erase x))).sum Finset.card +
          (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by

            rw [sum_of_size_eq_degree_plus_contraction_sum F x]
      _  = F.degree x + (F.contraction x hx geq2).total_size_of_hyperedges
              + (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by
            rw [←sub3]
            simp_all only [Int.ofNat_eq_coe, Nat.cast_sum]
      _  = F.degree x +  (F.contraction x hx geq2).total_size_of_hyperedges  +
          (F.deletion x hx geq2).total_size_of_hyperedges  := by
            rw [←sub4]
            simp_all only [Int.ofNat_eq_coe, Nat.cast_sum]
      _  = (F.deletion x hx geq2).total_size_of_hyperedges  +
          (F.contraction x hx geq2).total_size_of_hyperedges  + F.degree x := by
            ring_nf
      _  = (F.deletion x hx geq2).total_size_of_hyperedges + (F.contraction x hx geq2).total_size_of_hyperedges +  F.degree x := by
            ring_nf

  congr

lemma eqn (Dtotal Ctotal Dnum Cnum degree ground_card : ℤ):
    Dtotal*2 + Ctotal * 2 + degree * 2 + (-(Dnum * ground_card) - Cnum * ground_card )
    = Dtotal * 2 + (Ctotal * 2 - Dnum * ground_card) + (- Cnum - ground_card * Cnum) + Cnum + degree * 2 :=
by
  ring_nf

theorem nds_set_minors (F : IdealFamily α) [DecidablePred F.sets] (x : α) (hx : x ∈ F.ground) (geq2: F.ground.card ≥ 2)
 (hs : F.sets {x}):
  F.toSetFamily.normalized_degree_sum =
  (F.toSetFamily.deletion x hx geq2).normalized_degree_sum +
  (F.toSetFamily.contraction x hx geq2).normalized_degree_sum
  +2*(F.degree x) - F.number_of_hyperedges :=
by
  dsimp [SetFamily.normalized_degree_sum]
  haveI : DecidablePred (F.contraction x hs geq2).sets := by
    dsimp [IdealFamily.contraction]
    infer_instance
  have number := number_have F x geq2 hx hs
  have total := total_have F.toSetFamily x hx geq2 hs
  rw [total]
  rw [number]

  rw [←number_eq_card]
  rw [ground_contraction_card]
  rw [ground_deletion_card F.toSetFamily x hx geq2]
  --rw [set_ideal_contraction_num]
  clear total number
  ring_nf
  have eqn_lemma := eqn
    (F.toSetFamily.deletion x hx geq2).total_size_of_hyperedges
    (F.toSetFamily.contraction x hx geq2).total_size_of_hyperedges
    (F.toSetFamily.deletion x hx geq2).number_of_hyperedges
    (F.toSetFamily.contraction x hx geq2).number_of_hyperedges
    (F.degree x)
    (F.ground.card:Int)
  --rw [ideal_deletion_haveuv_total F x hx geq2 hx_hyperedge]
  --rw [ideal_deletion_haveuv_num F x hx geq2 hx_hyperedge]
  convert eqn_lemma

end Frankl
