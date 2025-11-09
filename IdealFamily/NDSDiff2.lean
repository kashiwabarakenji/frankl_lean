import IdealFamily.Core
import IdealFamily.TraceGuarded
import IdealFamily.Contraction
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.Basic

namespace IdealFamily
namespace Ideal

open Finset
open scoped BigOperators

noncomputable section

variable {α : Type*} [DecidableEq α]
variable (F : Ideal α) [DecidablePred F.sets]
variable (v : α)

-- Short alias; use full forms like `(F.toSetFamily).delCarrier v` explicitly elsewhere
local notation "SF" => F.toSetFamily
local notation "n"  => F.ground.card

/-- Integer-weighted size sum over a family. -/
private def sumZ (X : Finset (Finset α)) : ℤ := ∑ s ∈ X, (s.card : ℤ)

/-! ############################  Set-theoretic decompositions  ############################ -/

/-- Carrier decomposition: `carrier = del ∪ S`. -/
lemma carrier_eq_del_union_S :
  (F.toSetFamily).carrier = ((F.toSetFamily).delCarrier v) ∪ ((F.toSetFamily).S v) := by
  classical
  apply Finset.ext
  intro t
  constructor
  · intro ht
    by_cases hv : v ∈ t
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨ht, hv⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨ht, hv⟩))
  · intro ht
    cases Finset.mem_union.mp ht with
    | inl hA => exact (Finset.mem_filter.mp hA).1
    | inr hB => exact (Finset.mem_filter.mp hB).1

/-- `del` and `S` are disjoint. -/
lemma disjoint_del_S : Disjoint ((F.toSetFamily).delCarrier v) ((F.toSetFamily).S v) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro t htA htB
  have hv_not : v ∉ t := (Finset.mem_filter.mp htA).2
  have hv_yes : v ∈ t := (Finset.mem_filter.mp htB).2
  exact (hv_not hv_yes).elim

/-- Trace carrier: `carrier(trace) = del ∪ contr`. -/
lemma trace_carrier_eq_del_union_contr' (hne : (F.ground.erase v).Nonempty) :
  (F.traceIdeal v hne).toSetFamily.carrier = ((F.toSetFamily).delCarrier v) ∪ ((F.toSetFamily).contrCarrier v) :=
  trace_carrier_eq_del_union_contr (F := F) (v := v) hne

/-- Edge count split on `F`. -/
lemma numEdges_split_F :
  (F.toSetFamily).numEdges
    = (((F.toSetFamily).delCarrier v).card : ℤ) + (((F.toSetFamily).S v).card : ℤ) := by
  classical
  unfold SetFamily.numEdges
  change ((F.toSetFamily).carrier.card : ℤ)
          = (((F.toSetFamily).delCarrier v).card : ℤ) + (((F.toSetFamily).S v).card : ℤ)
  have hAB : (F.toSetFamily).carrier = (F.toSetFamily).delCarrier v ∪ (F.toSetFamily).S v := carrier_eq_del_union_S (F := F) (v := v)
  have hdis : Disjoint ((F.toSetFamily).delCarrier v) ((F.toSetFamily).S v) := disjoint_del_S (F := F) (v := v)
  have : ((F.toSetFamily).carrier.card : ℤ) = (((F.toSetFamily).delCarrier v ∪ (F.toSetFamily).S v).card : ℤ) := by exact congrArg Nat.cast (congrArg card hAB)--sorry--cases hAB; rfl
  have hcu : ((F.toSetFamily).delCarrier v ∪ (F.toSetFamily).S v).card
              = ((F.toSetFamily).delCarrier v).card + ((F.toSetFamily).S v).card := by exact card_union_of_disjoint hdis--Finset.card_disjoint_union hdis
  exact Eq.trans this (congrArg (fun k : ℕ => (k : ℤ)) hcu)

/-- Total size split on `trace(F)` as `del ⊎ (contr \ del)`. -/
lemma totalSize_split_trace (hne : (F.ground.erase v).Nonempty) :
  (F.traceIdeal v hne).toSetFamily.totalSize
    = sumZ ((F.toSetFamily).delCarrier v)
      + sumZ ((F.toSetFamily).contrCarrier v \ (F.toSetFamily).delCarrier v) := by
  classical
  have hTrace : (F.traceIdeal v hne).toSetFamily.carrier = (F.toSetFamily).delCarrier v ∪ (F.toSetFamily).contrCarrier v :=
    trace_carrier_eq_del_union_contr' (F := F) (v := v) hne
  have hRewr : (F.toSetFamily).delCarrier v ∪ (F.toSetFamily).contrCarrier v
                = (F.toSetFamily).delCarrier v ∪ ((F.toSetFamily).contrCarrier v \ (F.toSetFamily).delCarrier v) := by
    exact Eq.symm union_sdiff_self_eq_union--union_del_contr_eq_union_del_contrSdiff (F := F) (v := v)
  have hdis : Disjoint ((F.toSetFamily).delCarrier v) ((F.toSetFamily).contrCarrier v \ (F.toSetFamily).delCarrier v) := by
   exact disjoint_sdiff-- disjoint_del_contr_sdiff (F := F) (v := v)
  simp only [SetFamily.totalSize, SetFamily.totalSizeNat, sumZ]
  rw [hTrace, hRewr, Finset.sum_union hdis]
  simp only [Nat.cast_add, Nat.cast_sum]

/-- Edge count on `trace(F)`: `|del| + |contr| − |contr ∩ del|`. -/
lemma numEdges_split_trace (hne : (F.ground.erase v).Nonempty) :
  (F.traceIdeal v hne).toSetFamily.numEdges
    = (((F.toSetFamily).delCarrier v).card : ℤ)
      + (((F.toSetFamily).contrCarrier v).card : ℤ)
      - ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v).card := by
  classical
  unfold SetFamily.numEdges
  change (((F.traceIdeal v hne).toSetFamily.carrier).card : ℤ)
        = (((F.toSetFamily).delCarrier v).card : ℤ)
          + (((F.toSetFamily).contrCarrier v).card : ℤ)
          - ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v).card
  have hTrace : (F.traceIdeal v hne).toSetFamily.carrier = (F.toSetFamily).delCarrier v ∪ (F.toSetFamily).contrCarrier v :=
    trace_carrier_eq_del_union_contr' (F := F) (v := v) hne
  have hRewr : (F.toSetFamily).delCarrier v ∪ (F.toSetFamily).contrCarrier v
                = (F.toSetFamily).delCarrier v ∪ ((F.toSetFamily).contrCarrier v \ (F.toSetFamily).delCarrier v) := by
    exact Eq.symm union_sdiff_self_eq_union
  have hdis : Disjoint ((F.toSetFamily).delCarrier v) ((F.toSetFamily).contrCarrier v \ (F.toSetFamily).delCarrier v) := by
    exact disjoint_sdiff
  have hsubset : ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v) ⊆ (F.toSetFamily).contrCarrier v := by
    intro t ht; exact (Finset.mem_inter.mp ht).1
  have h1 : (((F.traceIdeal v hne).toSetFamily.carrier).card : ℤ)
            = (((F.toSetFamily).delCarrier v ∪ ((F.toSetFamily).contrCarrier v \ (F.toSetFamily).delCarrier v)).card : ℤ) := by
    simp
    dsimp [Ideal.traceIdeal]
    exact congrArg card hTrace

  have h2 : (((F.toSetFamily).delCarrier v ∪ ((F.toSetFamily).contrCarrier v \ (F.toSetFamily).delCarrier v)).card : ℤ)
            = ((((F.toSetFamily).delCarrier v).card + ((F.toSetFamily).contrCarrier v \ (F.toSetFamily).delCarrier v).card) : ℤ) := by
    apply congrArg (fun k : ℕ => (k : ℤ)) --(Finset.card_disjoint_union hdis)
    exact card_union_of_disjoint hdis
  have h3 : (((F.toSetFamily).contrCarrier v \ (F.toSetFamily).delCarrier v).card : ℤ)
            = (((F.toSetFamily).contrCarrier v).card : ℤ) - ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v).card := by
    have hNat :
    ((F.toSetFamily).contrCarrier v \ (F.toSetFamily).delCarrier v).card
      = ((F.toSetFamily).contrCarrier v).card
        - ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v).card := by
      classical
      simpa [Finset.inter_comm] using
        (Finset.card_sdiff :
          #(((F.toSetFamily).contrCarrier v) \ ((F.toSetFamily).delCarrier v))
            = #((F.toSetFamily).contrCarrier v)
              - #(((F.toSetFamily).delCarrier v) ∩ ((F.toSetFamily).contrCarrier v)))

    have hCast := congrArg (fun k : ℕ => (k : ℤ)) hNat
    have hLe :
        (F.contrCarrier v ∩ F.delCarrier v).card ≤ (F.contrCarrier v).card :=
      Finset.card_le_card hsubset
    simp only [hCast, Nat.cast_sub hLe]
  calc
    (((F.traceIdeal v hne).toSetFamily.carrier).card : ℤ)
        = (((F.toSetFamily).delCarrier v ∪ ((F.toSetFamily).contrCarrier v \ (F.toSetFamily).delCarrier v)).card : ℤ) := h1
    _   = ((((F.toSetFamily).delCarrier v).card + ((F.toSetFamily).contrCarrier v \ (F.toSetFamily).delCarrier v).card) : ℤ) := h2
    _   = (((F.toSetFamily).delCarrier v).card : ℤ) + (((F.toSetFamily).contrCarrier v \ (F.toSetFamily).delCarrier v).card : ℤ) := by
      exact Nat.cast_add _ _
    _   = (((F.toSetFamily).delCarrier v).card : ℤ)
          + (((F.toSetFamily).contrCarrier v).card : ℤ)
          - ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v).card := by
            rw [h3]
            ring

/-! ############################  Algebraic assembly lemmas  ############################ -/

/-- Contraction numerics:  `|contr| = |S|` and `Σ contr = Σ S − |S|`. -/
lemma contr_count_and_sum :
  ((((F.toSetFamily).contrCarrier v).card : ℤ) = (((F.toSetFamily).S v).card : ℤ)) ∧
  ((∑ t ∈ ((F.toSetFamily).contrCarrier v), (t.card : ℤ)) = ∑ s ∈ ((F.toSetFamily).S v), ((s.card : ℤ) - 1)) := by
  classical
  have hCard := IdealFamily.SetFamily.card_contr_eq_cardS  F.toSetFamily (v := v)
  have hSum  := IdealFamily.SetFamily.sum_card_contr_eq_sum_cardS_sub_one F.toSetFamily (v := v)
  exact And.intro (congrArg (fun k : ℕ => (k : ℤ)) hCard) hSum

/-- Delta of total sizes: `Δ_total = |S| + Σ_{t∈(contr∩del)} |t|`. -/
lemma delta_total_size (hne : (F.ground.erase v).Nonempty) :
  (F.toSetFamily).totalSize - (F.traceIdeal v hne).toSetFamily.totalSize
    = (((F.toSetFamily).S v).card : ℤ)
      + (∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), (t.card : ℤ)) := by
  classical
  set Sset := (F.toSetFamily).S v
  set Dset := (F.toSetFamily).delCarrier v
  set Cset := (F.toSetFamily).contrCarrier v
  set diff := Cset \ Dset
  set inter := Cset ∩ Dset
  --have hF := totalSize_split_F (F := F) (v := v)
  have hT := totalSize_split_trace (F := F) (v := v) hne
  have hsplitC : sumZ Cset = sumZ diff + sumZ inter := by
    have hunion : diff ∪ inter = Cset := by
      simp [diff, inter, Cset, Dset] --using   sdiff_union_inter_eq_self_on_contr (F := F) (v := v)
      exact sdiff_union_inter (F.contrCarrier v) (F.delCarrier v)
    have hdisj : Disjoint diff inter := by
      simp [diff, inter, Cset, Dset]
      exact disjoint_sdiff_inter (F.contrCarrier v) (F.delCarrier v)
    unfold sumZ
    simp [diff, inter, Cset, Dset]
    --  (Finset.sum_union (by exact hdisj) (f := fun s => (s.card : ℤ)))
    let fs := (Finset.sum_union (by exact hdisj) (f := fun s:Finset α => (s.card : ℤ)))
    simp at fs
    simp_all only [diff, Cset, Dset, inter]
  have hContr := contr_count_and_sum (F := F) (v := v)
  have hSumC : sumZ Cset = ∑ s ∈ Sset, ((s.card : ℤ) - 1) := by
    simpa [Cset, Sset] using hContr.right
  have hDelta0 :
      (F.toSetFamily).totalSize - (F.traceIdeal v hne).toSetFamily.totalSize
        = sumZ Sset - sumZ diff := by
    have hTotalF : (F.toSetFamily).totalSize = sumZ Dset + sumZ Sset := by
      simp only [SetFamily.totalSize, SetFamily.totalSizeNat, sumZ, Dset, Sset]
      rw [carrier_eq_del_union_S (F := F) (v := v), Finset.sum_union (disjoint_del_S (F := F) (v := v))]
      simp only [Nat.cast_add, Nat.cast_sum]
    rw [hTotalF, hT]
    ring
  have hDiff : sumZ diff = sumZ Cset - sumZ inter := by
    have := congrArg (fun z : ℤ => z - sumZ inter) hsplitC
    have : sumZ Cset - sumZ inter = sumZ diff := by
      simpa [diff, inter]
    exact this.symm
  have hconst : ∑ _s ∈ Sset, (1 : ℤ) = (Sset.card : ℤ) := by
    simp [Finset.sum_const]
  have hSumShift : sumZ Sset - ∑ s ∈ Sset, ((s.card : ℤ) - 1) = (Sset.card : ℤ) := by
    have h' :=
      (Finset.sum_sub_distrib (s := Sset)
        (f := fun s => (s.card : ℤ))
        (g := fun s => (s.card : ℤ) - 1)).symm
    have h'' :
        sumZ Sset - ∑ s ∈ Sset, ((s.card : ℤ) - 1)
          = ∑ s ∈ Sset, ((s.card : ℤ) - ((s.card : ℤ) - 1)) := by
      simp [sumZ]
    calc
      sumZ Sset - ∑ s ∈ Sset, ((s.card : ℤ) - 1)
          = ∑ s ∈ Sset, ((s.card : ℤ) - ((s.card : ℤ) - 1)) := h''
      _ = ∑ _s ∈ Sset, (1 : ℤ) := by
        refine Finset.sum_congr rfl ?_
        intro s hs
        simp
      _ = (Sset.card : ℤ) := hconst
  calc
    (F.toSetFamily).totalSize - (F.traceIdeal v hne).toSetFamily.totalSize
        = sumZ Sset - sumZ diff := hDelta0
    _ = sumZ Sset - (sumZ Cset - sumZ inter) := by
      simp [hDiff]
    _ = (sumZ Sset - ∑ s ∈ Sset, ((s.card : ℤ) - 1)) + sumZ inter := by
      simp [hSumC, sub_eq_add_neg, add_comm, add_left_comm]
    _ = (Sset.card : ℤ) + sumZ inter := by
      simp
      exact Int.sub_sub_self (sumZ Sset) ↑(#Sset)


/-- Edge-level combination under trace. -/
lemma edges_combo (hne : (F.ground.erase v).Nonempty) :
  - (F.toSetFamily).numEdges * (n : ℤ)
  + (F.traceIdeal v hne).toSetFamily.numEdges * ((n : ℤ) - 1)
  = - ( (((F.toSetFamily).delCarrier v).card : ℤ) + (((F.toSetFamily).S v).card : ℤ) )
    - ((n : ℤ) - 1) * (((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v).card : ℤ) := by
  classical
  have hF := numEdges_split_F (F := F) (v := v)
  have hT := numEdges_split_trace (F := F) (v := v) hne
  have hCard : (((F.toSetFamily).contrCarrier v).card : ℤ) = (((F.toSetFamily).S v).card : ℤ) :=
    (contr_count_and_sum (F := F) (v := v)).left
  calc
    - (F.toSetFamily).numEdges * (n : ℤ)
      + (F.traceIdeal v hne).toSetFamily.numEdges * ((n : ℤ) - 1)
        = - ((((F.toSetFamily).delCarrier v).card : ℤ) + (((F.toSetFamily).S v).card : ℤ)) * (n : ℤ)
          + ((((F.toSetFamily).delCarrier v).card : ℤ)
              + ((((F.toSetFamily).contrCarrier v).card : ℤ) - ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v).card)) * ((n : ℤ) - 1) := by
              rw [hF, hT]
              ring
    _   = - ((((F.toSetFamily).delCarrier v).card : ℤ) + (((F.toSetFamily).S v).card : ℤ)) * (n : ℤ)
          + ((((F.toSetFamily).delCarrier v).card : ℤ)
              + ((((F.toSetFamily).S v).card : ℤ) - ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v).card)) * ((n : ℤ) - 1) := by
              rw [hCard]
    _   = - ( (((F.toSetFamily).delCarrier v).card : ℤ) + (((F.toSetFamily).S v).card : ℤ) )
          - ((n : ℤ) - 1) * (((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v).card : ℤ) := by
              ring
omit [DecidablePred F.sets] in
/-- Cast `|U \ {v}|` to `ℤ` as `(n : ℤ) - 1`. -/
lemma card_ground_erase_z (hvU : v ∈ F.ground) :
  ((F.ground.erase v).card : ℤ) = (n : ℤ) - 1 := by
  classical
  have hN : (F.ground.erase v).card = n - 1 := Finset.card_erase_of_mem hvU
  have hZ : ((F.ground.erase v).card : ℤ) = ((n - 1 : ℕ) : ℤ) :=
    congrArg (fun k : ℕ => (k : ℤ)) hN
  have hnpos : 1 ≤ n := by
    have : 0 < F.ground.card := Finset.card_pos.mpr ⟨v, hvU⟩
    exact Nat.succ_le_of_lt this
  have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - (1 : ℤ) := (Nat.cast_sub hnpos)
  exact Eq.trans hZ hcast

/-- Rewrite the degree-term into `2|S| - (|del|+|S|)`. -/
lemma degree_numEdges_combo :
  ((2 : ℤ) * ((F.toSetFamily).degree v) - (F.toSetFamily).numEdges)
    = (2 : ℤ) * (((F.toSetFamily).S v).card : ℤ)
      - ( (((F.toSetFamily).delCarrier v).card : ℤ) + (((F.toSetFamily).S v).card : ℤ) ) := by
  classical
  have h1 : (F.toSetFamily).degree v = (((F.toSetFamily).S v).card : ℤ) := by exact rfl
  have h2 : (F.toSetFamily).numEdges = (((F.toSetFamily).delCarrier v).card : ℤ) + (((F.toSetFamily).S v).card : ℤ) := numEdges_split_F (F := F) (v := v)
  cases h1
  simp_all only [sub_left_inj, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
  rfl

/-- Linearize the intersection-sum: factor `2` and `n-1` out of the sums. -/
lemma inter_sum_linear :
  (2 : ℤ) * (∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), (t.card : ℤ))
    - ((n : ℤ) - 1) * (((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v).card : ℤ)
  = ∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), ((2 : ℤ) * (t.card : ℤ))
    - ∑ _t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), ((n : ℤ) - 1) := by
  classical
  have hmul :
    ∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), ((2 : ℤ) * (t.card : ℤ))
      = (2 : ℤ) * (∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), (t.card : ℤ)) := by
    rw [mul_sum]
  calc
    (2 : ℤ) * (∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), (t.card : ℤ))
      - ((n : ℤ) - 1) * (((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v).card : ℤ)
        = (∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), ((2 : ℤ) * (t.card : ℤ)))
          - ((n : ℤ) - 1) * (((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v).card : ℤ) := by
            simp_all only
    _   = (∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), ((2 : ℤ) * (t.card : ℤ)))
          - (∑ _t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), ((n : ℤ) - 1)) := by
            simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, mul_one, sub_right_inj]
            rw [mul_comm]
            rw [mul_sub, mul_one]

/-- Pack two sums into `∑ (2|t| − (n−1))`. -/
lemma inter_sum_pack :
  (∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), ((2 : ℤ) * (t.card : ℤ)))
    - (∑ _t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), ((n : ℤ) - 1))
  = ∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), ((2 : ℤ) * (t.card : ℤ) - ((n : ℤ) - 1)) := by
  classical
  simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, mul_one]

/-! #################################  Main theorem  ################################# -/

/-- Exact one-step difference under trace (requires `v∈U` and `(U\{v})` nonempty).

`nds(F) - nds(trace_v(F)) = normalizedDegreeAt v
  + ∑_{t∈(contr∩del)} ( 2|t| - (n-1) )`. -/
theorem nds_diff_trace_as_normdeg
  (hvU : v ∈ F.ground)
  (hne : (F.ground.erase v).Nonempty) :
  (F.toSetFamily).nds - (F.traceIdeal v hne).toSetFamily.nds
    = (F.toSetFamily).normalizedDegreeAt v
      + ∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v),
          ((2 : ℤ) * (t.card : ℤ) - ((n : ℤ) - 1)) := by
  classical
  -- Δ_total
  have hΔtot :
      (F.toSetFamily).totalSize - (F.traceIdeal v hne).toSetFamily.totalSize
      = (((F.toSetFamily).S v).card : ℤ)
        + (∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), (t.card : ℤ)) :=
    delta_total_size (F := F) (v := v) hne
  -- edges
  have hEdges :
      - (F.toSetFamily).numEdges * (n : ℤ)
      + (F.traceIdeal v hne).toSetFamily.numEdges * ((n : ℤ) - 1)
      = - ( (((F.toSetFamily).delCarrier v).card : ℤ) + (((F.toSetFamily).S v).card : ℤ) )
        - ((n : ℤ) - 1) * (((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v).card : ℤ) :=
    edges_combo (F := F) (v := v) hne
  -- |U\{v}| cast
  have hGround : ((F.ground.erase v).card : ℤ) = (n : ℤ) - 1 :=
    card_ground_erase_z (F := F) (v := v) hvU
  -- degree/edges rewrite
  have hDegEdges :
      ( (2 : ℤ) * (F.toSetFamily).degree v - (F.toSetFamily).numEdges )
      = (2 : ℤ) * (((F.toSetFamily).S v).card : ℤ) - ( (((F.toSetFamily).delCarrier v).card : ℤ) + (((F.toSetFamily).S v).card : ℤ) ) :=
    degree_numEdges_combo (F := F) (v := v)
  -- intersection sums
  have hInterLin :
      (2 : ℤ) * (∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), (t.card : ℤ))
        - ((n : ℤ) - 1) * (((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v).card : ℤ)
      = ∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), ((2 : ℤ) * (t.card : ℤ))
        - ∑ _t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), ((n : ℤ) - 1) :=
    inter_sum_linear (F := F) (v := v)
  have hInterPack :
      (∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), ((2 : ℤ) * (t.card : ℤ)))
        - (∑ _t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), ((n : ℤ) - 1))
      = ∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), ((2 : ℤ) * (t.card : ℤ) - ((n : ℤ) - 1)) :=
    inter_sum_pack (F := F) (v := v)

  -- Assemble pieces in the NDS definition
  unfold SetFamily.nds
  calc
    (2 : ℤ) * (F.toSetFamily).totalSize - (F.toSetFamily).numEdges * (n : ℤ)
      - ( (2 : ℤ) * (F.traceIdeal v hne).toSetFamily.totalSize
          - (F.traceIdeal v hne).toSetFamily.numEdges * (((F.ground.erase v).card : ℤ)) )
        = (2 : ℤ) * ((F.toSetFamily).totalSize - (F.traceIdeal v hne).toSetFamily.totalSize)
          + ( - (F.toSetFamily).numEdges * (n : ℤ)
              + (F.traceIdeal v hne).toSetFamily.numEdges * (((F.ground.erase v).card : ℤ)) ) := by
            ring
    _   = (2 : ℤ) * ( (((F.toSetFamily).S v).card : ℤ)
                      + (∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), (t.card : ℤ)) )
          + ( - (F.toSetFamily).numEdges * (n : ℤ)
              + (F.traceIdeal v hne).toSetFamily.numEdges * (((F.ground.erase v).card : ℤ)) ) := by
            rw [hΔtot]
    _   = (2 : ℤ) * ( (((F.toSetFamily).S v).card : ℤ)
                      + (∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), (t.card : ℤ)) )
          + ( - (F.toSetFamily).numEdges * (n : ℤ)
              + (F.traceIdeal v hne).toSetFamily.numEdges * ((n : ℤ) - 1) ) := by
            rw [hGround]
    _   = ( (2 : ℤ) * (((F.toSetFamily).S v).card : ℤ)
            - ( (((F.toSetFamily).delCarrier v).card : ℤ) + (((F.toSetFamily).S v).card : ℤ) ) )
          + ( (2 : ℤ) * (∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), (t.card : ℤ))
              - ((n : ℤ) - 1) * (((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v).card : ℤ) ) := by
            rw [hEdges]
            ring
    _   = ( (2 : ℤ) * ((F.toSetFamily).degree v) - (F.toSetFamily).numEdges )
          + ( ∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), ((2 : ℤ) * (t.card : ℤ))
              - ∑ _t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), ((n : ℤ) - 1) ) := by
            simp_all only [neg_mul, neg_add_rev, card_erase_of_mem, one_le_card, SetFamily.nonempty_ground,
              Nat.cast_sub, Nat.cast_one, sum_sub_distrib, sum_const, Int.nsmul_eq_mul, mul_one]
    _   = (F.toSetFamily).normalizedDegreeAt v
          + ∑ t ∈ ((F.toSetFamily).contrCarrier v ∩ (F.toSetFamily).delCarrier v), ((2 : ℤ) * (t.card : ℤ) - ((n : ℤ) - 1)) := by
            simp_all only [neg_mul, neg_add_rev, card_erase_of_mem, one_le_card, SetFamily.nonempty_ground,
              Nat.cast_sub, Nat.cast_one, sum_sub_distrib, sum_const, Int.nsmul_eq_mul, mul_one, add_left_inj]
            symm
            exact hDegEdges

end
end Ideal
end IdealFamily
