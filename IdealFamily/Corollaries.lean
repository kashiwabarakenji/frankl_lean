/-
  IdealFamily/Corollaries.lean

  Purpose.
    Handy corollaries that are frequently used in arguments built on top of
    the exact difference identity proved in `NDSDiff.lean`.
    We keep the statements tactic-light and close to paper wording.

  Contents overview.
    • Double counting:  Σ_v normalizedDegreeAt(v) = nds(F)  (SetFamily-level).
    • Existence of a rare vertex if nds(F) ≤ 0 (Ideal-level).
    • Lower bound on the trace difference when the intersection terms are
      "large" (each contributes ≥ 0).
    • Thin wrappers around the deg=1 specialization.

  Conventions.
    – One import per line.
    – No `induction'`, no `simpa using`.
-/
import IdealFamily.Core
import IdealFamily.Contraction
import IdealFamily.NDSDiff
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import LeanCopilot

namespace IdealFamily
namespace SetFamily

open Finset
open scoped BigOperators

noncomputable section

variable {α : Type*} [DecidableEq α]
variable (SF : SetFamily α) [DecidablePred SF.sets]

/- ********************  Double-counting identities  ******************** -/

/-- NAT version: total vertex-incidences equal total edge-sizes.
    Σ_{v∈U} degNat(v) = Σ_{s∈carrier} |s|. -/
lemma sum_degreeNat_over_ground_eq_totalSizeNat :
  ∑ v ∈ SF.ground, SF.degreeNat v
    = ∑ s ∈ SF.carrier, s.card := by
  classical
  -- Expand degreeNat(v) = |S v| then convert `card` to a sum of 1s and use `sum_filter`.
  have H1 :
      ∀ v ∈ SF.ground,
        SF.degreeNat v
          = ∑ s ∈ SF.carrier, (if v ∈ s then (1 : ℕ) else 0) := by
    intro v hv
    -- |S v| = card (carrier.filter (v∈·))
    -- Convert to sum of 1 over the filtered carrier, then to an "if" over carrier.
    calc
      SF.degreeNat v
          = (SF.S v).card := by rfl
      _   = ∑ _s ∈ SF.S v, (1 : ℕ) := by
              -- card = sum of ones
              exact Finset.card_eq_sum_ones _
      _   = ∑ s ∈ SF.carrier, (if v ∈ s then (1 : ℕ) else 0) := by
              -- sum over filter equals filtered-sum by an if-then-else
              -- sum_filter: ∑_{x∈s.filter p} f x = ∑_{x∈s} (if p x then f x else 0)
              simp
              exact rfl

  -- Swap the sums (Σ_v Σ_s ↔ Σ_s Σ_v) and evaluate the inner indicator sum.
  have H2 :
      ∑ v ∈ SF.ground, ∑ s ∈ SF.carrier, (if v ∈ s then (1 : ℕ) else 0)
        = ∑ s ∈ SF.carrier, ∑ v ∈ SF.ground, (if v ∈ s then (1 : ℕ) else 0) := by
    exact Finset.sum_comm

  -- For each s∈carrier, since s ⊆ ground, the inner sum equals |s|.
  have H3 :
      ∀ s ∈ SF.carrier,
        ∑ v ∈ SF.ground, (if v ∈ s then (1 : ℕ) else 0)
          = s.card := by
    intro s hs
    -- use s ⊆ ground


    have hsub : s ⊆ SF.ground :=
      (SetFamily.mem_carrier_iff (SF := SF)).mp hs |>.1
    -- counting members of s by filtering ground
    -- sum of 1 over ground with predicate (v∈s) equals (ground.filter (·∈s)).card
    -- and that equals s.card because s ⊆ ground.
    calc
      ∑ v ∈ SF.ground, (if v ∈ s then (1 : ℕ) else 0)
          = ∑ v ∈ (SF.ground.filter (fun v => v ∈ s)), (1 : ℕ) := by
                -- turn an "if" over ground into filtering
                simp
                exact rfl
      _   = (SF.ground.filter (fun v => v ∈ s)).card := by
                exact Eq.symm (card_eq_sum_ones ({v ∈ SF.ground | v ∈ s}))
      _   = s.card := by
                -- `filter`ing ground by membership in `s` recovers `s` because `s ⊆ ground`.
                have hEq : SF.ground.filter (fun v => v ∈ s) = s := by
                  classical
                  apply Finset.ext
                  intro v
                  constructor
                  · intro hv
                    -- v ∈ ground ∧ v ∈ s ⇒ v ∈ s
                    exact (Finset.mem_filter.mp hv).2
                  · intro hv
                    -- v ∈ s ⇒ v ∈ ground (since s ⊆ ground) and v ∈ s
                    exact Finset.mem_filter.mpr ⟨hsub hv, hv⟩
                exact congrArg Finset.card hEq

  -- Put all together
  calc
    ∑ v ∈ SF.ground, SF.degreeNat v
        = ∑ v ∈ SF.ground, ∑ s ∈ SF.carrier, (if v ∈ s then (1 : ℕ) else 0) := by
              refine Finset.sum_congr rfl ?step
              intro v hv
              exact H1 v hv
    _   = ∑ s ∈ SF.carrier, ∑ v ∈ SF.ground, (if v ∈ s then (1 : ℕ) else 0) := by
              exact H2
    _   = ∑ s ∈ SF.carrier, s.card := by
              simp_all only [sum_boole, Nat.cast_id]

/-- INT version: Σ_{v∈U} degree(v) = totalSize. -/
lemma sum_degree_over_ground_eq_totalSize :
  ∑ v ∈ SF.ground, (SF.degree v)
    = SF.totalSize := by
  classical
  -- degree = zcast degreeNat
  have hdeg :
      ∀ v, SF.degree v = (SF.degreeNat v : ℤ) := by
    intro v; rfl
  -- cast the NAT identity to ℤ
  have Hnat := sum_degreeNat_over_ground_eq_totalSizeNat (SF := SF)
  -- rewrite both sides via casts
  calc
    ∑ v ∈ SF.ground, SF.degree v
        = ∑ v ∈ SF.ground, ((SF.degreeNat v : ℤ)) := by
              refine Finset.sum_congr rfl ?step
              intro v hv; exact hdeg v
    _   = (∑ v ∈ SF.ground, SF.degreeNat v : ℤ) := by
              -- push-ofNat through sum (ℤ-linear)
              rfl
    _   = (∑ s ∈ SF.carrier, s.card : ℤ) := by
              norm_cast
    _   = SF.totalSize := by
            unfold SetFamily.totalSize
            norm_cast

/-- Frankl's identity: the sum of normalized degrees equals NDS. -/
lemma sum_normalizedDegree_over_ground_eq_nds :
  ∑ v ∈ SF.ground, SF.normalizedDegreeAt v
    = SF.nds := by
  classical
  -- Expand: Σ(2*deg - |F|) = 2 Σdeg - |U| * |F| = 2*totalSize - n*|F| = nds.
  have Hdeg := sum_degree_over_ground_eq_totalSize (SF := SF)
  calc
    ∑ v ∈ SF.ground, SF.normalizedDegreeAt v
        = ∑ v ∈ SF.ground, ((2 : ℤ) * SF.degree v - SF.numEdges) := by
              rfl
    _   = (2 : ℤ) * (∑ v ∈ SF.ground, SF.degree v)
          - (SF.ground.card : ℤ) * SF.numEdges := by
              -- linearity of sum
              ring_nf
              simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul]
              have hsum :
                ∑ x ∈ SF.ground, SF.degree x * (2 : ℤ)
                  = SF.totalSize * 2 := by
                classical
                -- pull 2 out of the sum, then use Hdeg
                have h1 :
                  ∑ x ∈ SF.ground, SF.degree x * (2 : ℤ)
                    = (∑ x ∈ SF.ground, SF.degree x) * (2 : ℤ) := by
                  exact Eq.symm (sum_mul SF.ground SF.degree 2)
                have h2 :
                  (∑ x ∈ SF.ground, SF.degree x) * (2 : ℤ)
                    = SF.totalSize * 2 := by
                  exact congrArg (fun z : ℤ => z * (2 : ℤ)) Hdeg
                exact Eq.trans h1 h2

              have hcomm :
                (SF.ground.card : ℤ) * SF.numEdges = SF.numEdges * (SF.ground.card : ℤ) := by
                exact mul_comm _ _

              calc
                ∑ x ∈ SF.ground, SF.degree x * 2 - (SF.ground.card : ℤ) * SF.numEdges
                    = SF.totalSize * 2 - (SF.ground.card : ℤ) * SF.numEdges := by
                      simp_all only
                _   = SF.totalSize * 2 - (SF.numEdges * (SF.ground.card : ℤ)) := by
                      simp_all only
                _   = -(SF.numEdges * (SF.ground.card : ℤ)) + SF.totalSize * 2 := by
                      ring


    _   = (2 : ℤ) * SF.totalSize - (SF.ground.card : ℤ) * SF.numEdges := by
              simp_all only
    _   = SF.nds := by
              unfold SetFamily.nds
              simp_all only [sub_right_inj]
              ring

end
end SetFamily

/- ********************  Rare vertices and existence  ******************** -/

namespace Ideal

open Finset
open scoped BigOperators

--namespace Ideal

variable {α : Type*} [DecidableEq α]
variable (F : Ideal α) [DecidablePred F.sets]


/-- **General split formula for the `{v}`-edge case (no `deg1` needed).**
If `{v} ∈ F` then `∅` appears in the intersection block of the exact trace-difference
identity. Splitting off that `∅` term gives a clean relation useful for the
“{v} is a hyperedge” branch.

This lemma rewrites
`nds(F) - nds(trace_v(F))`
as
`normalizedDegreeAt v - (|U|-1) + (sum over the remaining intersection members)`.

It does **not** assume `degNat v = 1` nor `ground.erase v ∈ F`.
-/
theorem nds_diff_trace_split_empty_when_singleton
  (v : α)
  (hvU : v ∈ F.ground)
  (hne : (F.ground.erase v).Nonempty)
  (hSing : F.sets {v}) :
  F.toSetFamily.nds - (F.traceIdeal v hne).toSetFamily.nds
    = F.toSetFamily.normalizedDegreeAt v
      - ((F.ground.card : ℤ) - 1)
      + ∑ t ∈ ((F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v).erase (∅ : Finset α)),
          ((2 : ℤ) * (t.card : ℤ) - ((F.ground.card : ℤ) - 1)) := by
  classical
  -- Start from the exact difference identity against trace.
  have h := Ideal.nds_diff_trace_as_normdeg (F := F) (v := v) hvU hne
  -- Notation for the intersection block and its summand.
  let I : Finset (Finset α) :=
    (F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v)
  let g : Finset α → ℤ :=
    fun t => ((2 : ℤ) * (t.card : ℤ) - ((F.ground.card : ℤ) - 1))

  -- Show that `∅ ∈ I` because `{v} ∈ S v` and erasing `v` gives `∅`,
  -- and `∅ ∈ delCarrier v` holds trivially.
  have h_empty_in_contr : (∅ : Finset α) ∈ F.toSetFamily.contrCarrier v := by
    -- `{v} ∈ S v`:
    have h_sing_in_carrier :
        ({v} : Finset α) ∈ F.toSetFamily.carrier := by
      -- membership in carrier: `{v} ⊆ ground` and `sets {v}`
      have hsub : ({v} : Finset α) ⊆ F.ground :=
        by
          -- `{v} ⊆ ground` iff `v ∈ ground`
          exact Finset.singleton_subset_iff.mpr hvU
      exact (IdealFamily.SetFamily.mem_carrier_iff (SF := F.toSetFamily)).mpr ⟨hsub, hSing⟩
    have h_in_S : ({v} : Finset α) ∈ F.toSetFamily.S v := by
      -- filter by `v ∈ s`
      unfold IdealFamily.SetFamily.S
      exact Finset.mem_filter.mpr ⟨h_sing_in_carrier, by simp⟩
    -- Image along `erase v` hits `∅`.
    unfold IdealFamily.SetFamily.contrCarrier
    -- `erase v {v} = ∅`
    have : ({v} : Finset α).erase v = (∅ : Finset α) := by simp
    exact Finset.mem_image.mpr ⟨({v} : Finset α), h_in_S, by simp [this]⟩

  have h_empty_in_del : (∅ : Finset α) ∈ F.toSetFamily.delCarrier v := by
    -- `∅ ∈ carrier` and `v ∉ ∅`.
    unfold IdealFamily.SetFamily.delCarrier
    have hempty_in_carrier :
        (∅ : Finset α) ∈ F.toSetFamily.carrier := by
      -- `sets ∅` and `∅ ⊆ ground`
      have hsub : (∅ : Finset α) ⊆ F.ground := by
        intro x hx; exact False.elim (Finset.notMem_empty _ hx)
      have hset : F.sets (∅ : Finset α) := F.has_empty
      exact (IdealFamily.SetFamily.mem_carrier_iff (SF := F.toSetFamily)).mpr ⟨hsub, hset⟩
    exact Finset.mem_filter.mpr ⟨hempty_in_carrier, by simp⟩

  have h_empty_in_I : (∅ : Finset α) ∈ I := by
    exact Finset.mem_inter.mpr ⟨h_empty_in_contr, h_empty_in_del⟩

  -- Split the intersection sum into the `∅` part and the rest.
  have h_split :
      ∑ t ∈ I, g t
        = g (∅ : Finset α) + ∑ t ∈ I.erase (∅ : Finset α), g t := by
    -- `I = insert ∅ (I.erase ∅)` because `∅ ∈ I`
    have hIe : insert (∅ : Finset α) (I.erase (∅ : Finset α)) = I :=
      Finset.insert_erase h_empty_in_I
    -- sum over `insert a s` splits
    have := Finset.sum_insert (by exact Finset.notMem_erase (∅ : Finset α) I) (s := I.erase (∅ : Finset α)) (f := g)
    simpa [hIe]

  -- Evaluate the `∅`-term: `g ∅ = 2*0 - (n-1) = -(n-1)`.
  have hg_empty :
      g (∅ : Finset α) = - ((F.ground.card : ℤ) - 1) := by
    unfold g
    simp

  -- Substitute into the exact identity.
  -- nds(F) - nds(trace) = normdeg + (g ∅ + Σ_{I\{∅}} g)
  --                    = normdeg - (n-1) + Σ_{I\{∅}} g.
  calc
    F.toSetFamily.nds - (F.traceIdeal v hne).toSetFamily.nds
        = F.toSetFamily.normalizedDegreeAt v
          + ∑ t ∈ I, g t := by
            simpa [I, g] using h
    _   = F.toSetFamily.normalizedDegreeAt v
          + (g (∅ : Finset α) + ∑ t ∈ I.erase (∅ : Finset α), g t) := by
            simp [h_split]
    _   = F.toSetFamily.normalizedDegreeAt v
          - ((F.ground.card : ℤ) - 1)
          + ∑ t ∈ I.erase (∅ : Finset α), g t := by
            simpa [hg_empty] using by ring

--end Ideal

noncomputable section

variable {α : Type*} [DecidableEq α]
variable (F : Ideal α) [DecidablePred F.sets]

--local notation "SF" => F.toSetFamily

/-- A vertex is *rare* if its normalized degree is ≤ 0. -/
def rare (v : α) : Prop :=
  (F.toSetFamily).normalizedDegreeAt v ≤ 0


/-- When `|ground| = 1`, the carrier is exactly `{∅, ground}`. -/
lemma carrier_eq_pair_card_one
  (h1 : F.ground.card = 1) :
  F.toSetFamily.carrier = {∅, F.ground} := by
  classical
  -- `ground = {u}`
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
  have hU : F.ground = {u} := hu
  -- Show both inclusions.
  apply Finset.Subset.antisymm_iff.mpr
  constructor
  · -- `⊆`
    intro s hs
    -- From `s ∈ carrier` we get `s ⊆ ground` and `sets s`.
    have hsub : s ⊆ F.ground :=
      (IdealFamily.SetFamily.mem_carrier_iff (SF := F.toSetFamily)).mp hs |>.1
    -- Reduce to `s ⊆ {u}`
    have hsub' : s ⊆ {u} := by simpa [hU] using hsub
    -- Two possibilities: `u ∈ s` or not.
    by_cases huin : u ∈ s
    · -- Then `{u} ⊆ s` and `s ⊆ {u}` ⇒ `s = {u} = ground`.
      have : ({u} : Finset α) ⊆ s := by
        intro x hx;
        simp_all only [card_singleton, subset_singleton_iff, mem_singleton]
      have : s = ({u} : Finset α) := Finset.Subset.antisymm hsub' this
      -- place into `{∅, ground}`
      have : s = F.ground := by simpa [hU] using this
      subst this
      simp
    · -- If `u ∉ s` and `s ⊆ {u}`, then `s = ∅`.
      have : s = (∅ : Finset α) := by
        -- No element can be in `s`.
        simp_all only [card_singleton, subset_singleton_iff]
        cases hsub' with
        | inl h =>
          subst h
          simp_all only [notMem_empty, not_false_eq_true]
        | inr h_1 =>
          subst h_1
          simp_all only [mem_singleton, not_true_eq_false]

      subst this
      simp
  · -- `⊇`
    intro s hs
    rcases Finset.mem_insert.mp hs with h | h
    · -- s = ground
      subst h
      exact empty_mem_carrier F
    · dsimp [SetFamily.carrier]
      rw [Finset.mem_filter]
      rw [Finset.mem_powerset]
      constructor
      · simp_all only [card_singleton, mem_insert, mem_singleton, subset_refl]
      · simp at h
        rw [h]
        exact F.has_ground


/-- Base case for the induction: if `|U| = 1` then `nds(F) = 0`. -/
lemma nds_eq_zero_card_one
  (h1 : F.ground.card = 1) :
  F.toSetFamily.nds = 0 := by
  classical
  -- Identify the carrier.
  have hcar : F.toSetFamily.carrier = {∅, F.ground} :=
    carrier_eq_pair_card_one (F := F) h1
  -- Compute `totalSize` and `numEdges` from the identified carrier.
  have hTotal :
      F.toSetFamily.totalSize = (F.ground.card : ℤ) := by
    -- totalSize = zcast (sum of sizes over carrier)
    -- For `{∅, ground}`, that's `0 + |ground| = |ground|`.
    simp [IdealFamily.SetFamily.totalSize, IdealFamily.SetFamily.totalSizeNat, hcar]
  have hEdges :
      F.toSetFamily.numEdges = (2 : ℤ) := by
    classical
    -- まず NAT 側で card = 2 を出す
    have hcard2 :
        (F.toSetFamily.carrier).card = 2 := by
      -- {∅, ground} = insert ∅ {ground}
      have : ∅ ≠ F.ground := by
        -- |ground|=1 なので ∅ とは異なる
        intro heq
        have : (∅ : Finset α).card = 1 := by rw [heq]; exact h1
        simp_all only
        simp_all only [mem_singleton, insert_eq_of_mem, Nat.cast_one]
        rw [← heq] at h1
        simp_all only
        simp [heq.symm] at h1
      have hnot : (∅ : Finset α) ∉ ({F.ground} : Finset (Finset α)) := by simp_all only [Nat.cast_one, ne_eq,
        mem_singleton, not_false_eq_true]
      have :
          (({∅, F.ground} : Finset (Finset α))).card
            = (({F.ground} : Finset (Finset α))).card + 1 := by
        simpa using (card_insert_of_notMem hnot)
      -- {ground} の card は 1
      have : (({∅, F.ground} : Finset (Finset α))).card = 2 := by
        simp_all only [Nat.cast_one, mem_singleton, not_false_eq_true, card_insert_of_notMem, card_singleton,
          Nat.reduceAdd]
      -- carrier=その対集合
      simpa [hcar] using this
    -- ℤ へ持ち上げる
    simp [IdealFamily.SetFamily.numEdges,
           IdealFamily.SetFamily.numEdgesNat, hcard2]

  have h1z : (F.ground.card : ℤ) = 1 := by exact_mod_cast h1
  -- NDS(F) = 2*|ground| - 2*|ground|
  --       = 2*1 - 2*1 = 0.
  simp [IdealFamily.SetFamily.nds, hTotal, hEdges, h1z]

/-- As a corollary of the base case, `nds(F) ≤ 0` when `|U| = 1`. -/
lemma nds_nonpos_card_one
  (h1 : F.ground.card = 1) :
  F.toSetFamily.nds ≤ 0 := by
  simp [nds_eq_zero_card_one (F := F) h1]

/-
If NDS(F) ≤ 0 and U≠∅, there exists a rare vertex in U.
-/
theorem exists_rare_of_nds_le_zero
  (hneU : F.ground.Nonempty)
  (hN :  (F.toSetFamily).nds ≤ 0) :
  ∃ v ∈ F.ground, F.rare v := by
  classical
  -- Σ_v nd(v) = nds(F)
  have Hsum :
      ∑ v ∈ F.ground, (F.toSetFamily).normalizedDegreeAt v
        = (F.toSetFamily).nds :=
    SetFamily.sum_normalizedDegree_over_ground_eq_nds (SF := F.toSetFamily)

  -- 反証法：レア頂点が存在しないと仮定
  by_contra hno
  -- すると全ての項が正：0 < nd(v)
  have hpos :
      ∀ v ∈ F.ground, 0 < (F.toSetFamily).normalizedDegreeAt v := by
    intro v hv
    have : ¬ ( (F.toSetFamily).normalizedDegreeAt v ≤ 0) := by
      exact fun hle => hno ⟨v, hv, hle⟩
    exact Int.lt_of_not_ge this

  -- 整数では 0 < x ↔ 1 ≤ x。よって 1 ≤ nd(v) が各 v で成り立つ
  have hone :
      ∀ v ∈ F.ground, (1 : ℤ) ≤ (F.toSetFamily).normalizedDegreeAt v := by
    intro v hv
    have : 0 < (F.toSetFamily).normalizedDegreeAt v := hpos v hv
    -- a+1 ≤ b ↔ a < b（a=0）を使って 1 ≤ nd(v)
    have := (Int.add_one_le_iff.mpr this : 0 + 1 ≤ (F.toSetFamily).normalizedDegreeAt v)
    simpa [zero_add] using this

  -- 和の下界：Σ 1 ≤ Σ nd(v) ⇒ |U| ≤ Σ nd(v)
  have hsum_ge :
      (F.ground.card : ℤ)
        ≤ ∑ v ∈ F.ground, (F.toSetFamily).normalizedDegreeAt v := by
    have : ∑ _v ∈ F.ground, (1 : ℤ)
            ≤ ∑ v ∈ F.ground, (F.toSetFamily).normalizedDegreeAt v := by
      exact Finset.sum_le_sum (by intro v hv; exact hone v hv)
    -- Σ 1 = card • 1 = card
    simpa [Finset.sum_const, nsmul_one] using this

  -- まとめ： (card : ℤ) ≤ nds(F) ≤ 0 は |U|>0 に矛盾
  have le_nds : (F.ground.card : ℤ) ≤ (F.toSetFamily).nds := by
    simpa [Hsum] using hsum_ge
  have le_zero : (F.ground.card : ℤ) ≤ 0 := le_trans le_nds hN
  have pos_card : 0 < (F.ground.card : ℤ) :=
    Int.natCast_pos.mpr (Finset.card_pos.mpr hneU)
  exact (lt_irrefl (F.ground.card : ℤ)) (lt_of_le_of_lt le_zero pos_card)


/- ********************  When the intersection block is nonnegative  ******************** -/

--variable [DecidablePred F.sets]

/- If every `t ∈ (A∩C)` satisfies `2|t| ≥ n-1` (in ℤ), then
    `nds(F) - nds(trace_v(F)) ≥ normalizedDegreeAt v`. -/
--omit [DecidablePred F.sets] in
theorem diff_ge_normdeg_if_inter_terms_nonneg
  (v : α)
  (hvU : v ∈ F.ground)
  (hne : (F.ground.erase v).Nonempty)
  (hge :
     ∀ t ∈ (F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v),
       (2 : ℤ) * (t.card : ℤ) - ((F.ground.card : ℤ) - 1) ≥ 0) :
  F.toSetFamily.nds - (F.traceIdeal v hne).toSetFamily.nds
    ≥ F.toSetFamily.normalizedDegreeAt v := by
  classical
  -- Use the exact difference identity and drop the nonnegative sum.
  have h := Ideal.nds_diff_trace_as_normdeg (F := F) (v := v) hvU hne
  -- RHS = normdeg + Σ_{A∩C}(2|t| - (n-1)) ≥ normdeg
  -- since each summand is ≥ 0
  -- Rewrite as:  nds(F) - nds(trace) - normdeg ≥ 0.
  -- Then conclude.
  -- We estimate the sum directly by nonnegativity.
  -- Provide the sum ≥ 0 bound:
  have hsum_nonneg :
      0 ≤ ∑ t ∈ (F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v),
              ((2 : ℤ) * (t.card : ℤ) - ((F.ground.card : ℤ) - 1)) := by
    -- each term ≥ 0 ⇒ sum ≥ 0
    have hx :
        ∀ t ∈ (F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v),
          0 ≤ ((2 : ℤ) * (t.card : ℤ) - ((F.ground.card : ℤ) - 1)) := by
      intro t ht
      exact hge t ht
    -- `sum_nonneg` variant via monotonicity: sum of nonnegative terms ≥ 0
    -- Approach: build a lower bound by 0 termwise using `sum_le_sum`.
    -- 0 ≤ Σ f  ⇔  Σ 0 ≤ Σ f
    have : ∑ _t ∈ (F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v), (0 : ℤ)
            ≤ ∑ t ∈ (F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v),
                ((2 : ℤ) * (t.card : ℤ) - ((F.ground.card : ℤ) - 1)) := by
      exact Finset.sum_le_sum (fun t ht => by exact hx t ht)
    -- LHS is 0
    -- Σ 0 over a finset is 0 by definition
    -- thus 0 ≤ Σ ...
    -- Finish:
    have : 0 ≤
      ∑ t ∈ (F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v),
          ((2 : ℤ) * (t.card : ℤ) - ((F.ground.card : ℤ) - 1)) := by
      -- convert previous inequality
      -- (We avoid `simp`; present it as an explicit equality for the left sum.)
      -- sum of zeros is zero:
      have : (∑ _t ∈ (F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v), (0 : ℤ)) = 0 := by
        simp_all
      -- monotonicity inequality gives 0 ≤ RHS
      exact by
        -- `this` named twice; shadow to avoid confusion
        have hz := this
        -- Replace LHS by 0
        apply le_trans (by (expose_names; exact Int.le_refl 0))
        simp_all only [mem_inter, Int.sub_nonneg, tsub_le_iff_right, and_imp, sum_sub_distrib,
          sum_const, Int.nsmul_eq_mul, mul_one, implies_true]
    -- The previous block got too tangled; give it directly:
    -- For clarity and brevity, assert the standard fact:
    -- All terms ≥ 0 ⇒ sum ≥ 0.
    -- We'll re-state it directly:
    clear this
    -- Direct evaluation by induction-free reasoning is allowed; we use the known lemma:
    -- `sum_nonneg`: not available directly; we bound by 0-terms using `sum_le_sum`.
    -- Here, we can simply note that each term is ≥ 0, hence the sum is ≥ 0.
    -- Provide it as `by`:
    exact
      (by
        -- sum of nonnegatives is nonnegative
        -- since ℤ is an ordered ring and the finset is finite, the inequality holds.
        -- Give a short direct proof:
        -- If the set is empty, sum=0≥0. Otherwise, a finite sum of ≥0's ≥0.
        -- Accepted as a standard step.
        exact le_trans (by
           simp_all
           rfl) (by simp_all))

  -- Unfold the exact difference and conclude:
  -- nds(F) - nds(trace) = normdeg + sum ≥ normdeg + 0 = normdeg.
  -- We avoid rewriting machinery; present as inequality via equal RHS form.
  have : F.toSetFamily.nds - (F.traceIdeal v hne).toSetFamily.nds
           = F.toSetFamily.normalizedDegreeAt v
             + ∑ t ∈ (F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v),
                 ((2 : ℤ) * (t.card : ℤ) - ((F.ground.card : ℤ) - 1)) := by
    exact h
  -- Transform equality to ≥ by dropping a ≥0 term.
  -- Thus the desired inequality holds.
  -- Final step:
  --   from  nds(F)-nds(trace) = normdeg + S  and  0 ≤ S,
  --   infer  nds(F)-nds(trace) ≥ normdeg.
  -- Keep it explicit:
  have : F.toSetFamily.nds - (F.traceIdeal v hne).toSetFamily.nds
          - F.toSetFamily.normalizedDegreeAt v
          = ∑ t ∈ (F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v),
                ((2 : ℤ) * (t.card : ℤ) - ((F.ground.card : ℤ) - 1)) := by
    -- rearrange equality
    -- (X = A + S) ⇒ (X - A = S)
    calc
      F.toSetFamily.nds - (F.traceIdeal v hne).toSetFamily.nds
          - F.toSetFamily.normalizedDegreeAt v
            = (F.toSetFamily.normalizedDegreeAt v
               + ∑ t ∈ (F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v),
                   ((2 : ℤ) * (t.card : ℤ) - ((F.ground.card : ℤ) - 1)))
              - F.toSetFamily.normalizedDegreeAt v := by
                simp_all only [mem_inter, Int.sub_nonneg, tsub_le_iff_right, and_imp, sum_sub_distrib, sum_const,
                  Int.nsmul_eq_mul, mul_one, add_sub_cancel_left]
      _ = ∑ t ∈ (F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v),
                ((2 : ℤ) * (t.card : ℤ) - ((F.ground.card : ℤ) - 1)) := by
                ring
  -- Hence the LHS difference is ≥ 0 by `hsum_nonneg`.
  have : 0 ≤
    F.toSetFamily.nds - (F.traceIdeal v hne).toSetFamily.nds
      - F.toSetFamily.normalizedDegreeAt v := by
    -- rewrite by the equality
    simp_all only [mem_inter, Int.sub_nonneg, tsub_le_iff_right, and_imp, sum_sub_distrib, sum_const, Int.nsmul_eq_mul,
      mul_one, add_sub_cancel_left]
  -- Move the term to RHS.
  exact le_of_sub_nonneg this

/- ********************  Convenience around deg=1 specialization  ******************** -/


/-- If `deg v = 1` and `U \\ {v}` is a hyperedge, then `nds(F) ≤ 0`.

Idea: with `deg v = 1`, necessarily `S v = {U}`. If moreover `U\\{v} ∈ F`,
then every subset of `U\\{v}` also lies in `F` by downward closure.
Using the exact trace-difference identity,
`nds(F) - nds(trace_v F) = (2*deg v - |F|) + Σ_{t∈A∩C}(2|t|-(n-1))`,
the intersection block reduces to the single term `t = U\\{v}`,
whose contribution simplifies to `(U\\{v}).card` in ℤ.
Hence
`nds(F) = nds(trace_v F) + ((U\\{v}).card + 2) - |F|`.
Finally, since `F` contains at least the `|U|-1` singletons `{u}` with `u≠v`,
together with `∅` and `U`, we have `|F| ≥ (U\\{v}).card + 2`. Therefore
`nds(F) ≤ nds(trace_v F) ≤ 0` (the latter by the general nonpositivity theorem
for the trace ideal). -/
theorem nds_nonpos_deg1_groundErase_in
  (v : α)
  (hvU   : v ∈ F.ground)
  (hdeg1 : F.toSetFamily.degreeNat v = 1)
  (hne   : (F.ground.erase v).Nonempty)
  (hHave : F.sets (F.ground.erase v)) :
  F.toSetFamily.nds ≤ 0 := by
  classical
  -- Notation
  set P : Finset α := F.ground.erase v with hPdef

  -- Step 1: `S v = {ground}` from `deg v = 1`.
  have hS_card1 : (F.toSetFamily.S v).card = 1 := by
    -- degreeNat v is definitionally `(S v).card`
    simpa using hdeg1
  have hS_singleton : F.toSetFamily.S v = {F.ground} := by
    -- card(S v) = 1 かつ ground ∈ S v ⇒ S v = {ground}
    have hUmem : F.ground ∈ F.toSetFamily.S v := by
      have hcar : F.ground ∈ F.toSetFamily.carrier := Ideal.ground_mem_carrier F
      exact Finset.mem_filter.mpr ⟨hcar, hvU⟩
    obtain ⟨s0, hs0⟩ := Finset.card_eq_one.mp hS_card1
    -- ground ∈ S v = {s0} より ground = s0
    have : F.ground ∈ ({s0} : Finset (Finset α)) := by simpa [hs0] using hUmem
    have hgs0 : F.ground = s0 := by simpa [Finset.mem_singleton] using this
    simp [hs0, hgs0]

  -- Step 2: `contrCarrier v = {P}` and hence `(contr ∩ del) = {P}`.
  have h_contr_singleton : F.toSetFamily.contrCarrier v = {P} := by
    have : F.toSetFamily.contrCarrier v
            = (F.toSetFamily.S v).image (fun s => s.erase v) := rfl
    simp [this, hS_singleton, hPdef]
  have hP_in_del : P ∈ F.toSetFamily.delCarrier v := by
    -- P is in the carrier (downward from `P ∈ F`) and does not contain v.
    have hP_set : F.sets P := by
      -- `P ⊆ F.ground` and `P ≠ ground`, so from `hHave : F.sets P` we already have it.
      simpa [hPdef] using hHave
    have hP_subU : P ⊆ F.ground := by
      -- `erase` is a subset of the original finset
      intro x hx
      exact Finset.mem_of_mem_erase hx
    have hP_car : P ∈ F.toSetFamily.carrier :=
      (IdealFamily.SetFamily.mem_carrier_iff (SF := F.toSetFamily)).mpr ⟨hP_subU, hP_set⟩
    have hv_notin_P : v ∉ P := by simp [hPdef]  -- by property of `erase`
    -- Put together: `delCarrier` is `carrier.filter (v∉·)`.
    exact Finset.mem_filter.mpr ⟨hP_car, by simp [hv_notin_P]⟩
  have h_inter_singleton :
      (F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v) = {P} := by
    apply Finset.ext
    intro t
    constructor
    · intro ht
      have htC : t ∈ F.toSetFamily.contrCarrier v := (Finset.mem_inter.mp ht).1
      have : t ∈ ({P} : Finset (Finset α)) := by simpa [h_contr_singleton] using htC
      have : t = P := by simpa [Finset.mem_singleton] using this
      simp [this]
    · intro ht
      have htP : t = P := by simpa [Finset.mem_singleton] using ht
      subst htP
      exact Finset.mem_inter.mpr ⟨by simp [h_contr_singleton], hP_in_del⟩

  -- Step 3: Plug into the exact identity and simplify the (A∩C)-sum.
  have hdiff :=
    Ideal.nds_diff_trace_as_normdeg (F := F) (v := v) hvU hne
  have hsum_eq :
      ∑ t ∈ (F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v),
          ((2 : ℤ) * (t.card : ℤ) - ((F.ground.card : ℤ) - 1))
        = ((2 : ℤ) * (P.card : ℤ) - ((F.ground.card : ℤ) - 1)) := by
    -- intersection is `{P}`
    simp [h_inter_singleton]
  -- Convert the last term using `card_erase_add_one : P.card + 1 = ground.card`.
  have hNat : P.card + 1 = F.ground.card := by
    -- standard card lemma for erase
    simpa [hPdef] using Finset.card_erase_add_one hvU
  have hUZ : (F.ground.card : ℤ) = (P.card : ℤ) + 1 := by
    -- cast the NAT equality
    have : ((P.card + 1 : ℕ) : ℤ) = (F.ground.card : ℤ) := by exact_mod_cast hNat
    -- rewrite the LHS
    simpa [Int.natCast_add, Int.ofNat_one] using this.symm
  have hUZ_sub :
      (F.ground.card : ℤ) - 1 = (P.card : ℤ) := by
    -- subtract 1 on both sides of `hUZ`
    have := congrArg (fun z : ℤ => z - 1) hUZ
    -- `(P.card : ℤ) + 1 - 1 = (P.card : ℤ)`
    simpa [add_comm, add_left_comm, add_assoc, sub_self] using this
  have hsum_simpl :
      ((2 : ℤ) * (P.card : ℤ) - ((F.ground.card : ℤ) - 1)) = (P.card : ℤ) := by
    simp [hUZ_sub, two_mul, sub_eq_add_neg, add_assoc]

    --  (by ring_nf : (2 : ℤ) * (P.card : ℤ) - (P.card : ℤ) = (P.card : ℤ))

  -- Therefore:
  have hmain_eq :
      F.toSetFamily.nds - (F.traceIdeal v hne).toSetFamily.nds
        = (2 : ℤ) * (F.toSetFamily.degree v) - (F.toSetFamily.numEdges)
          + (P.card : ℤ) := by
    -- rewrite the exact identity
    simpa [hsum_eq, hsum_simpl, SetFamily.normalizedDegreeAt, SetFamily.degree_eq_zcast_degreeNat,
      SetFamily.numEdges_eq_zcast_card] using hdiff

  -- But `deg v = 1` ⇒ the first part is `2 - |F|`.
  have hdeg_z : (F.toSetFamily.degree v) = (1 : ℤ) := by
    simp [SetFamily.degree_eq_zcast_degreeNat, hdeg1]
  have hfirst :
      (2 : ℤ) * (F.toSetFamily.degree v) - (F.toSetFamily.numEdges)
        = (2 : ℤ) - (F.toSetFamily.numEdges) := by
    simp [hdeg_z]

  -- Lower bound the number of edges: at least all subsets of `P` plus `ground`.
  -- Build an explicit subfamily `T ⊆ carrier` with `|T| = P.card + 2`.
  let T : Finset (Finset α) :=
    insert F.ground (insert (∅ : Finset α) ((P.image fun u => ({u} : Finset α))))
  have hT_sub : T ⊆ F.toSetFamily.carrier := by
    intro t ht
    -- cases on membership in the inserted finset
    have hU_car : F.ground ∈ F.toSetFamily.carrier := Ideal.ground_mem_carrier F
    have hempty_car : (∅ : Finset α) ∈ F.toSetFamily.carrier := Ideal.empty_mem_carrier (F := F)
    -- Each `{u}` with `u ∈ P` is in the carrier by downward closure from `P`.
    have h_singleton_car :
        ∀ {u}, u ∈ P → ({u} : Finset α) ∈ F.toSetFamily.carrier := by
      intro u hu
      -- `{u} ⊆ P` and `F.sets P` with `P ≠ ground` ⇒ `F.sets {u}`
      have hsub : ({u} : Finset α) ⊆ P := by
        intro x hx
        have hx' : x = u := by simpa [Finset.mem_singleton] using hx
        simpa [hx'] using hu

      have hP_ne_ground : P ≠ F.ground := by
        intro h
        have hv_in_P : v ∈ P := by simpa [h] using hvU
        have : v ∉ P := by simp [hPdef]
        exact this hv_in_P


      have hset_u : F.sets ({u} : Finset α) := by
        exact F.down_closed (by simpa [hPdef] using hHave) hP_ne_ground (by
          -- `{u} ⊆ P` proved above
          exact hsub)
      -- also `{u} ⊆ ground`
      have hsubU : ({u} : Finset α) ⊆ F.ground := by
        intro x hx
        have : x = u := by simpa [Finset.mem_singleton] using hx
        simpa [this, hPdef] using Finset.mem_of_mem_erase hu
      exact (IdealFamily.SetFamily.mem_carrier_iff (SF := F.toSetFamily)).mpr ⟨hsubU, hset_u⟩
    -- dispatch membership cases
    rcases Finset.mem_insert.mp ht with htU | ht'
    · -- t = F.ground
      subst htU
      exact Ideal.ground_mem_carrier F
    ·
      rcases Finset.mem_insert.mp ht' with ht0 | ht1
      · -- t = ∅
        subst ht0
        exact Ideal.empty_mem_carrier F
      · rcases Finset.mem_image.mp ht1 with ⟨u, huP, rfl⟩
        exact h_singleton_car huP

  -- Compute `|T| = P.card + 2`.
  have h_card_image :
      (P.image fun u => ({u} : Finset α)).card = P.card := by
    -- image by an injective map preserves card
    apply Finset.card_image_iff.mpr
    intro x hx y hy hxy
    simpa [Finset.ext_iff, Finset.mem_singleton] using hxy
  have hdisj0 : (∅ : Finset α) ∉ (P.image fun u => ({u} : Finset α)) := by
    -- `{u} ≠ ∅`
    intro h
    rcases Finset.mem_image.mp h with ⟨u, -, hu⟩
    have : False := by
      have hne : ({u} : Finset α).Nonempty := by simp
      have heq : ({u} : Finset α) = ∅ := hu
      rw [heq] at hne
      exact Finset.not_nonempty_empty hne
    exact this.elim
  have hdisjU : F.ground ∉ insert (∅ : Finset α) (P.image fun u => ({u} : Finset α)) := by
    -- ground contains `v`, but neither `∅` nor `{u}` (with `u ∈ P`) contains `v`.
    intro h
    rcases Finset.mem_insert.mp h with h0 | hrest
    · -- `ground = ∅` impossible (ground is nonempty)
      have : F.ground.Nonempty := F.nonempty_ground
      simp_all only [notMem_empty]
    · rcases Finset.mem_image.mp hrest with ⟨u, huP, hu⟩
      -- then `v ∉ {u}`, contradicts `v ∈ ground`
      have : v ∉ ({u} : Finset α) := by
        -- u ∈ P = F.ground.erase v, so u ≠ v
        have huneq : u ≠ v := by
          have := Finset.mem_erase.mp huP
          exact this.1
        intro hv
        have : v = u := by simpa [Finset.mem_singleton] using hv
        exact huneq (this.symm)
      have : v ∈ ({u} : Finset α) := by simpa [hu] using hvU
      (expose_names; exact this_1 this)
  have hT_card :
      T.card = P.card + 2 := by
    -- card(insert ground (insert ∅ (image ...))) = card(image ...) + 2
    have h1 : (insert (∅ : Finset α) (P.image fun u => ({u} : Finset α))).card
              = (P.image fun u => ({u} : Finset α)).card + 1 := by
      exact card_insert_of_notMem hdisj0-- Finset.card_insert_if_not_mem.mpr hdisj0
    have h2 : T.card
              = (insert (∅ : Finset α) (P.image fun u => ({u} : Finset α))).card + 1 := by
      exact card_insert_of_notMem hdisjU
    calc T.card
        = (insert (∅ : Finset α) (P.image fun u => ({u} : Finset α))).card + 1 := h2
      _ = ((P.image fun u => ({u} : Finset α)).card + 1) + 1 := by rw [h1]
      _ = (P.card + 1) + 1 := by rw [h_card_image]
      _ = P.card + 2 := by simp [Nat.add_assoc]


  -- Hence: `|carrier| ≥ |T| = P.card + 2`.
  have hEdges_ge :
      (P.card + 2) ≤ F.toSetFamily.carrier.card := by
    rw [←hT_card]
    exact Finset.card_le_card hT_sub

  -- Move to ℤ and combine all pieces.
  have hEdges_ge_z :
      ((P.card : ℤ) + 2) ≤ (F.toSetFamily.carrier.card : ℤ) := by
    exact_mod_cast hEdges_ge

  -- From `hmain_eq` and `hfirst`, we get
  have hineq :
      F.toSetFamily.nds - (F.traceIdeal v hne).toSetFamily.nds
        ≤ ((P.card : ℤ) + 2) - (F.toSetFamily.carrier.card : ℤ) := by
    -- rewrite LHS and bound by replacing `|F|` with its lower bound
    have := hmain_eq
    -- `|F|` is `numEdges` in ℤ
    have hFedges : F.toSetFamily.numEdges = (F.toSetFamily.carrier.card : ℤ) := by rfl
    -- rewrite equality to isolate RHS
    -- nds - nds(trace) = (2 - |F|) + P.card = (P.card + 2) - |F|
    have hrew :
        F.toSetFamily.nds - (F.traceIdeal v hne).toSetFamily.nds
          = ((P.card : ℤ) + 2) - (F.toSetFamily.carrier.card : ℤ) := by
      rw [hmain_eq, hfirst, hFedges]
      ring
    -- Now compare with the same RHS; it's equality, so ≤ holds trivially.
    simp [hrew]

  -- Use the lower bound `((P.card)+2) ≤ |F|` to force the RHS ≤ 0.
  have hRHS_nonpos :
      ((P.card : ℤ) + 2) - (F.toSetFamily.carrier.card : ℤ) ≤ 0 := by
    -- a - b ≤ 0  if  a ≤ b  (on ℤ)
    exact sub_nonpos.mpr hEdges_ge_z

  -- Therefore `nds(F) - nds(trace) ≤ 0`, i.e., `nds(F) ≤ nds(trace)`.
  have h_nds_le_trace :
      F.toSetFamily.nds ≤ (F.traceIdeal v hne).toSetFamily.nds := by
    -- from LHS - RHS ≤ 0 ⇒ LHS ≤ RHS
    have := le_trans hineq hRHS_nonpos
    exact (le_of_sub_nonpos this)

  -- Finally, apply nonpositivity to the trace ideal (one size smaller).
  -- NOTE: This requires either (1) adding an induction hypothesis parameter to this theorem,
  -- or (2) invoking a general nds ≤ 0 theorem (like nds_nonpos_via_rare from ViaRare.lean,
  -- but ViaRare imports Corollaries, creating a circular dependency).
  have h_trace_le_zero :
      (F.traceIdeal v hne).toSetFamily.nds ≤ 0 := by
    -- Proof omitted / admitted: the trace ideal has strictly smaller ground,
    -- so one can apply the induction hypothesis or the appropriate nonpositivity
    -- theorem for the smaller ideal; we admit this step here to avoid a
    -- circular import or an unresolved identifier.
      -- ★ trace の carrier = P の冪集合
    have trace_carrier_is_powerset :
        (F.traceIdeal v hne).toSetFamily.carrier = P.powerset := by
      classical
      -- ⊆：trace の carrier の要素は trace の ground ⊆ P に入る
      apply Finset.Subset.antisymm_iff.mpr
      constructor
      · intro s hs
        have hsSub :
            s ⊆ (F.traceIdeal v hne).ground :=
          (IdealFamily.SetFamily.mem_carrier_iff
            (SF := (F.traceIdeal v hne).toSetFamily)).mp hs |>.1
        -- ground = P
        have : (F.traceIdeal v hne).ground = P := by
          -- traceIdeal の ground は定義で erase v
          -- （環境にある等式・simp で潰れます）
          rfl
        -- s ⊆ P ⇒ s ∈ P.powerset
        exact (by
          -- `mem_powerset` で書き換えて終わり
          have : s ⊆ P := by simpa [this] using hsSub
          exact (Finset.mem_powerset.mpr this))
      · -- ⊇：任意の s ⊆ P が trace に入る（delete で取り込まれる）
        intro s hsPow
        have hsSub : s ⊆ P := Finset.mem_powerset.mp hsPow
        -- まず s ∈ F（P ∈ F とイデアルの下方閉性より）
        have hP_ne_ground : P ≠ F.ground := by
          -- v ∈ ground かつ v ∉ P なので明らかに異なる
          intro h; have : v ∉ P := by simp [hPdef]
          have : v ∈ P := by simpa [h] using hvU
          (expose_names; exact this_1 this)
        have h_sets_in_F : F.sets s := by
          -- A ⊆ B & B ∈ F & B ≠ ground ⇒ A ∈ F
          exact F.down_closed (by simpa [hPdef] using hHave) hP_ne_ground
                (by
                  intro x hx; exact (Finset.mem_of_subset hsSub hx))
        -- s ⊆ P なので v ∉ s
        have hvnot : v ∉ s := by
          have : v ∉ P := by simp [hPdef]
          exact fun hv => this ((hsSub hv))
        -- trace の carrier 条件：s ⊆ trace.ground ∧ trace.sets s
        have hsub_trace : s ⊆ (F.traceIdeal v hne).ground := by
          simpa [hPdef] using hsSub
        -- 「delete を取り込む」定義部分で trace.sets s を得る
        have hsets_trace : (F.traceIdeal v hne).sets s := by
          -- `traceIdeal` の定義（del ∪ contr）から左側（del）を使う：
          --   v ∉ s かつ F.sets s ⇒ trace.sets s
          -- traceSets の左側の条件を使う
          unfold Ideal.traceIdeal Ideal.traceSets
          simp
          left
          exact ⟨h_sets_in_F, hvnot⟩
        -- 以上で carrier メンバーシップ
        exact (IdealFamily.SetFamily.mem_carrier_iff
                (SF := (F.traceIdeal v hne).toSetFamily)).mpr
              ⟨hsub_trace, hsets_trace⟩

    -- ★ 冪集合の NDS は 0：二分割（u を含む/含まない）で 2*deg = |F|
    have h_trace_nds_zero :
        (F.traceIdeal v hne).toSetFamily.nds = 0 := by
      classical
      -- 記法
      set SFt := (F.traceIdeal v hne).toSetFamily
      have hcar : SFt.carrier = P.powerset := trace_carrier_is_powerset
      -- 各 u∈P について，包含/非包含で対にして 2*degNat = |carrier|
      have h_two_deg_eq_card :
          ∀ u ∈ P, 2 * (SFt.degreeNat u) = SFt.carrier.card := by
        intro u huP
        classical
        -- Rewrite equalities on the powerset side using `hcar : SFt.carrier = P.powerset`.
        have hcar' : SFt.carrier = P.powerset := hcar
        -- degreeNat equals the size of the "contains u" filter
        have hdeg_filter :
            SFt.degreeNat u
              = (SFt.carrier.filter (fun s => u ∈ s)).card := by
          simp [IdealFamily.SetFamily.degreeNat, IdealFamily.SetFamily.S]
        -- Sum of the two filters equals the whole powerset
        have hsum_pow :
            (P.powerset.filter (fun s => u ∈ s)).card
              + (P.powerset.filter (fun s => u ∉ s)).card
              = (P.powerset).card := by
          simpa using
            (Finset.filter_card_add_filter_neg_card_eq_card
              (s := P.powerset) (p := fun s => u ∈ s))
        -- The two filtered parts have the same cardinality via s ↦ erase u / t ↦ insert u t
        have hswap_pow :
            (P.powerset.filter (fun s => u ∈ s)).card
              = (P.powerset.filter (fun s => u ∉ s)).card := by
          -- bijection between {s ⊆ P | u ∈ s} and {t ⊆ P | u ∉ t}
          apply Finset.card_bij (i := fun s hs => s.erase u)
          · intro s hs
            rcases Finset.mem_filter.mp hs with ⟨hsPow, huins⟩
            have hsSub : s ⊆ P := Finset.mem_powerset.mp hsPow
            refine Finset.mem_filter.mpr ?_
            constructor
            · -- (s.erase u) ⊆ P
              exact Finset.mem_powerset.mpr (by
                intro x hx; exact hsSub (Finset.mem_of_mem_erase hx))
            · -- u ∉ s.erase u
              simp
          · intro s₁ hs₁ s₂ hs₂ h
            -- both contain u; inserting u after erasing recovers the original
            have hu1 : u ∈ s₁ := (Finset.mem_filter.mp hs₁).2
            have hu2 : u ∈ s₂ := (Finset.mem_filter.mp hs₂).2
            have : insert u (s₁.erase u) = insert u (s₂.erase u) := by
              rw [h]
            -- `insert u (erase u s) = s` when `u ∈ s`
            simpa [Finset.insert_erase hu1, Finset.insert_erase hu2] using this
          · intro t ht
            -- take s = insert u t
            refine ⟨insert u t, ?mem_left, ?image_eq⟩
            · -- membership in the left filter (contains u)
              rcases Finset.mem_filter.mp ht with ⟨htPow, hunot⟩
              have htSub : t ⊆ P := Finset.mem_powerset.mp htPow
              refine Finset.mem_filter.mpr ?_
              constructor
              · -- insert u t ⊆ P
                exact Finset.mem_powerset.mpr (by
                  intro x hx
                  rcases Finset.mem_insert.mp hx with hx | hx
                  · simpa [hx] using huP
                  · exact htSub hx)
              · -- u ∈ insert u t
                simp
            · -- f (insert u t) = t
              -- (insert u t).erase u = t because u ∉ t
              have hunot : u ∉ t := (Finset.mem_filter.mp ht).2
              exact Finset.erase_insert hunot
        -- Conclude: 2 * |{contains u}| = |powerset|
        have hA_pow :
            2 * ((P.powerset.filter (fun s => u ∈ s)).card)
              = (P.powerset).card := by
          calc
            2 * ((P.powerset.filter (fun s => u ∈ s)).card)
                = ((P.powerset.filter (fun s => u ∈ s)).card)
                  + ((P.powerset.filter (fun s => u ∈ s)).card) := by
                    simp [two_mul]
            _   = ((P.powerset.filter (fun s => u ∈ s)).card)
                  + ((P.powerset.filter (fun s => u ∉ s)).card) := by
                    rw [hswap_pow]
            _   = (P.powerset).card := hsum_pow
        -- Rewrite back from powerset to `SFt.carrier`
        have hA :
            2 * ((SFt.carrier.filter (fun s => u ∈ s)).card)
              = SFt.carrier.card := by
          simpa [hcar'] using hA_pow
        -- Finally, substitute degreeNat = |{contains u}|
        simpa [hdeg_filter] using hA
      -- INT に上げて各 u の正規化次数が 0 だと分かる
      have h_each_u_norm0 :
          ∀ u ∈ P, (2 : ℤ) * (SFt.degree u) - SFt.numEdges = 0 := by
        intro u huP
        have hnat := h_two_deg_eq_card u huP
        -- 2 * degNat = |carrier| を ℤ に
        have : (2 : ℤ) * (SFt.degree u)
                = (SFt.carrier.card : ℤ) := by
          -- degree = zcast degreeNat
          simpa [SetFamily.degree_eq_zcast_degreeNat] using congrArg (fun k : ℕ => (k : ℤ)) hnat
        simpa [SetFamily.numEdges_eq_zcast_card] using
          sub_eq_zero.mpr this
      -- Σ_u normalizedDegreeAt(u) = Σ_u (2*deg - |F|) = 0 ⇒ nds = 0
      -- ground = P
      have h_ground : SFt.ground = P := rfl
      have hsum :
          ∑ u ∈ SFt.ground, ((2 : ℤ) * SFt.degree u - SFt.numEdges) = 0 := by
        -- 各項 0 の和
        have : ∀ u ∈ SFt.ground, ((2 : ℤ) * SFt.degree u - SFt.numEdges) = 0 := by
          intro u hu; exact h_each_u_norm0 u (by simpa [h_ground] using hu)
        -- sum of zeros is zero
        exact Finset.sum_eq_zero this
      -- Frankl 恒等式で nds = Σ_u normalizedDegree = 0
      have H := IdealFamily.SetFamily.sum_normalizedDegree_over_ground_eq_nds (SF := SFt)
      -- これで nds(trace) = 0
      --   （`H : Σ = nds` と `hsum : Σ = 0` の合成）
      calc
        SFt.nds = ∑ u ∈ SFt.ground, SFt.normalizedDegreeAt u := by exact H.symm
        _       = ∑ u ∈ SFt.ground, ((2 : ℤ) * SFt.degree u - SFt.numEdges) := by rfl
        _       = 0 := hsum
    -- 以上から nds(trace) ≤ 0
    simp [h_trace_nds_zero]

  exact le_trans h_nds_le_trace h_trace_le_zero

theorem nds_diff_deg1_groundErase_notin
  (v : α)
  (hvU   : v ∈ F.ground)
  (hdeg1 : F.toSetFamily.degreeNat v = 1)
  (hne   : (F.ground.erase v).Nonempty)
  (hnot  : ¬ F.sets (F.ground.erase v)) :
  F.toSetFamily.nds - (F.traceIdeal v hne).toSetFamily.nds
    = F.toSetFamily.normalizedDegreeAt v := by
  classical
  -- 記法
  set P : Finset α := F.ground.erase v with hPdef

  -- deg=1 ⇒ S v は単点（しかも ground がその要素）
  have hS_card1 : (F.toSetFamily.S v).card = 1 := by simpa using hdeg1
  have hUmem : F.ground ∈ F.toSetFamily.S v :=
    Finset.mem_filter.mpr ⟨Ideal.ground_mem_carrier F, hvU⟩
  obtain ⟨s0, hs0⟩ := Finset.card_eq_one.mp hS_card1
  have hg_eq_s0 : F.ground = s0 := by
    have : F.ground ∈ ({s0} : Finset (Finset α)) := by simpa [hs0] using hUmem
    simpa [Finset.mem_singleton] using this
  have hS_singleton : F.toSetFamily.S v = {F.ground} := by simpa [hg_eq_s0, hs0]

  -- contrCarrier も単点 {P}
  have h_contr_singleton : F.toSetFamily.contrCarrier v = {P} := by
    simp [IdealFamily.SetFamily.contrCarrier, hS_singleton, hPdef]

  -- 交差 (contr ∩ del) が空：P が delCarrier に入らないことを示せばよい
  have hP_not_in_del : P ∉ F.toSetFamily.delCarrier v := by
    -- delCarrier ならば carrier にも入るはずだが，hnot : ¬ F.sets P と矛盾
    intro hmem
    have hcar : P ∈ F.toSetFamily.carrier := (Finset.mem_filter.mp hmem).1
    have : F.sets P :=
      (IdealFamily.SetFamily.mem_carrier_iff (SF := F.toSetFamily)).mp hcar |>.2
    exact hnot this

  have h_inter_empty :
      (F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v)
        = (∅ : Finset (Finset α)) := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro t ht
    rcases Finset.mem_inter.mp ht with ⟨htC, htD⟩
    have : t = P := by simpa [h_contr_singleton, Finset.mem_singleton] using htC
    subst this
    exact hP_not_in_del htD

  -- 正確な差分恒等式から，交差ブロックが空なので和=0
  have hdiff := Ideal.nds_diff_trace_as_normdeg (F := F) (v := v) hvU hne
  simpa [h_inter_empty] using hdiff

end
end Ideal
--end IdealFamily
