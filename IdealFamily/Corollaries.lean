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

/- If NDS(F) ≤ 0 and U≠∅, there exists a rare vertex in U. -/
theorem exists_rare_of_nds_le_zero
  (hneU : F.ground.Nonempty)
  (hN :  (F.toSetFamily).nds ≤ 0) :
  ∃ v ∈ F.ground, F.rare v := by
  classical
  -- Use Σ normdeg = nds. If all terms were > 0, the sum would be > 0.
  -- Hence some term must be ≤ 0.
  -- Step 1: identify the sum identity.
  have Hsum :
      ∑ v ∈ F.ground,  (F.toSetFamily).normalizedDegreeAt v =  (F.toSetFamily).nds :=
    SetFamily.sum_normalizedDegree_over_ground_eq_nds (SF := (F.toSetFamily))
  -- Suppose by contradiction that all terms are > 0.
  -- Then by `Int.add_one_le_iff` we get 1 ≤ each term, hence the sum ≥ |U|.
  -- But |U| > 0, contradicting hN.
  -- We build the existential directly without classical contradiction.
  -- If not (∃ v∈U, nd(v) ≤ 0), then ∀ v∈U, 0 < nd(v). Hence 1 ≤ nd(v) for each v.
  -- Sum ≥ |U| • 1 = |U|, which is > 0 (U nonempty).
  -- Therefore, there exists v with nd(v) ≤ 0.
  by_contra hno
  -- hno : ¬ ∃ v∈U, nd(v) ≤ 0  ⇒  ∀ v∈U, 0 < nd(v)
  have hpos_all :
      ∀ v ∈ F.ground, 0 <  (F.toSetFamily).normalizedDegreeAt v := by
    intro v hv
    have : ¬ ( (F.toSetFamily).normalizedDegreeAt v ≤ 0) := by
      -- from hno
      exact fun hle => hno ⟨v, hv, hle⟩
    -- total order on ℤ
    exact Int.lt_of_not_ge this
    -- Provide directly: on ℤ, not (x ≤ 0) ⇒ 0 < x
    -- Lean lemma: `lt_of_le_of_ne` is not needed; we use trichotomy.
  -- The previous attempt tried to derive `0 < x` from `¬(x ≤ 0)`.
  -- On ℤ's linear order: `¬(x ≤ 0)` is equivalent to `0 < x`.
  -- Let's restate cleanly:
  clear hpos_all
  have hpos_all :
      ∀ v ∈ F.ground, 0 <  (F.toSetFamily).normalizedDegreeAt v := by
    intro v hv
    have : ¬ ( (F.toSetFamily).normalizedDegreeAt v ≤ 0) := by exact fun hle => hno ⟨v, hv, hle⟩
    exact lt_of_le_of_ne (by exact le_of_lt (by exact Int.lt_of_not_ge this)) (by
    simp_all only [SetFamily.nonempty_ground, not_exists, not_and, not_le, ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only [lt_self_iff_false])

  -- The above is too condensed; instead, we use a standard equivalence:
  -- On integers, `0 < x ↔ 1 ≤ x` (via `Int.add_one_le_iff`). We'll use that forward.
  -- We only need `1 ≤ nd(v)` to lower bound the sum.
  -- So we switch to a simpler derivation:

  clear hpos_all
  have hone_le :
      ∀ v ∈ F.ground, (1 : ℤ) ≤  (F.toSetFamily).normalizedDegreeAt v := by
    intro v hv
    -- `0 < nd(v)` ⇒ `1 ≤ nd(v)` on ℤ by `Int.add_one_le_iff` (rewritten).
    -- We re-obtain `0 < nd(v)` as explained above from `hno`.
    have hpos : 0 <  (F.toSetFamily).normalizedDegreeAt v := by
      have : ¬ ( (F.toSetFamily).normalizedDegreeAt v ≤ 0) := by exact fun hle => hno ⟨v, hv, hle⟩
      -- linear order: not (x ≤ 0) ⇒ 0 < x
      exact Int.lt_of_not_ge this
    -- now 0 < x ⇒ 1 ≤ x
    have : (1 : ℤ) ≤  (F.toSetFamily).normalizedDegreeAt v := by
      -- `Int.add_one_le_iff` : a + 1 ≤ b ↔ a < b
      -- with a=0, b=nd(v) gives 1 ≤ nd(v) ↔ 0 < nd(v)
      exact hpos
    -- We already have hpos; rearrange:
    exact this
  -- Lower bound the sum by |U| • 1 = |U|.
  have hsum_ge :
      (F.ground.card : ℤ)
        ≤ ∑ v ∈ F.ground,  (F.toSetFamily).normalizedDegreeAt v := by
    -- sum_le_sum-like in the other direction; we prove
    --   ∀v∈U, 1 ≤ nd(v), hence  Σ 1 ≤ Σ nd(v)
    -- `sum_const` on ℤ: Σ 1 = card • 1
    have hsum1 :
        ∑ _v ∈ F.ground, (1 : ℤ) = F.ground.card • (1 : ℤ) := by
      exact Finset.sum_const (b := (1 : ℤ)) (s := F.ground)
    -- convert nsmul-one to card (as ℤ)
    have hcard :
        F.ground.card • (1 : ℤ) = (F.ground.card : ℤ) := by
      exact nsmul_one _
    -- use sum_le_sum_of_nonneg? We can directly apply monotonicity termwise:
    have hmono :
        ∀ v ∈ F.ground, (1 : ℤ) ≤  (F.toSetFamily).normalizedDegreeAt v := by
      intro v hv; exact hone_le v hv
    -- conclude
    calc
      (F.ground.card : ℤ)
          = F.ground.card • (1 : ℤ) := by
           simp_all only [SetFamily.nonempty_ground, not_exists, not_and, implies_true, sum_const, Int.nsmul_eq_mul,
             mul_one]
      _   = ∑ _v ∈ F.ground, (1 : ℤ) := by
           simp_all only [SetFamily.nonempty_ground, not_exists, not_and, implies_true, sum_const, Int.nsmul_eq_mul,
             mul_one]
      _   ≤ ∑ v ∈ F.ground,  (F.toSetFamily).normalizedDegreeAt v := by
            refine Finset.sum_le_sum ?mono
            intro v hv
            exact hmono v hv


  -- But the RHS equals nds(F); combine with hN ≤ 0 and U≠∅ to force contradiction.
  have hsum_eq : ∑ v ∈ F.ground,  (F.toSetFamily).normalizedDegreeAt v =  (F.toSetFamily).nds :=
    SetFamily.sum_normalizedDegree_over_ground_eq_nds (SF := (F.toSetFamily))
  have hposU : 0 < (F.ground.card : ℤ) := by
    -- U nonempty ⇒ card > 0 ⇒ cast > 0
    have : 0 < F.ground.card := Finset.card_pos.mpr hneU
    -- cast to ℤ
    exact Int.natCast_pos.mpr this

  -- Combine inequalities: (card : ℤ) ≤ Σ nd = nds ≤ 0, contradicting card>0.
  -- Hence ∃ rare vertex.
  have : (F.ground.card : ℤ) ≤  (F.toSetFamily).nds := by
    simp_all only [SetFamily.nonempty_ground, not_exists, not_and, Int.natCast_pos, card_pos]--

  -- now compare with hN
  have : (F.ground.card : ℤ) ≤ 0 := le_trans this hN
  exact absurd (lt_of_le_of_lt this hposU) (lt_irrefl _)

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
    -- As in the deg1-wrapper above: ground ∈ S v and uniqueness forces equality.
    -- (We re-prove it here for self-containment.)
    -- Show `ground ∈ S v`.
    have hUmem : F.ground ∈ F.toSetFamily.S v := by
      have hcar : F.ground ∈ F.toSetFamily.carrier := Ideal.ground_mem_carrier F
      exact Finset.mem_filter.mpr ⟨hcar, hvU⟩
    -- Now use `card_eq_one` to pin the unique element.
    obtain ⟨s0, hs0⟩ := Finset.card_eq_one.mp hS_card1
    -- `s0` is the unique member of `S v`.
    have : s0 = F.ground := by
      -- since `ground ∈ S v`, the unique element must be `ground`
      have : s0 ∈ F.toSetFamily.S v := by simp [hs0]
      -- elements of `S v` are exactly those in carrier with `v∈·`
      -- Uniqueness forces `s0 = ground`.
      -- Prove by contradiction: if `s0 ≠ ground`, downward-closure of `s0` would give `{v} ∈ F`,
      -- hence two distinct sets containing `v` (`s0` and `ground`), contradicting `deg=1`.
      by_cases hEq : s0 = F.ground
      · exact hEq
      · -- `s0 ∈ carrier` and `v ∈ s0`
        have hs0_car : s0 ∈ F.toSetFamily.carrier := (Finset.mem_filter.mp this).1
        have hv_in : v ∈ s0 := (Finset.mem_filter.mp this).2
        -- membership gives `F.sets s0`
        have hsets : F.sets s0 := (IdealFamily.SetFamily.mem_carrier_iff (SF := F.toSetFamily)).mp hs0_car |>.2
        -- downward-closed below top: if `s0 ≠ ground` and `{v} ⊆ s0`, then `{v} ∈ F`
        have hsing : F.sets ({v} : Finset α) := by
          apply F.down_closed hsets hEq
          exact Finset.singleton_subset_iff.mpr hv_in
        -- then `S v` contains both `ground` and `{v}`, contradiction to card=1
        have : 2 ≤ (F.toSetFamily.S v).card := by
          -- `{v}` and `ground` are distinct and both belong to `S v`
          have h1 : ({v} : Finset α) ∈ F.toSetFamily.S v := by
            have hcar :
              ({v} : Finset α) ∈ F.toSetFamily.carrier := by
                -- `{v} ⊆ ground` (since v ∈ ground) and `sets {v}`
                have hsub : ({v} : Finset α) ⊆ F.ground := Finset.singleton_subset_iff.mpr hvU
                exact (IdealFamily.SetFamily.mem_carrier_iff (SF := F.toSetFamily)).mpr ⟨hsub, hsing⟩
            exact Finset.mem_filter.mpr ⟨hcar, by simp⟩
          have h2 : F.ground ∈ F.toSetFamily.S v := hUmem
          have hneq : ({v} : Finset α) ≠ F.ground := by
            -- since v ∈ ground and ground.Nonempty with more than singleton would make a contradiction,
            -- but simpler: if `{v} = ground` then `ground.erase v = ∅`, contradicting `hne`.
            intro hcontra
            have : (F.ground.erase v) = (∅ : Finset α) := by simp_all only [erase_nonempty, card_singleton,
              mem_singleton, not_true_eq_false, P]
            have : (∅ : Finset α).Nonempty := by simp_all only [Finset.not_nonempty_empty, P]
            cases this
            simp_all only [Finset.not_nonempty_empty, P]
          -- two distinct members ⇒ card ≥ 2
          simp_all only [erase_nonempty, card_singleton, mem_singleton, not_true_eq_false, P]
        simp [hS_card1] at this
      -- discharge impossible branch (already contradicted)
    -- Finally, rewrite `S v = {s0}` via `hs0` and substitute `s0 = ground`.
    have hS_eq_s0 : F.toSetFamily.S v = {s0} := by simp [hs0]
    simpa [this] using hS_eq_s0

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
    -- `contr` is `{P}`, and `P ∈ del`, so intersection is exactly `{P}`.
    apply Finset.ext
    intro t
    constructor
    · intro ht
      have htC : t ∈ F.toSetFamily.contrCarrier v := (Finset.mem_inter.mp ht).1
      have htA : t ∈ F.toSetFamily.delCarrier v := (Finset.mem_inter.mp ht).2
      -- from `contr = {P}` we get `t = P`
      have : t = P := by simpa [h_contr_singleton] using Finset.mem_singleton.mp (by
        -- show t ∈ {P}
        have : t ∈ (F.toSetFamily.contrCarrier v) := htC
        simpa [h_contr_singleton] using this)
      simp [this]
    · intro ht
      -- t = P
      have : t = P := Finset.mem_singleton.mp ht
      -- and P is in both
      simp [this, h_contr_singleton]
      subst this
      simp_all only [erase_nonempty, card_singleton, mem_singleton, P]

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
        intro x hx;
        have : x = u := by simpa [Finset.mem_singleton] using hx
        rw [←this] at hu
        exact hu

      have hP_ne_ground : P ≠ F.ground := by
        -- because `v ∈ ground` but `v ∉ P`
        have : v ∉ P := by simp [hPdef]
        intro hcontra
        have : v ∈ P := by simpa [hcontra] using hvU
        (expose_names; exact this_1 this)
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
    · sorry
    ·
      rcases Finset.mem_insert.mp ht' with ht0 | ht1
      · sorry
      · rcases Finset.mem_image.mp ht1 with ⟨u, huP, rfl⟩
        exact h_singleton_car huP

  -- Compute `|T| = P.card + 2`.
  have h_inj_singleton : Function.LeftInverse (fun (s : Finset α) => Classical.choice (by sorry)) (fun u => ({u} : Finset α)) := by
    -- We don't need a full left-inverse; we only need that `u ↦ {u}` is injective.
    -- Use the standard fact: `Finset.singleton` is injective.
    sorry
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
      have : ({u} : Finset α).Nonempty := by simp
      sorry

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
      have : v ∉ ({u} : Finset α) := by sorry
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
    sorry

  -- Hence: `|carrier| ≥ |T| = P.card + 2`.
  have hEdges_ge :
      (P.card + 2) ≤ F.toSetFamily.carrier.card := by sorry
    --Finset.card_le_card hT_sub

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
      simp [sub_eq_add_neg,  add_assoc]
      sorry
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
  have h_trace_le_zero :
      (F.traceIdeal v hne).toSetFamily.nds ≤ 0 := by
    sorry

  exact le_trans h_nds_le_trace h_trace_le_zero



end
end Ideal
--end IdealFamily
