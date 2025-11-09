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
import IdealFamily.NDSDiff2
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

/-- Wrapper around the deg=1 case: the difference collapses to `normalizedDegreeAt v`
    when `U\\{v} ∉ F`. -/
theorem nds_diff_deg1_groundErase_notin
  (v : α)
  (hvU   : v ∈ F.ground)
  (hdeg1 : F.toSetFamily.degreeNat v = 1)
  (hne   : (F.ground.erase v).Nonempty)
  (hnot  : ¬ F.sets (F.ground.erase v)) :
  F.toSetFamily.nds - (F.traceIdeal v hne).toSetFamily.nds
    = F.toSetFamily.normalizedDegreeAt v := by
    classical
    -- Step 1: S v has exactly one element, namely ground.
    have hS_card1 : (F.toSetFamily.S v).card = 1 := by
      -- degreeNat v is definitionally (S v).card
      have hdef : F.toSetFamily.degreeNat v = (F.toSetFamily.S v).card := by rfl
      exact hdef ▸ hdeg1
    have hS_singleton : F.toSetFamily.S v = {F.ground} := by
      let fc := Finset.card_eq_one.mp hS_card1
      obtain ⟨s0, hs0⟩ := fc
      -- ground ∈ S v（ground∈carrier かつ v∈ground）
      have hUmem : F.ground ∈ F.toSetFamily.S v := by
        have hcar :
            F.ground ∈ F.toSetFamily.carrier := by exact ground_mem_carrier F
          --  ⟨F.has_ground, by intro x hx; exact hx⟩
        exact Finset.mem_filter.mpr ⟨hcar, hvU⟩
      -- 一意性から s0 = ground
      --search_proof
      have hs0_eq : s0 = F.ground := by
        simp_all only [erase_nonempty, card_singleton, mem_singleton]
      -- S v = {s0} を経由して {ground} に書き換え
      have hS_eq_s0 : F.toSetFamily.S v = {s0} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        subst hs0_eq
        simp_all only [erase_nonempty, card_singleton, mem_singleton, implies_true, and_self]
      cases hs0_eq
      exact hS_eq_s0

    -- Step 2: contr ∩ del = ∅ なので、和項は 0。
    have hinter_empty :
        (F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v)
          = (∅ : Finset (Finset α)) := by
      classical
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      -- t ∈ contr, t ∈ del
      have htC : t ∈ F.toSetFamily.contrCarrier v := (Finset.mem_inter.mp ht).1
      have htA : t ∈ F.toSetFamily.delCarrier v := (Finset.mem_inter.mp ht).2
      -- contrCarrier v = (S v).image (erase v)
      unfold IdealFamily.SetFamily.contrCarrier at htC
      -- S v = {ground} で書き換え
      --cases hS_singleton
      rcases Finset.mem_image.mp htC with ⟨s, hs, hteq⟩
      have : s = F.ground := by
        subst hteq
        simp_all only [erase_nonempty, card_singleton, mem_singleton, mem_inter, image_singleton]--Finset.mem_singleton.mp hs
      cases this
      -- いま t = ground.erase v
      -- delCarrier は carrier.filter (v∉·) なので、t∈del ⇒ t∈carrier
      unfold IdealFamily.SetFamily.delCarrier at htA
      have hmem_carrier : F.ground.erase v ∈ F.toSetFamily.carrier := by
        subst hteq
        simp_all only [erase_nonempty, card_singleton, mem_singleton, mem_inter, image_singleton, mem_filter,
          mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true]
      -- carrier ∈ ↔ sets ∧ ⊆ground
      have hsets :
          F.sets (F.ground.erase v) := by
          let sm := (SetFamily.mem_carrier_iff F.toSetFamily).mp hmem_carrier |>.2
          exact sm

      exact hnot hsets

    -- Step 3: 差分恒等式に代入して和=0を潰す。
    have hdiff :=
      Ideal.nds_diff_trace_as_normdeg (F := F) (v := v) hvU hne
    have hsum0 :
        ∑ t ∈ (F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v),
            ((2 : ℤ) * (t.card : ℤ) - ((F.ground.card : ℤ) - 1)) = 0 := by
      simp_all only [card_singleton, sum_sub_distrib, sum_empty, sum_const, card_empty, zero_nsmul, sub_self, add_zero]--cases hinter_empty
    calc
      F.toSetFamily.nds - (F.traceIdeal v hne).toSetFamily.nds
          = F.toSetFamily.normalizedDegreeAt v
            + ∑ t ∈ (F.toSetFamily.contrCarrier v ∩ F.toSetFamily.delCarrier v),
                ((2 : ℤ) * (t.card : ℤ) - ((F.ground.card : ℤ) - 1)) := by
              exact hdiff
      _   = F.toSetFamily.normalizedDegreeAt v + 0 := by
              simp_all only [card_singleton, sum_sub_distrib, sum_empty, sum_const, card_empty, zero_nsmul, sub_self,
                add_zero]
      _   = F.toSetFamily.normalizedDegreeAt v := by
              ring



end
end Ideal
--end IdealFamily
