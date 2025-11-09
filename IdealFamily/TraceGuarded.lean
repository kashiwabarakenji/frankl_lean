/-
  IdealFamily/TraceGuarded.lean

  Purpose.
    Define the trace of an ideal at a vertex `v` as another ideal on the
    ground `U\{v}`, and relate its carrier with the A/B/C decomposition
    of the original family:
       A := carrier members not containing v
       B := carrier members containing v
       C := image of B by erasing v
    We show  carrier(trace_v(F)) = A ∪ C.

  Conventions.
    • Everything is purely set-theoretic over Finsets.
    • No UC/NEP assumptions are used.
    • Arithmetic is not used here; this module prepares structural identities.

  Tactic policy.
    – One import per line.
    – No `induction'`, no `simpa using`.
-/
import IdealFamily.Core
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset

namespace IdealFamily
namespace Ideal

open Finset
open scoped BigOperators

noncomputable section
variable {α : Type*} [DecidableEq α]
variable (F : Ideal α) [DecidablePred F.sets]
variable (v : α)

--local notation "SF" => F.toSetFamily

/- ********************  Helpers  ******************** -/

omit [DecidablePred F.sets] in
/-- If `t ⊆ U` and `v ∉ t`, then `t ⊆ U\\{v}`. -/
private lemma subset_erase_of_subset_and_not_mem
  {t : Finset α} (htU : t ⊆ F.ground) (hvnot : v ∉ t) :
  t ⊆ F.ground.erase v := by
  intro x hx
  have hxU : x ∈ F.ground := htU hx
  have hx_ne : x ≠ v := by
    intro h; have : v ∈ t := by cases h; exact hx
    exact False.elim (hvnot this)
  exact (Finset.mem_erase.mpr ⟨hx_ne, hxU⟩)

/- ********************  Trace predicate and Ideal  ******************** -/

/-- Trace membership predicate on `U\\{v}`:
    either a member already in `F` and *avoiding* `v`, or an erase-image
    of a member of `F` that *contains* `v`. -/
def traceSets (t : Finset α) : Prop :=
  (F.sets t ∧ v ∉ t)
  ∨ ∃ s : Finset α, F.sets s ∧ v ∈ s ∧ t = s.erase v

/-- The traced ideal at `v`, whose ground is `U\\{v}`.
    The `hne` witness guarantees nonemptiness of the new ground. -/
def traceIdeal (hne : (F.ground.erase v).Nonempty) : Ideal α :=
{ ground := F.ground.erase v
  sets := traceSets (F := F) v
  inc_ground := by
    intro t ht
    -- show: t ⊆ U\{v}
    cases ht with
    | inl hA =>
      -- t ∈ F and v ∉ t  ⇒  t ⊆ U\{v}
      have htU : t ⊆ F.ground := F.inc_ground hA.1
      exact subset_erase_of_subset_and_not_mem (F := F) (v := v) htU hA.2
    | inr hC =>
      -- t = s.erase v with s ∈ F and v ∈ s  ⇒  t ⊆ U\{v}
      rcases hC with ⟨s, hsF, hvs, ht⟩
      -- pick x∈t ⇒ x≠v ∧ x∈s ⇒ x∈U and x≠v ⇒ x∈U\{v}
      intro x hx
      have hx_in : x ∈ s := by
        -- from x∈s.erase v
        have : x ≠ v ∧ x ∈ s := (Finset.mem_erase.mp (by cases ht; exact hx ))
        exact this.2
      have hxU : x ∈ F.ground := (F.inc_ground hsF) hx_in
      have hx_ne : x ≠ v := by
        have : x ≠ v ∧ x ∈ s := (Finset.mem_erase.mp (by cases ht; exact hx))
        exact this.1
      exact (Finset.mem_erase.mpr ⟨hx_ne, hxU⟩)
  nonempty_ground := hne
  has_empty := by
    -- ∅ is in trace: left branch via F.has_empty and v ∉ ∅.
    left; exact And.intro F.has_empty (by exact Finset.notMem_empty v)
  has_ground := by
    -- ground' = U\{v} belongs to trace:
    -- if v∈U, use right branch with s=U; else use left branch with t=U.
    by_cases hvU : v ∈ F.ground
    · -- right branch, s = U
      right
      refine ⟨F.ground, F.has_ground, hvU, rfl⟩
    · -- left branch, t = U (since U\{v} = U when v∉U)
      left
      have hEq : F.ground.erase v = F.ground := by
        -- erasing a nonmember does nothing
        exact Finset.erase_eq_of_notMem hvU
      exact And.intro
        (by
           rw[hEq]
           exact F.has_ground
        )
        (by
          -- v ∉ U when hvU is false; transport along hEq
          simp_all only [not_false_eq_true, erase_eq_of_notMem, SetFamily.nonempty_ground]
        )

  down_closed := by
    -- Downward closure below the top ground' = U\{v}.
    intro A B hB hBne hAB
    -- Two cases: B from left branch (in F, avoids v) or from right branch (erase of some s∈F with v∈s).
    cases hB with
    | inl hleft =>
      -- B ∈ F, v∉B. Since B⊆U\{v}, B≠U as well; hence use F.down_closed on F.
      have hBsubU : B ⊆ F.ground := (F.inc_ground hleft.1)
      have hvnotB : v ∉ B := hleft.2
      have hBsubUerase : B ⊆ F.ground.erase v :=
        subset_erase_of_subset_and_not_mem (F := F) (v := v) hBsubU hvnotB
      -- From B ⊆ U\{v} and B ≠ U\{v}, we get B ≠ U automatically (in both cases v∈U or not).
      have hBneU : B ≠ F.ground := by
        intro h
        -- If B=U, then B ⊆ U\{v} implies U ⊆ U\{v} which is impossible when v∈U,
        -- and when v∉U we would have U=U\{v} but then hBne contradicts.
        -- We argue by membership of v:
        by_cases hvU : v ∈ F.ground
        · -- then v∈U but v∉B (hvnotB), contradiction with B=U
          have : v ∈ B := by cases h; exact hvU
          exact False.elim (hvnotB this)
        · -- v∉U ⇒ U\{v} = U, so hBne contradicts h
          have hEq : F.ground.erase v = F.ground := Finset.erase_eq_of_notMem hvU
          have : B = F.ground.erase v := by
            subst h
            simp_all only [not_false_eq_true, erase_eq_of_notMem, SetFamily.nonempty_ground, ne_eq, not_true_eq_false]
          exact False.elim (hBne (by cases this; rfl))
      -- Now use F.down_closed on F (below U):
      have hAinF : F.sets A :=
        F.down_closed (A := A) (B := B) hleft.1 hBneU hAB
      -- Also, v∉A because A⊆B and v∉B.
      have hvnotA : v ∉ A := by
        intro hvA; exact hvnotB (hAB hvA)
      exact Or.inl (And.intro hAinF hvnotA)
    | inr hright =>
      -- B = s.erase v with s∈F and v∈s.
      rcases hright with ⟨s, hsF, hvs, hBdef⟩
      -- A ⊆ B = s.erase v ⇒ A ⊆ s and v ∉ A.
      have hAsubS : A ⊆ s := by
        intro x hxA
        have hx_in : x ≠ v ∧ x ∈ s :=
          (Finset.mem_erase.mp (by cases hBdef; exact hAB hxA))
        exact hx_in.2
      have hvnotA : v ∉ A := by
        intro hvA
        -- If v∈A, then v∈B(=s.erase v), impossible since `mem_erase` requires v≠v.
        have hvB : v ∈ B := hAB hvA
        have hv_in_erase : v ∈ s.erase v := by
          cases hBdef
          exact hvB
        -- mem_erase ⇒ v ≠ v ∧ v ∈ s
        have hv_pair := Finset.mem_erase.mp hv_in_erase
        exact (hv_pair.1 rfl)

      -- Moreover, s ≠ U because otherwise B = U\{v} contradicts hBne.
      have hs_neU : s ≠ F.ground := by
        intro h
        -- B = s.erase v = U\{v}
        have : B = F.ground.erase v := by cases h; exact hBdef
        exact False.elim (hBne (by cases this; rfl))
      -- Apply downward closure in F to get A∈F, then use left branch (v∉A).
      have hAinF : F.sets A := F.down_closed (A := A) (B := s) hsF hs_neU hAsubS
      exact Or.inl (And.intro hAinF hvnotA) }

/- ********************  Carrier identity: A ∪ C  ******************** -/

/- The carrier of the traced ideal equals -/
-- Provide decidability for the trace predicate (used elsewhere via typeclass).
--instance traceSets_decidable : DecidablePred (traceSets (F := F) v) := fun t => Classical.dec _

-- Provide decidability for the .sets field of the constructed traceIdeal (depends on the nonempty witness).
instance traceIdeal_sets_decidable (hne : (F.ground.erase v).Nonempty) :
  DecidablePred ((F.traceIdeal v hne).sets) := fun t => Classical.dec (traceSets (F := F) v t)

/- ********************  Carrier identity: A ∪ C  ******************** -/
lemma trace_carrier_eq_del_union_contr
  (hne : (F.ground.erase v).Nonempty) :
  (F.traceIdeal v hne).toSetFamily.carrier
    = (F.toSetFamily.carrier.filter fun s => v ∉ s) ∪ ((F.toSetFamily.S v).image fun s => s.erase v) := by
  classical
  -- Unfold carrier on the trace side: (U\{v}).powerset.filter traceSets
  -- We prove mutual inclusion.
  apply Finset.ext
  intro t
  constructor
  · -- → : from trace-carrier to A ∪ C
    intro ht
    -- from filter membership, get: t ⊆ U\{v} and traceSets t
    have htPow : t ⊆ (F.ground.erase v) :=
      (SetFamily.mem_carrier_iff (SF := (F.traceIdeal v hne).toSetFamily)).mp ht |>.1
    have hTrace : traceSets (F := F) v t :=
      (SetFamily.mem_carrier_iff (SF := (F.traceIdeal v hne).toSetFamily)).mp ht |>.2
    -- split on traceSets
    cases hTrace with
    | inl hA =>
      -- Left branch: t∈F and v∉t.
      -- Show t∈A = carrier.filter (v∉).
      -- First show t∈carrier(SF):
      have htU : t ⊆ F.ground :=
        F.inc_ground hA.1
      have hMemCarrier : t ∈ F.toSetFamily.carrier :=
        (SetFamily.mem_carrier_iff (SF := F.toSetFamily)).mpr (And.intro htU hA.1)
      -- Now v∉t gives filter to delCarrier.
      have hMemDel : t ∈ (F.toSetFamily.carrier.filter fun s => v ∉ s) := by
        -- delCarrier = carrier.filter (v∉)
        -- We use `mem_filter` directly.
        exact Finset.mem_filter.mpr (And.intro hMemCarrier hA.2)
      -- Hence membership in A ⊆ A∪C.
      exact Finset.mem_union.mpr (Or.inl hMemDel)
    | inr hC =>
      -- Right branch: ∃ s∈F with v∈s and t = s.erase v.
      rcases hC with ⟨s, hsF, hvs, htdef⟩
      -- Show s ∈ S = carrier.filter (v∈).
      have hsU : s ⊆ F.ground := F.inc_ground hsF
      have hsMemCarrier : s ∈ F.toSetFamily.carrier :=
        (SetFamily.mem_carrier_iff (SF := F.toSetFamily)).mpr (And.intro hsU hsF)
      have hsMemS : s ∈ (F.toSetFamily.S v) := by
        -- S = carrier.filter (v∈)
        exact Finset.mem_filter.mpr (And.intro hsMemCarrier hvs)
      -- Then t ∈ image (erase v) of S, i.e., contrCarrier.
      have hMemContr : t ∈ ((F.toSetFamily.S v).image fun s => s.erase v) := by
        -- contrCarrier = (S v).image (fun s => s.erase v)
        -- Provide witness s and equality t = s.erase v.
        subst htdef
        simp_all only [SetFamily.inc_ground, mem_image]
        use s
      exact Finset.mem_union.mpr (Or.inr hMemContr)
  · -- ← : from A ∪ C to trace-carrier
    intro ht
    -- split membership
    cases (Finset.mem_union.mp ht) with
    | inl hA =>
      -- t ∈ A = carrier.filter (v∉)
      have hInCarrier : t ∈ F.toSetFamily.carrier := (Finset.mem_filter.mp hA).1
      have hvnot : v ∉ t := (Finset.mem_filter.mp hA).2
      -- From carrier membership, we get t ⊆ U and F.sets t.
      have htU  : t ⊆ F.ground := (SetFamily.mem_carrier_iff (SF := F.toSetFamily)).mp hInCarrier |>.1
      have htF  : F.sets t     := (SetFamily.mem_carrier_iff (SF := F.toSetFamily)).mp hInCarrier |>.2
      -- Show t ⊆ U\{v}:
      have htUerase : t ⊆ F.ground.erase v :=
        subset_erase_of_subset_and_not_mem (F := F) (v := v) htU hvnot
      -- Build trace-carrier membership: powerset+predicate
      have hPow : t ∈ (F.ground.erase v).powerset := by
        exact Finset.mem_powerset.mpr htUerase
      have hTrace : traceSets (F := F) v t := Or.inl (And.intro htF hvnot)
      -- Now filter
      exact
        (SetFamily.mem_carrier_iff (SF := (F.traceIdeal v hne).toSetFamily)).mpr
          (And.intro htUerase hTrace)
    | inr hC =>
      -- t ∈ C = image (erase v) of S
      rcases Finset.mem_image.mp hC with ⟨s, hsS, htdef⟩
      -- hsS : s ∈ S = carrier.filter (v∈)
      have hsCarrier : s ∈ F.toSetFamily.carrier := (Finset.mem_filter.mp hsS).1
      have hvs : v ∈ s := (Finset.mem_filter.mp hsS).2
      have hsU  : s ⊆ F.ground := (SetFamily.mem_carrier_iff (SF := F.toSetFamily)).mp hsCarrier |>.1
      have hsF  : F.sets s     := (SetFamily.mem_carrier_iff (SF := F.toSetFamily)).mp hsCarrier |>.2
      -- t = s.erase v  ⇒  t ⊆ U\{v}
      have htUerase : t ⊆ F.ground.erase v := by
        intro x hx
        -- translate membership via equality
        have hx' : x ∈ s.erase v := by
          subst htdef
          simp_all only [SetFamily.inc_ground, mem_union, mem_filter, mem_erase, ne_eq, not_true_eq_false,
            and_true, not_false_eq_true, or_true, mem_image, and_self]
        -- x ≠ v ∧ x ∈ s
        have hx_pair := Finset.mem_erase.mp hx'
        have hx_ne : x ≠ v := hx_pair.1
        have hx_s : x ∈ s := hx_pair.2
        -- x ∈ U
        have hxU : x ∈ F.ground := hsU hx_s
        -- hence x ∈ U\{v}
        exact (Finset.mem_erase.mpr ⟨hx_ne, hxU⟩)
      -- Build trace predicate (right branch)
      have hTrace : traceSets (F := F) v t := by
        right
        refine ⟨s, hsF, hvs, ?_⟩
        dsimp [traceIdeal]
        rw [← htdef]

      -- conclude membership in trace carrier
      exact
        (SetFamily.mem_carrier_iff (SF := (F.traceIdeal v hne).toSetFamily)).mpr
          (And.intro htUerase hTrace)

end
end Ideal
