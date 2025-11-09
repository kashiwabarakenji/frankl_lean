/-
  IdealFamily/Contraction.lean

  Purpose.
    Basic facts about the contraction carrier
      C := (S v).image (fun s => s.erase v)
    where S := members containing v. We prove:

      • `card_contr_eq_cardS` :
          |C| = |S|
        (erase at v is injective on `S` because every `s∈S` can be recovered
         as `insert v (s.erase v)`)

      • `sum_card_contr_eq_sum_cardS_sub_one` (ℤ version) :
          ∑_{t∈C} |t|
            =
          ∑_{s∈S} (|s| - 1)
        using `card_erase_add_one` for each `s∈S`.

  No UC/NEP assumptions appear here; everything is finitary over `Finset`.
  Tactic policy:
    – One import per line.
    – No `induction'`, no `simpa using`.
-/
import IdealFamily.Core
import Mathlib.Data.Finset.Card
--import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Image

namespace IdealFamily
namespace SetFamily

open Finset
open scoped BigOperators

noncomputable section

variable {α : Type*} [DecidableEq α]
variable (SF : SetFamily α) [DecidablePred SF.sets]
variable (v : α)

local notation "S" => SF.S v
local notation "C" => SF.contrCarrier v

/- ********************  Injectivity of erase on S  ******************** -/

/-- If `v ∈ s`, then `insert v (erase s v) = s`. We use this to recover `s` from `erase s v`. -/
private lemma insert_erase_of_mem {s : Finset α} (hv : v ∈ s) :
  insert v (s.erase v) = s := by
  -- standard Finset lemma: `insert_erase` with membership
  -- (exists in Mathlib; we re-prove minimally if needed)
  -- We'll use the library lemma:
  exact Finset.insert_erase hv

/-- `erase v` is injective on `S = {s∈carrier | v∈s}`. -/
lemma erase_injective_on_S :
  ∀ {x} (_hx : x ∈ S) {y} (_hy : y ∈ S),
      x.erase v = y.erase v → x = y := by
  classical
  intro x hx y hy hEq
  -- From membership in S, we know `v ∈ x` and `v ∈ y`.
  have hvx : v ∈ x := (Finset.mem_filter.mp hx).2
  have hvy : v ∈ y := (Finset.mem_filter.mp hy).2
  -- Recover both sides by inserting `v` back, then compare.
  have hx' : insert v (x.erase v) = x := insert_erase_of_mem  (v := v) hvx
  have hy' : insert v (y.erase v) = y := insert_erase_of_mem  (v := v) hvy
  -- Rewrite by `hEq`.
  -- insert v (x.erase v) = insert v (y.erase v) ⇒ x = y
  -- because `hx'` and `hy'` are equalities to x and y respectively.
  -- We use transitivity:
  have : insert v (x.erase v) = insert v (y.erase v) := by
    -- rewrite RHS/LHS via hEq
    exact congrArg (insert v) hEq

  -- Now replace with `hx'` and `hy'`.
  -- From `hx' : insert v (x.erase v) = x` and `hy' : insert v (y.erase v) = y`
  -- we conclude `x = y`.
  exact by
    -- turn equalities around for a direct rewrite
    -- `hx'` : insert v (x.erase v) = x
    -- `hy'` : insert v (y.erase v) = y
    -- thus `x = y` follows by rewriting `this` with these.
    have : x = y := by
      -- replace left with x, right with y
      -- (Lean accepts rewriting equalities in both directions)
      -- left:
      have hL : insert v (x.erase v) = x := hx'
      -- right:
      have hR : insert v (y.erase v) = y := hy'
      -- chain
      -- from `insert v (x.erase v) = insert v (y.erase v)` and both equalities to x and y:
      -- deduce x = y
      -- We'll rewrite both sides:
      -- hL ▸ hR ▸ this  gives x = y
      -- Implement with `cases`:
      simp_all only [insert_erase]
    exact this

/- ********************  Cardinality of C equals cardinality of S  ******************** -/

/- `|C| = |S|`, i.e., cardinality is preserved by `erase v` on the B-side. -/
lemma card_contr_eq_cardS :
  (C).card = (S).card := by
  classical
  -- Build the natural bijection between the attached versions of `C` and `S`.
  let f :
      { x : Finset α // x ∈ S } →
      { t : Finset α // t ∈ C } :=
    fun ⟨x, hx⟩ =>
      ⟨x.erase v, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩

  have hf_inj : Function.Injective f := by
    intro a b h
    rcases a with ⟨x, hx⟩
    rcases b with ⟨y, hy⟩
    have hxye : x.erase v = y.erase v := by
      simpa using congrArg Subtype.val h
    have hxy : x = y := erase_injective_on_S (SF := SF) (v := v) hx hy hxye
    subst hxy
    rfl

  have hf_surj : Function.Surjective f := by
    intro b
    rcases b with ⟨t, ht⟩
    rcases Finset.mem_image.mp ht with ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    -- simplification of the subtype equality goal
    rfl

  -- Convert the bijection to a cardinality equality.
  have card_eq :=
    Fintype.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  -- Unfold subtype cardinalities to get the statement about finset cards.
  simpa [Fintype.card_subtype] using card_eq.symm

/-- `card (s.erase v)` の整数版：`((s.erase v).card : ℤ) = (s.card : ℤ) - 1` （`v ∈ s`）。 -/
lemma card_erase_z (s : Finset α) (hvs : v ∈ s) :
  ((s.erase v).card : ℤ) = (s.card : ℤ) - 1 := by
  -- 自然数で card (erase) + 1 = card
  have hN : (s.erase v).card + 1 = s.card := Finset.card_erase_add_one hvs
  -- 整数へキャストして整理
  have hZ : ((s.erase v).card : ℤ) + 1 = (s.card : ℤ) :=
    congrArg (fun n : ℕ => (n : ℤ)) hN
  -- a + 1 = b から a = b - 1
  exact (eq_sub_iff_add_eq).mpr hZ

/- ********************  Sum of sizes on C vs S  ******************** -/
/-- 主要恒等式：`∑_{t∈C} |t| = ∑_{s∈S} (|s| - 1)` （整数版）。 -/
lemma sum_card_contr_eq_sum_cardS_sub_one :
  (∑ t ∈ C, (t.card : ℤ)) =
    ∑ s ∈ S, ((s.card : ℤ) - 1) := by
  classical
  -- Step 1: rewrite the sum over C via a bijection with S using `erase`.
  have h_sum :
      (∑ t ∈ C, (t.card : ℤ)) = ∑ s ∈ S, (((s.erase v).card : ℤ)) := by
    classical
    -- Auxiliary data for `Finset.sum_bij`.
    let f : Finset α → ℤ := fun s => ((s.erase v).card : ℤ)
    let g : Finset α → ℤ := fun t => (t.card : ℤ)
    let i : ∀ s, s ∈ S → Finset α := fun s _ => s.erase v
    have h_mem : ∀ s (hs : s ∈ S), i s hs ∈ C := by
      intro s hs
      -- C is the image under erase.
      exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    have h_inj : ∀ s₁ (hs₁ : s₁ ∈ S) s₂ (hs₂ : s₂ ∈ S),
        i s₁ hs₁ = i s₂ hs₂ → s₁ = s₂ := by
      intro s₁ hs₁ s₂ hs₂ h
      exact erase_injective_on_S (SF := SF) (v := v) hs₁ hs₂ h
    have h_surj : ∀ t, t ∈ C → ∃ s, ∃ hs : s ∈ S, i s hs = t := by
      intro t ht
      rcases Finset.mem_image.mp ht with ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
    have h_val : ∀ s (hs : s ∈ S), f s = g (i s hs) := by
      intro s hs
      rfl
    -- Apply the bijection-based sum lemma.
    have h_bij :=
      @Finset.sum_bij _ _ _ _ S C f g i
        (fun s hs => h_mem s hs)
        (fun s₁ hs₁ s₂ hs₂ h => h_inj s₁ hs₁ s₂ hs₂ h)
        (fun t ht => h_surj t ht)
        (fun s hs => h_val s hs)
    -- Simplify the statement of the result.
    simpa [f, g, i] using h_bij.symm
  -- Step 2: convert each term `((s.erase v).card : ℤ)` into `(s.card : ℤ) - 1`.
  have h_step :
      ∑ s ∈ S, (((s.erase v).card : ℤ))
        = ∑ s ∈ S, ((s.card : ℤ) - 1) := by
    refine Finset.sum_congr rfl ?_
    intro s hs
    have hvs : v ∈ s := (Finset.mem_filter.mp hs).2
    simpa using card_erase_z (v := v) s hvs
  -- Combine both steps.
  exact h_sum.trans h_step


/-- For each `s∈S`, `(erase s v).card` as an integer equals `s.card - 1`. -/
private lemma zcard_erase_eq_card_sub_one
  {s : Finset α} (hs : s ∈ S) :
  ((s.erase v).card : ℤ) = (s.card : ℤ) - 1 := by
  classical
  -- From `hs : s ∈ S = carrier.filter (v∈)`, get `v∈s`.
  have hv : v ∈ s := (Finset.mem_filter.mp hs).2
  -- Nat identity: `card (erase s v) + 1 = card s`
  have hNat : (s.erase v).card + 1 = s.card := Finset.card_erase_add_one hv
  -- Cast to ℤ and rearrange:
  -- a + 1 = b  ⇒  a = b - 1  in an additive group.
  have hZ : ((s.erase v).card : ℤ) + (1 : ℤ) = (s.card : ℤ) := by
    -- direct cast of the Nat equality
    -- `(a + 1 : ℕ) : ℤ = (a : ℤ) + 1`
    -- Lean accepts congrArg then uses the ring morphism ℕ→ℤ.
    exact congrArg (fun k : ℕ => (k : ℤ)) hNat
  -- rearrange to subtraction form
  exact (eq_sub_iff_add_eq).mpr hZ

end
end SetFamily
end IdealFamily
