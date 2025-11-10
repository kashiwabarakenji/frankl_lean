import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.FinSupp.Basic
import IdealFamily.Core
import IdealFamily.TraceGuarded
import IdealFamily.Contraction
import IdealFamily.NDSDiff
import IdealFamily.Corollaries      -- 基底: |U|=1 の非正など
import IdealFamily.Proofs
import IdealFamily.FranklRare -- レア頂点の存在: ideal_version_of_frankl_conjecture
import LeanCopilot

namespace IdealFamily
namespace Ideal

open scoped BigOperators
open Finset

variable {α : Type*} [DecidableEq α]
variable (F : Ideal α)


/-! ### 小補題（カード計算など、依存なしで使える形に） -/

private lemma card_erase_eq_of_card_succ (n : ℕ)
  {F : Ideal α} (h : F.ground.card = Nat.succ n) (v : α) (hv : v ∈ F.ground) :
  (F.ground.erase v).card = n := by
  -- card (erase v) + 1 = card ground = n+1
  have h1 : (F.ground.erase v).card + 1 = F.ground.card := card_erase_add_one hv
  have h2 : (F.ground.erase v).card + 1 = Nat.succ n := by
    exact Eq.trans h1 h
  have h3 : Nat.succ ((F.ground.erase v).card) = Nat.succ n := by
    simpa [Nat.succ_eq_add_one] using h2
  exact Nat.succ.inj h3

private lemma erase_nonempty_of_card_succ_succ (n : ℕ)
  {F : Ideal α} (h : F.ground.card = Nat.succ (Nat.succ n)) (v : α) (hv : v ∈ F.ground) :
  (F.ground.erase v).Nonempty := by
  -- card (erase v) = n.succ ≥ 1 → Nonempty
  have hcard : (F.ground.erase v).card = Nat.succ n := by
    apply card_erase_eq_of_card_succ (F := F) (h := by
      --  ground.card = (n.succ).succ なので、(erase).card = (n.succ)
      exact h) --(show F.ground.card = Nat.succ (Nat.succ n) from h))
    exact hv
  have hpos : 0 < (F.ground.erase v).card := by
    simp [hcard] --using Nat.succ_pos n
  exact (card_pos.mp hpos)

/-! ### |U| = 1 のときの NDS を直接計算して 0 とする補題 -/
private lemma nds_eq_zero_card_one
  {G : Ideal α} [DecidablePred G.sets]
  (h1 : G.ground.card = 1) :
  G.toSetFamily.nds = 0 := by
  classical
  -- ground = {a}
  obtain ⟨a, hground⟩ := Finset.card_eq_one.mp h1
  -- powerset({a}) = {∅, {a}}
  have hPow : G.ground.powerset = ({∅, ({a} : Finset α)} : Finset (Finset α)) := by
    simp [hground]  -- `simp` で powerset {a} = {∅, {a}}
    exact rfl
  -- `carrier ⊆ powerset = {∅,{a}}`
  have hSub1 :
      G.toSetFamily.carrier ⊆ ({∅, ({a} : Finset α)} : Finset (Finset α)) := by
    intro s hs
    have hs' :=
      (IdealFamily.SetFamily.carrier_subset_powerset (SF := G.toSetFamily)) hs
    simpa [hPow] using hs'
  -- `∅ ∈ carrier` と `ground ∈ carrier`
  have hMemEmpty : (∅ : Finset α) ∈ G.toSetFamily.carrier :=
    Ideal.empty_mem_carrier (F := G)
  have hMemGround : ({a} : Finset α) ∈ G.toSetFamily.carrier := by
    simpa [hground] using Ideal.ground_mem_carrier (F := G)
  -- `{∅,{a}} ⊆ carrier`
  have hSub2 :
      ({∅, ({a} : Finset α)} : Finset (Finset α)) ⊆ G.toSetFamily.carrier := by
    intro s hs
    have : s = ∅ ∨ s = {a} := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hs
    cases this with
    | inl h => simpa [h] using hMemEmpty
    | inr h => simpa [h] using hMemGround
  -- 等号：carrier = {∅,{a}}
  have hCarrier :
      G.toSetFamily.carrier = ({∅, ({a} : Finset α)} : Finset (Finset α)) := by
    exact Subset.antisymm hSub1 hSub2
  -- 以上から NDS を直接計算
  -- totalSize は |∅| + |{a}| = 0 + 1、edge 数は 2、|U| は 1
  have : G.toSetFamily.nds
      = (2 : ℤ) * ((G.toSetFamily.carrier.sum (fun s => s.card)) : ℤ)
        - ((G.toSetFamily.carrier.card : ℤ)) * (G.ground.card : ℤ) := by
    simp [IdealFamily.SetFamily.nds,
          IdealFamily.SetFamily.totalSize_eq_zcast_sum_card,
          IdealFamily.SetFamily.numEdges_eq_zcast_card]
  -- 具体的に簡約
  simp [hCarrier, hground, this, Finset.card_singleton]  -- 結果は 0
  exact rfl

/-! ### 論文準拠：レア頂点から NDS ≤ 0 を示す別証明 -/

variable (F : Ideal α) [DecidablePred F.sets]

/--
`via rare` 版の主定理：
**レア頂点の存在を仮定（または既存の定理で得て）し、マイナーの帰納と合成式で `F.nds ≤ 0` を示す。**

この証明は、既存の構造的証明（レア頂点に依存しない版）とは独立にコンパイルできます。
-/
theorem nds_nonpos_via_rare : F.nds ≤ 0 := by
  classical
  -- `P n := ∀ {G}, G.ground.card = n → G.nds ≤ 0`
  refine
    (Nat.rec (motive := fun n => ∀ {G : Ideal α} [DecidablePred G.sets], G.ground.card = n → G.nds ≤ 0)
      -- base: n = 0 （Ideal では ground.Nonempty のため起きないが、防御的に閉じる）
      (by
        intro G _ h0
        -- ground = ∅ と Nonempty の矛盾から任意命題が従う（あるいは別途 0 ケースの補題があればそれを使う）
        have hZ : G.ground = (∅ : Finset α) := card_eq_zero.mp (by simpa using h0)
        cases G.nonempty_ground with
        | _ =>
          have : False := by
            -- Nonempty と 空集合の矛盾
            simpa [hZ] using G.nonempty_ground
          exact this.elim)
      -- step: n → n+1
      (by
        intro n IH G _ hS
        -- n による分岐：n = 0（⇒ |U|=1 は別途の基底補題）、n = k+1（⇒ |U|≥2 の本体）
        cases hn:n with
        | zero =>
          -- |U| = 1 の基底：直接計算で NDS = 0
          --change G.toSetFamily.nds ≤ 0
          have h1 : G.ground.card = 1 := by
            subst hn
            simp_all only [card_eq_zero, Nat.succ_eq_add_one, zero_add]
          have h0 : G.toSetFamily.nds = 0 := nds_eq_zero_card_one (α := α) (G := G) h1
          exact le_of_eq h0
        | succ k =>
          -- |U| = k+2 ≥ 2
          -- レア頂点の存在（FranklRare 側の主張）を取得
          obtain ⟨v, hvU, hRare⟩ := ideal_version_of_frankl_conjecture (F := G)
          -- ケース分け：{v} ∈ F か？
          by_cases hSing : G.sets {v}
          · /- {v} が超辺のとき： deletion / contraction の合成式で分解し、両マイナーに IH、レアで最後の項 ≤ 0 -/
            -- deletion' と contraction の定義が存在しないため、この部分は未実装
            --ここはdeg1ではない。contractionで、idealが閉じている。よって帰納法が使える。
            -- 既存補題があるかどうか調べる。
            sorry
          · /- {v} が超辺でない：イデアル性から自動的に `deg(v)=1`。さらに `U\\{v}` の有無で分岐 -/
            have hNotSing : ¬ G.sets {v} := hSing
            have deg1 : G.toSetFamily.degreeNat v = 1 := by
                -- degreeNat v = |S(v)| = |{s ∈ carrier | v ∈ s}|
                -- {v}∉F より、v∈s∈F ⇒ s=ground を示す
                have hSvEqGround : G.toSetFamily.S v = {G.ground} := by
                  apply Finset.ext
                  intro s
                  simp only [SetFamily.S, Finset.mem_filter, Finset.mem_singleton]
                  constructor
                  · intro ⟨hsCarrier, hvs⟩
                    -- s ∈ carrier かつ v ∈ s
                    -- carrier の定義より s ∈ powerset(ground) かつ G.sets s
                    have hsSet : G.sets s := by
                      exact (SetFamily.mem_carrier_iff (SF := G.toSetFamily)).mp hsCarrier |>.2
                    -- s ≠ ground と仮定すると矛盾を導く
                    by_cases hEq : s = G.ground
                    · exact hEq
                    · -- s ≠ ground のとき、下方閉性より {v} ∈ F
                      have : G.sets {v} := by
                        apply G.down_closed hsSet hEq
                        exact Finset.singleton_subset_iff.mpr hvs
                      exact absurd this hNotSing
                  · intro hEq
                    subst hEq
                    constructor
                    · -- ground ∈ carrier
                      exact Ideal.ground_mem_carrier G
                    · -- v ∈ ground
                      exact hvU
                -- |S(v)| = |{ground}| = 1
                -- degreeNat v の定義を展開
                show (G.toSetFamily.S v).card = 1
                rw [hSvEqGround]
                simp

            -- `U\\{v}` がメンバーか？
            by_cases hHaveUminus : G.sets (G.ground.erase v)
            · -- 既存の deg1 + haveUV ケースの専用結論（実装側にあるはず）
              -- 例： `nds_nonpos_deg1_haveUV`
              -- この定理が存在しないため、未実装

              let ind := Ideal.nds_diff_deg1_groundErase_in G  v hvU deg1
              have hne : (G.ground.erase v).Nonempty := by
                --G.ground.card ≥ 2 なので erase は Nonempty
                sorry
              specialize ind hne
              specialize ind hHaveUminus
              have hCard : (G.ground.erase v).card = Nat.succ k := by
                subst hn
                simp_all only [not_false_eq_true, Nat.succ_eq_add_one]
                simp_all only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, card_erase_of_mem,
                  add_tsub_cancel_right]
              --使うのは、IHからG.traceIdealのndsは<=0で、indの右辺は、レアで<=0
              have hTraceNonpos : (G.traceIdeal v hne).nds ≤ 0 := by
                apply IH
                dsimp [Ideal.traceIdeal]
                rw [hn]
                exact hCard
              dsimp [SetFamily.isRare] at hRare
              dsimp [SetFamily.degreeNat] at deg1
              have deg1_int : G.toSetFamily.degree v = 1 := by
                dsimp [SetFamily.degree]
                subst hn
                simp_all only [tsub_le_iff_right, zero_add, not_false_eq_true, Nat.succ_eq_add_one,
                  Nat.cast_add, Nat.cast_one, add_sub_cancel_right, card_erase_of_mem,
                  add_tsub_cancel_right, Nat.cast_eq_one]
                exact deg1
              have hRareIneq :
                  (2 : ℤ) - (G.toSetFamily.numEdges)
                    ≤ 0 := by
                subst hn
                simp_all only [mul_one, tsub_le_iff_right, zero_add, not_false_eq_true,
                  Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
                  card_erase_of_mem, add_tsub_cancel_right]
              sorry --deg 1の場合をこんなに大変に行う必要があるのか？contractionで閉じてない。traceで閉じている。
              --もともとは、deg1の場合は、traceによりnumberが保存され、大きさの和は1しか変わらないということを利用していた。
              --その関係式を補題にする必要がある。

            · -- `U\\{v}` も無し：差分恒等式の特化で NDS を trace と normdeg の和に分解し、IH とレアで ≤ 0
              -- ground ≥ 2 なので erase は Nonempty
              have hCard : G.ground.card = Nat.succ (Nat.succ k) := by
                subst hn
                simp_all only [not_false_eq_true, Nat.succ_eq_add_one]
              have hNE : (G.ground.erase v).Nonempty :=
                erase_nonempty_of_card_succ_succ (F := G) (n := k) (v := v) (hv := hvU) hCard
              -- 差分恒等式（次数1 特化）
              have hDiff :
                  G.toSetFamily.nds
                    -
                  (G.traceIdeal v hNE).toSetFamily.nds
                  =
                  (2 * (G.toSetFamily.degree v : ℤ) - (G.toSetFamily.numEdges)) := by
                -- 既存の `nds_diff_deg1_groundErase_notin`
                -- （仮定：hvU, deg1, hNE, hnot を満たしている）
                -- deg1 は `{v}∉F` のイデアル性から従う
                -- {v}∉F かつ v∈ground なら、v∈s∈F となる s は ground のみ
                have hdeg1 : G.toSetFamily.degreeNat v = 1 := by
                  -- degreeNat v = |S(v)| = |{s ∈ carrier | v ∈ s}|
                  -- {v}∉F より、v∈s∈F ⇒ s=ground を示す
                  have hSvEqGround : G.toSetFamily.S v = {G.ground} := by
                    apply Finset.ext
                    intro s
                    simp only [SetFamily.S, Finset.mem_filter, Finset.mem_singleton]
                    constructor
                    · intro ⟨hsCarrier, hvs⟩
                      -- s ∈ carrier かつ v ∈ s
                      -- carrier の定義より s ∈ powerset(ground) かつ G.sets s
                      have hsSet : G.sets s := by
                        exact (SetFamily.mem_carrier_iff (SF := G.toSetFamily)).mp hsCarrier |>.2
                      -- s ≠ ground と仮定すると矛盾を導く
                      by_cases hEq : s = G.ground
                      · exact hEq
                      · -- s ≠ ground のとき、下方閉性より {v} ∈ F
                        have : G.sets {v} := by
                          apply G.down_closed hsSet hEq
                          exact Finset.singleton_subset_iff.mpr hvs
                        exact absurd this hNotSing
                    · intro hEq
                      subst hEq
                      constructor
                      · -- ground ∈ carrier
                        exact Ideal.ground_mem_carrier G
                      · -- v ∈ ground
                        exact hvU
                  -- |S(v)| = |{ground}| = 1
                  -- degreeNat v の定義を展開
                  show (G.toSetFamily.S v).card = 1
                  rw [hSvEqGround]
                  simp
                exact nds_diff_deg1_groundErase_notin
                  (F := G) (v := v) hvU hdeg1 hNE hHaveUminus
              -- 目標形へ並べ替え
              -- G.nds = (trace v).nds + normalizedDegreeAt v
              have hEq :
                  G.toSetFamily.nds
                    =
                  (G.traceIdeal v hNE).toSetFamily.nds
                  +
                  (2 * (G.toSetFamily.degree v : ℤ) - (G.toSetFamily.numEdges)) := by
                -- sub_eq_add_neg を使わず等式変形で寄せる
                -- hDiff : A - B = C から A = B + C
                -- ring レベル等式
                have := hDiff
                -- ここは等式の移項：A - B = C  ⇒  A = B + C
                -- Lean では `sub_eq` を明示展開して扱う
                -- A - B = C  ↔  A = C + B
                -- 以降のファイル方針に合わせ、必要なら `ring` で同型変形してください
                -- ここでは手で書き換えます
                -- A - B = C  ⇒  A = C + B
                -- 具体的には、等式 `hDiff` を書き換えて `=` 右辺に B を足す
                have h' :
                    G.toSetFamily.nds
                      =
                    (2 * (G.toSetFamily.degree v : ℤ) - (G.toSetFamily.numEdges))
                      +
                    (G.traceIdeal v hNE).toSetFamily.nds := by
                  -- `add_comm` を一回使って順序を合わせる
                  have := eq_add_of_sub_eq this
                  -- eq_add_of_sub_eq : A - B = C → A = C + B
                  exact this
                -- 順序を `(trace).nds + normdeg` にしたいなら comm を一度使う
                simpa [add_comm] using h'
              -- trace 側は ground が 1 減（= k+1）、よって IH
              have hCardTrace :
                  (G.traceIdeal v hNE).ground.card = Nat.succ k := by
                -- trace の ground は erase v
                -- したがって card は先ほどと同じく k+1
                apply card_erase_eq_of_card_succ (F := G) (h := by
                  exact hCard )
                exact hvU

              have hIHTrace :
                  (G.traceIdeal v hNE).toSetFamily.nds ≤ 0 := by
                have := IH (G := (G.traceIdeal v hNE)) (by
                  -- traceIdeal の ground は erase v なので、card は hCardTrace で示した通り
                  -- 型が一致しないため、ここは保留
                  subst hn
                  simp_all only [not_false_eq_true, Nat.succ_eq_add_one,  add_sub_cancel_left])
                exact this
              -- レア（最後の項） ≤ 0
              have hRareZ :
                  (2 * (G.toSetFamily.degree v : ℤ) - (G.toSetFamily.numEdges)) ≤ 0 := by
                exact hRare
              -- 合成
              -- G.nds = (trace).nds + normdeg ≤ 0 + 0
              have hLe :
                  (G.traceIdeal v hNE).toSetFamily.nds
                  +
                  (2 * (G.toSetFamily.degree v : ℤ) - (G.toSetFamily.numEdges))
                  ≤ 0 + 0 := by
                exact add_le_add hIHTrace hRareZ
              have hZero : (0 : ℤ) + 0 = 0 := by ring
              rw [hEq]
              calc (G.traceIdeal v hNE).toSetFamily.nds
                    + (2 * (G.toSetFamily.degree v : ℤ) - (G.toSetFamily.numEdges))
                  ≤ 0 + 0 := hLe
                _ = 0 := hZero)
      ) F.ground.card rfl

end Ideal
