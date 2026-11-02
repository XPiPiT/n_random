import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Continuity
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Topology.Order.Compact

/-!
# 五阶线段多项式 SPR 综合的精简证明

只导入 Mathlib，不调用三阶、四阶或任意阶的主定理。
Hurwitz 与 SPR 定义沿用原五阶文件。

证明路线：频率紧化与凸分离 → 连续 max-min 临界支撑 → 有限矩证书
→ 留数插值 → 次数与接触点计数矛盾。
临界证书只要求原子数有限，不再携带六点上界。
互素分支直接使用二次因子整除插值多项式得到次数下界，
不再证明常数插值乘子或五点/六点二分结论。
公共根不成比例、成比例这两个退化分支仍分别处理。

本文件保留五阶主定理的必要性和充分性，公共分子与分母均为五阶。
命名空间：`MKNumina.SPR.Simplified.MonicQuinticCoeff`。
-/

namespace MKNumina.SPR.Simplified

structure MonicQuinticCoeff where
  c1 : ℝ
  c2 : ℝ
  c3 : ℝ
  c4 : ℝ
  c5 : ℝ

namespace MonicQuinticCoeff

noncomputable section

open Set

def jw (ω : ℝ) : ℂ := Complex.I * (ω : ℂ)

lemma complex_div_re_eq
    (z w : ℂ) :
    (z / w).re
      = (z.re * w.re + z.im * w.im) / Complex.normSq w := by
  rw [Complex.div_re]
  ring

lemma complex_div_re_pos_comm
    {z w : ℂ}
    (hz : z ≠ 0)
    (hw : w ≠ 0) :
    0 < (z / w).re ↔ 0 < (w / z).re := by
  rw [complex_div_re_eq, complex_div_re_eq]
  have hnz : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  have hnw : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  have hnum :
      z.re * w.re + z.im * w.im
        = w.re * z.re + w.im * z.im := by ring
  rw [hnum]
  constructor
  · intro h
    exact div_pos ((div_pos_iff_of_pos_right hnw).mp h) hnz
  · intro h
    exact div_pos ((div_pos_iff_of_pos_right hnz).mp h) hnw

lemma convexCoeff_pos_of_pos
    {x y t : ℝ}
    (hx : 0 < x)
    (hy : 0 < y)
    (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    0 < t * y + (1 - t) * x := by
  rcases eq_or_lt_of_le ht0 with hzero | htpos
  · subst t
    simpa using hx
  · have hleft : 0 < t * y := mul_pos htpos hy
    have hright : 0 ≤ (1 - t) * x := by
      exact mul_nonneg (sub_nonneg.mpr ht1) (le_of_lt hx)
    linarith

/-! ## 1. 五阶系数判据、频率代数与必要性 -/

def hurwitzDet2 (p : MonicQuinticCoeff) : ℝ :=
  p.c1 * p.c2 - p.c3

def hurwitzDet3 (p : MonicQuinticCoeff) : ℝ :=
  p.c1 * p.c2 * p.c3 - p.c1 ^ 2 * p.c4 - p.c3 ^ 2 + p.c1 * p.c5

def hurwitzDet4 (p : MonicQuinticCoeff) : ℝ :=
  p.c4 * p.hurwitzDet3 -
    p.c5 * (p.c1 * p.c2 ^ 2 - p.c1 * p.c4 - p.c2 * p.c3 + p.c5)

structure Hurwitz (p : MonicQuinticCoeff) : Prop where
  c1_pos : 0 < p.c1
  c2_pos : 0 < p.c2
  c3_pos : 0 < p.c3
  c4_pos : 0 < p.c4
  c5_pos : 0 < p.c5
  det2_pos : 0 < p.hurwitzDet2
  det3_pos : 0 < p.hurwitzDet3
  det4_pos : 0 < p.hurwitzDet4

def convex (p q : MonicQuinticCoeff) (t : ℝ) : MonicQuinticCoeff where
  c1 := (1 - t) * p.c1 + t * q.c1
  c2 := (1 - t) * p.c2 + t * q.c2
  c3 := (1 - t) * p.c3 + t * q.c3
  c4 := (1 - t) * p.c4 + t * q.c4
  c5 := (1 - t) * p.c5 + t * q.c5

def allConvexHurwitz (p q : MonicQuinticCoeff) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (p.convex q t).Hurwitz

@[simp] lemma convex_zero (p q : MonicQuinticCoeff) :
    p.convex q 0 = p := by
  cases p
  simp [convex]

@[simp] lemma convex_one (p q : MonicQuinticCoeff) :
    p.convex q 1 = q := by
  cases q
  simp [convex]

lemma convex_convex_left
    (p q : MonicQuinticCoeff) (u t : ℝ) :
    p.convex (p.convex q u) t = p.convex q (t * u) := by
  cases p
  cases q
  dsimp [convex]
  congr 1 <;> ring

lemma allConvexHurwitz_initial
    {p q : MonicQuinticCoeff} (h : p.allConvexHurwitz q)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    p.allConvexHurwitz (p.convex q u) := by
  intro t ht0 ht1
  rw [convex_convex_left]
  have htu0 : 0 ≤ t * u := mul_nonneg ht0 hu0
  have htuu : t * u ≤ u := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hu0]
  exact h (t * u) htu0 (htuu.trans hu1)

lemma allConvexHurwitz_left {p q : MonicQuinticCoeff}
    (h : p.allConvexHurwitz q) : p.Hurwitz := by
  simpa using h 0 (by norm_num) (by norm_num)

lemma allConvexHurwitz_right {p q : MonicQuinticCoeff}
    (h : p.allConvexHurwitz q) : q.Hurwitz := by
  simpa using h 1 (by norm_num) (by norm_num)

def evalJW (p : MonicQuinticCoeff) (ω : ℝ) : ℂ :=
  jw ω ^ 5 + (p.c1 : ℂ) * jw ω ^ 4 +
    (p.c2 : ℂ) * jw ω ^ 3 + (p.c3 : ℂ) * jw ω ^ 2 +
    (p.c4 : ℂ) * jw ω + (p.c5 : ℂ)

def evenPart (p : MonicQuinticCoeff) (t : ℝ) : ℝ :=
  p.c1 * t ^ 2 - p.c3 * t + p.c5

def oddPart (p : MonicQuinticCoeff) (t : ℝ) : ℝ :=
  t ^ 2 - p.c2 * t + p.c4

lemma evalJW_re (p : MonicQuinticCoeff) (ω : ℝ) :
    (p.evalJW ω).re = p.evenPart (ω ^ 2) := by
  norm_num [evalJW, jw, evenPart, pow_two, pow_succ]
  ring

lemma evalJW_im (p : MonicQuinticCoeff) (ω : ℝ) :
    (p.evalJW ω).im = ω * p.oddPart (ω ^ 2) := by
  norm_num [evalJW, jw, oddPart, pow_two, pow_succ]
  ring

lemma evalJW_ne_zero {p : MonicQuinticCoeff}
    (hp : p.Hurwitz) (ω : ℝ) : p.evalJW ω ≠ 0 := by
  intro hz
  have hre : p.evenPart (ω ^ 2) = 0 := by
    rw [← evalJW_re, hz]
    simp
  have him : ω * p.oddPart (ω ^ 2) = 0 := by
    rw [← evalJW_im, hz]
    simp
  by_cases hω : ω = 0
  · subst ω
    simp [evenPart] at hre
    exact (ne_of_gt hp.c5_pos) hre
  · have hodd : p.oddPart (ω ^ 2) = 0 :=
      (mul_eq_zero.mp him).resolve_left hω
    let D := p.hurwitzDet2
    let M := p.c1 * p.c4 - p.c5
    have hlin : D * (ω ^ 2) = M := by
      dsimp [D, M, hurwitzDet2]
      calc
        (p.c1 * p.c2 - p.c3) * (ω ^ 2) =
            p.evenPart (ω ^ 2) - p.c1 * p.oddPart (ω ^ 2) +
              (p.c1 * p.c4 - p.c5) := by
                unfold evenPart oddPart
                ring
        _ = p.c1 * p.c4 - p.c5 := by rw [hre, hodd]; ring
    have hresult : M ^ 2 - p.c2 * D * M + p.c4 * D ^ 2 = 0 := by
      have hscaled : D ^ 2 * p.oddPart (ω ^ 2) = 0 := by rw [hodd]; ring
      calc
        M ^ 2 - p.c2 * D * M + p.c4 * D ^ 2 =
            D ^ 2 * p.oddPart (ω ^ 2) := by
          rw [← hlin]
          unfold oddPart
          ring
        _ = 0 := hscaled
    have hid : M ^ 2 - p.c2 * D * M + p.c4 * D ^ 2 =
        -p.hurwitzDet4 := by
      dsimp [M, D, hurwitzDet2, hurwitzDet3, hurwitzDet4]
      ring
    linarith [hp.det4_pos]

lemma evalJW_normSq_pos {p : MonicQuinticCoeff}
    (hp : p.Hurwitz) (ω : ℝ) :
    0 < Complex.normSq (p.evalJW ω) :=
  Complex.normSq_pos.mpr (evalJW_ne_zero hp ω)

private def gap (p : MonicQuinticCoeff) : ℝ := p.c1 * p.c4 - p.c5

private def slope (p : MonicQuinticCoeff) : ℝ := p.c4 * p.c3 - p.c2 * p.c5

private lemma det4_gap_identity (p : MonicQuinticCoeff) :
    p.hurwitzDet4 =
      p.slope * p.hurwitzDet2 - p.gap ^ 2 := by
  dsimp [slope, gap, hurwitzDet2, hurwitzDet3, hurwitzDet4]
  ring

private lemma gap_pos {p : MonicQuinticCoeff} (hp : p.Hurwitz) :
    0 < p.gap := by
  have hid : p.hurwitzDet4 =
      p.c2 * p.hurwitzDet2 * p.gap - p.gap ^ 2 -
        p.c4 * p.hurwitzDet2 ^ 2 := by
    dsimp [gap, hurwitzDet2, hurwitzDet3, hurwitzDet4]
    ring
  by_contra h
  have hm : p.gap ≤ 0 := le_of_not_gt h
  have hprod : p.c2 * p.hurwitzDet2 * p.gap ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (mul_pos hp.c2_pos hp.det2_pos)) hm
  have hs1 := sq_nonneg p.gap
  have hs2 : 0 ≤ p.c4 * p.hurwitzDet2 ^ 2 :=
    mul_nonneg (le_of_lt hp.c4_pos) (sq_nonneg _)
  linarith [hp.det4_pos]

private lemma slope_pos {p : MonicQuinticCoeff} (hp : p.Hurwitz) :
    0 < p.slope := by
  have hid := p.det4_gap_identity
  have hsq := sq_nonneg p.gap
  have hprod : 0 < p.slope * p.hurwitzDet2 := by
    have hdet := hp.det4_pos
    rw [hid] at hdet
    nlinarith
  exact (mul_pos_iff_of_pos_right hp.det2_pos).mp hprod

def perturbCross (p d : MonicQuinticCoeff) (t : ℝ) : ℝ :=
  p.evenPart t * d.evenPart t + t * p.oddPart t * d.oddPart t

def SPR5For (p n : MonicQuinticCoeff) : Prop :=
  p.Hurwitz ∧ ∀ ω : ℝ, 0 < ((n.evalJW ω) / p.evalJW ω).re

def ExistsCommonMonicSPR5 (p q : MonicQuinticCoeff) : Prop :=
  ∃ n : MonicQuinticCoeff, p.SPR5For n ∧ q.SPR5For n

lemma re_monicQuintic_div (p n : MonicQuinticCoeff) (ω : ℝ) :
    ((n.evalJW ω) / p.evalJW ω).re =
      p.perturbCross n (ω ^ 2) /
        Complex.normSq (p.evalJW ω) := by
  rw [complex_div_re_eq, evalJW_re, evalJW_re,
    evalJW_im, evalJW_im]
  unfold perturbCross
  ring

theorem existsCommonMonicSPR5_iff_cross_positive
    {p q : MonicQuinticCoeff} :
    p.ExistsCommonMonicSPR5 q ↔
      p.Hurwitz ∧ q.Hurwitz ∧
        ∃ n : MonicQuinticCoeff, ∀ t : ℝ, 0 ≤ t →
          0 < p.perturbCross n t ∧ 0 < q.perturbCross n t := by
  constructor
  · rintro ⟨n, ⟨hp, hrealP⟩, ⟨hq, hrealQ⟩⟩
    refine ⟨hp, hq, n, ?_⟩
    intro t ht
    have hsqrt : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht
    constructor
    · have h := hrealP (Real.sqrt t)
      rw [re_monicQuintic_div, hsqrt] at h
      exact (div_pos_iff_of_pos_right
        (evalJW_normSq_pos hp (Real.sqrt t))).mp h
    · have h := hrealQ (Real.sqrt t)
      rw [re_monicQuintic_div, hsqrt] at h
      exact (div_pos_iff_of_pos_right
        (evalJW_normSq_pos hq (Real.sqrt t))).mp h
  · rintro ⟨hp, hq, n, hcross⟩
    refine ⟨n, ⟨hp, ?_⟩, ⟨hq, ?_⟩⟩
    · intro ω
      rw [re_monicQuintic_div]
      exact div_pos (hcross (ω ^ 2) (sq_nonneg ω)).1
        (evalJW_normSq_pos hp ω)
    · intro ω
      rw [re_monicQuintic_div]
      exact div_pos (hcross (ω ^ 2) (sq_nonneg ω)).2
        (evalJW_normSq_pos hq ω)

lemma perturbCross_self_pos
    {p : MonicQuinticCoeff} (hp : p.Hurwitz)
    {t : ℝ} (ht : 0 ≤ t) :
    0 < p.perturbCross p t := by
  have hnorm := evalJW_normSq_pos hp (Real.sqrt t)
  rw [Complex.normSq_apply, evalJW_re, evalJW_im] at hnorm
  have hsqrt := Real.sq_sqrt ht
  rw [hsqrt] at hnorm
  have himag :
      Real.sqrt t * p.oddPart t * (Real.sqrt t * p.oddPart t) =
        t * p.oddPart t * p.oddPart t := by
    calc
      Real.sqrt t * p.oddPart t * (Real.sqrt t * p.oddPart t) =
          (Real.sqrt t) ^ 2 * (p.oddPart t) ^ 2 := by ring
      _ = t * p.oddPart t * p.oddPart t := by rw [hsqrt]; ring
  rw [himag] at hnorm
  unfold perturbCross
  exact hnorm

lemma oddPart_convex (p q : MonicQuinticCoeff) (t v : ℝ) :
    (p.convex q t).oddPart v =
      (1 - t) * p.oddPart v + t * q.oddPart v := by
  unfold convex oddPart
  ring

lemma evenPart_convex (p q : MonicQuinticCoeff) (t v : ℝ) :
    (p.convex q t).evenPart v =
      (1 - t) * p.evenPart v + t * q.evenPart v := by
  unfold convex evenPart
  ring

lemma evalJW_convex (p q : MonicQuinticCoeff) (t ω : ℝ) :
    (p.convex q t).evalJW ω =
      ((1 - t : ℝ) : ℂ) * p.evalJW ω +
        (t : ℂ) * q.evalJW ω := by
  unfold convex evalJW
  push_cast
  ring

lemma re_convex_div (p q n : MonicQuinticCoeff) (t ω : ℝ) :
    (((p.convex q t).evalJW ω) / n.evalJW ω).re =
      (1 - t) * ((p.evalJW ω) / n.evalJW ω).re +
        t * ((q.evalJW ω) / n.evalJW ω).re := by
  rw [evalJW_convex, add_div]
  rw [mul_div_assoc, mul_div_assoc]
  norm_num

lemma numerator_evalJW_ne_zero_of_re_pos
    {d n : MonicQuinticCoeff}
    (hreal : ∀ ω : ℝ,
      0 < ((n.evalJW ω) / d.evalJW ω).re)
    (ω : ℝ) : n.evalJW ω ≠ 0 := by
  intro hz
  have h := hreal ω
  rw [hz] at h
  norm_num at h

theorem common_monicSPR5_segment_evalJW_ne_zero
    {p q : MonicQuinticCoeff}
    (hcommon : p.ExistsCommonMonicSPR5 q)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ω : ℝ) :
    (p.convex q t).evalJW ω ≠ 0 := by
  obtain ⟨n, hp, hq⟩ := hcommon
  have hn : n.evalJW ω ≠ 0 :=
    numerator_evalJW_ne_zero_of_re_pos hp.2 ω
  have hInvP : 0 < ((p.evalJW ω) / n.evalJW ω).re :=
    (complex_div_re_pos_comm hn (evalJW_ne_zero hp.1 ω)).1 (hp.2 ω)
  have hInvQ : 0 < ((q.evalJW ω) / n.evalJW ω).re :=
    (complex_div_re_pos_comm hn (evalJW_ne_zero hq.1 ω)).1 (hq.2 ω)
  have hConv : 0 <
      (((p.convex q t).evalJW ω) / n.evalJW ω).re := by
    rw [re_convex_div]
    simpa [add_comm] using
      (convexCoeff_pos_of_pos hInvP hInvQ ht0 ht1)
  intro hz
  rw [hz] at hConv
  norm_num at hConv

private lemma evenPart_sub_oddPart (p : MonicQuinticCoeff) (t : ℝ) :
    p.evenPart t = p.c1 * p.oddPart t +
      p.hurwitzDet2 * t - p.gap := by
  dsimp [evenPart, oddPart, hurwitzDet2, gap]
  ring

private lemma det4_resultant_identity (p : MonicQuinticCoeff) :
    p.hurwitzDet4 =
      p.c2 * p.hurwitzDet2 * p.gap - p.gap ^ 2 -
        p.c4 * p.hurwitzDet2 ^ 2 := by
  dsimp [hurwitzDet2, hurwitzDet3, hurwitzDet4, gap]
  ring

private lemma odd_discriminant_identity (p : MonicQuinticCoeff) :
    4 * p.hurwitzDet4 =
      (p.c2 ^ 2 - 4 * p.c4) * p.hurwitzDet2 ^ 2 -
        (2 * p.gap - p.c2 * p.hurwitzDet2) ^ 2 := by
  rw [p.det4_resultant_identity]
  ring

lemma odd_discriminant_pos {p : MonicQuinticCoeff}
    (hp : p.Hurwitz) : 0 < p.c2 ^ 2 - 4 * p.c4 := by
  have hid := p.odd_discriminant_identity
  have hs := sq_nonneg (2 * p.gap - p.c2 * p.hurwitzDet2)
  have hprod : 0 <
      (p.c2 ^ 2 - 4 * p.c4) * p.hurwitzDet2 ^ 2 := by
    nlinarith [hp.det4_pos]
  exact (mul_pos_iff_of_pos_right
    (sq_pos_of_pos hp.det2_pos)).mp hprod

structure QuinticDenominatorInterlacing
    (p : MonicQuinticCoeff) where
  e₁ : ℝ
  o₁ : ℝ
  e₂ : ℝ
  o₂ : ℝ
  ordered : 0 < e₁ ∧ e₁ < o₁ ∧ o₁ < e₂ ∧ e₂ < o₂
  roots : p.evenPart e₁ = 0 ∧ p.oddPart o₁ = 0 ∧
    p.evenPart e₂ = 0 ∧ p.oddPart o₂ = 0

theorem denominator_interlacing_of_hurwitz
    {p : MonicQuinticCoeff} (hp : p.Hurwitz) :
    Nonempty (QuinticDenominatorInterlacing p) := by
  let r : ℝ := p.gap / p.hurwitzDet2
  have hrpos : 0 < r := div_pos (gap_pos hp) hp.det2_pos
  have hDr : p.hurwitzDet2 * r = p.gap := by
    dsimp [r]
    field_simp [ne_of_gt hp.det2_pos]
  have hT : 0 < p.c2 * p.hurwitzDet2 - p.gap := by
    have hid := p.det4_resultant_identity
    have hc4D := mul_pos hp.c4_pos (sq_pos_of_pos hp.det2_pos)
    by_contra hn
    have hnonpos : p.c2 * p.hurwitzDet2 - p.gap ≤ 0 :=
      le_of_not_gt hn
    have hprod := mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (gap_pos hp)) hnonpos
    nlinarith [hp.det4_pos]
  have hrc2 : r < p.c2 := by
    dsimp [r]
    exact (div_lt_iff₀ hp.det2_pos).2 (by nlinarith)
  have hodd_r : p.oddPart r < 0 := by
    have hscaled : p.hurwitzDet2 ^ 2 * p.oddPart r =
        -p.hurwitzDet4 := by
      rw [p.det4_resultant_identity]
      dsimp [r, oddPart]
      field_simp [ne_of_gt hp.det2_pos]
      ring
    have hD2 : 0 < p.hurwitzDet2 ^ 2 := sq_pos_of_pos hp.det2_pos
    nlinarith [hp.det4_pos]
  have hodd_zero : 0 < p.oddPart 0 := by
    simpa [oddPart] using hp.c4_pos
  have hodd_c2 : 0 < p.oddPart p.c2 := by
    dsimp [oddPart]
    nlinarith [hp.c4_pos]
  have hodd_cont : Continuous p.oddPart := by
    unfold oddPart
    fun_prop
  have hzero_mem_left : 0 ∈ Set.Icc (p.oddPart r) (p.oddPart 0) :=
    ⟨hodd_r.le, hodd_zero.le⟩
  obtain ⟨o₁, ho₁mem, ho₁root⟩ :=
    (intermediate_value_Icc' hrpos.le hodd_cont.continuousOn)
      hzero_mem_left
  have ho₁pos : 0 < o₁ := by
    rcases eq_or_lt_of_le ho₁mem.1 with h | h
    · subst o₁
      have : p.c4 = 0 := by simpa [oddPart] using ho₁root
      exact False.elim ((ne_of_gt hp.c4_pos) this)
    · exact h
  have ho₁r : o₁ < r := by
    rcases eq_or_lt_of_le ho₁mem.2 with h | h
    · subst o₁
      linarith
    · exact h
  have hzero_mem_right : 0 ∈ Set.Icc (p.oddPart r) (p.oddPart p.c2) :=
    ⟨hodd_r.le, hodd_c2.le⟩
  obtain ⟨o₂, ho₂mem, ho₂root⟩ :=
    (intermediate_value_Icc hrc2.le hodd_cont.continuousOn)
      hzero_mem_right
  have hro₂ : r < o₂ := by
    rcases eq_or_lt_of_le ho₂mem.1 with h | h
    · subst o₂
      linarith
    · exact h
  have ho₂c2 : o₂ < p.c2 := by
    rcases eq_or_lt_of_le ho₂mem.2 with h | h
    · subst o₂
      have : p.c4 = 0 := by
        dsimp [oddPart] at ho₂root
        nlinarith
      exact False.elim ((ne_of_gt hp.c4_pos) this)
    · exact h
  have heven_o₁ : p.evenPart o₁ < 0 := by
    rw [p.evenPart_sub_oddPart o₁, ho₁root]
    simp only [mul_zero, add_zero]
    nlinarith [hDr, hp.det2_pos]
  have heven_o₂ : 0 < p.evenPart o₂ := by
    rw [p.evenPart_sub_oddPart o₂, ho₂root]
    simp only [mul_zero, add_zero]
    nlinarith [hDr, hp.det2_pos]
  have heven_zero : 0 < p.evenPart 0 := by
    simpa [evenPart] using hp.c5_pos
  have heven_cont : Continuous p.evenPart := by
    unfold evenPart
    fun_prop
  have hzero_even_left : 0 ∈ Set.Icc (p.evenPart o₁) (p.evenPart 0) :=
    ⟨heven_o₁.le, heven_zero.le⟩
  obtain ⟨e₁, he₁mem, he₁root⟩ :=
    (intermediate_value_Icc' ho₁pos.le heven_cont.continuousOn)
      hzero_even_left
  have he₁pos : 0 < e₁ := by
    rcases eq_or_lt_of_le he₁mem.1 with h | h
    · subst e₁
      have : p.c5 = 0 := by simpa [evenPart] using he₁root
      exact False.elim ((ne_of_gt hp.c5_pos) this)
    · exact h
  have he₁o₁ : e₁ < o₁ := by
    rcases eq_or_lt_of_le he₁mem.2 with h | h
    · subst e₁
      linarith
    · exact h
  have hzero_even_right : 0 ∈
      Set.Icc (p.evenPart o₁) (p.evenPart o₂) :=
    ⟨heven_o₁.le, heven_o₂.le⟩
  obtain ⟨e₂, he₂mem, he₂root⟩ :=
    (intermediate_value_Icc (le_trans ho₁r.le hro₂.le)
      heven_cont.continuousOn) hzero_even_right
  have ho₁e₂ : o₁ < e₂ := by
    rcases eq_or_lt_of_le he₂mem.1 with h | h
    · subst e₂
      linarith
    · exact h
  have he₂o₂ : e₂ < o₂ := by
    rcases eq_or_lt_of_le he₂mem.2 with h | h
    · subst e₂
      linarith
    · exact h
  exact ⟨⟨e₁, o₁, e₂, o₂,
    ⟨he₁pos, he₁o₁, ho₁e₂, he₂o₂⟩,
    ⟨he₁root, ho₁root, he₂root, ho₂root⟩⟩⟩

lemma QuinticDenominatorInterlacing.odd_eval
    {p : MonicQuinticCoeff} (D : QuinticDenominatorInterlacing p)
    (t : ℝ) :
    p.oddPart t = (t - D.o₁) * (t - D.o₂) := by
  have h₁ := D.roots.2.1
  have h₂ := D.roots.2.2.2
  dsimp [oddPart] at h₁ h₂ ⊢
  have hprod : (D.o₂ - D.o₁) *
      (D.o₂ + D.o₁ - p.c2) = 0 := by
    nlinarith
  have hsum : D.o₂ + D.o₁ - p.c2 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left
      (ne_of_gt (sub_pos.mpr
        (D.ordered.2.2.1.trans D.ordered.2.2.2)))
  have hc2 : p.c2 = D.o₁ + D.o₂ := by linarith
  rw [hc2] at h₁
  have hc4 : p.c4 = D.o₁ * D.o₂ := by
    nlinarith
  rw [hc2, hc4]
  ring

lemma QuinticDenominatorInterlacing.even_eval
    {p : MonicQuinticCoeff} (D : QuinticDenominatorInterlacing p)
    (t : ℝ) :
    p.evenPart t = p.c1 * ((t - D.e₁) * (t - D.e₂)) := by
  have h₁ := D.roots.1
  have h₂ := D.roots.2.2.1
  dsimp [evenPart] at h₁ h₂ ⊢
  have hprod : (D.e₂ - D.e₁) *
      (p.c1 * (D.e₂ + D.e₁) - p.c3) = 0 := by
    nlinarith
  have hsum : p.c1 * (D.e₂ + D.e₁) - p.c3 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left
      (ne_of_gt (sub_pos.mpr
        (D.ordered.2.1.trans D.ordered.2.2.1)))
  have hc3 : p.c3 = p.c1 * (D.e₁ + D.e₂) := by linarith
  rw [hc3] at h₁
  have hc5 : p.c5 = p.c1 * (D.e₁ * D.e₂) := by
    nlinarith
  rw [hc3, hc5]
  ring

lemma QuinticDenominatorInterlacing.odd_e₁_pos
    {p : MonicQuinticCoeff} (D : QuinticDenominatorInterlacing p) :
    0 < p.oddPart D.e₁ := by
  rw [D.odd_eval]
  exact mul_pos_of_neg_of_neg
    (sub_neg.mpr D.ordered.2.1)
    (sub_neg.mpr (D.ordered.2.1.trans
      (D.ordered.2.2.1.trans D.ordered.2.2.2)))

lemma QuinticDenominatorInterlacing.odd_e₂_neg
    {p : MonicQuinticCoeff} (D : QuinticDenominatorInterlacing p) :
    p.oddPart D.e₂ < 0 := by
  rw [D.odd_eval]
  exact mul_neg_of_pos_of_neg
    (sub_pos.mpr D.ordered.2.2.1)
    (sub_neg.mpr D.ordered.2.2.2)

lemma QuinticDenominatorInterlacing.even_o₁_neg
    {p : MonicQuinticCoeff} (D : QuinticDenominatorInterlacing p)
    (hp : p.Hurwitz) :
    p.evenPart D.o₁ < 0 := by
  rw [D.even_eval]
  exact mul_neg_of_pos_of_neg hp.c1_pos
    (mul_neg_of_pos_of_neg
      (sub_pos.mpr D.ordered.2.1)
      (sub_neg.mpr D.ordered.2.2.1))

lemma QuinticDenominatorInterlacing.even_o₂_pos
    {p : MonicQuinticCoeff} (D : QuinticDenominatorInterlacing p)
    (hp : p.Hurwitz) :
    0 < p.evenPart D.o₂ := by
  rw [D.even_eval]
  exact mul_pos hp.c1_pos
    (mul_pos
      (sub_pos.mpr (D.ordered.2.1.trans
        (D.ordered.2.2.1.trans D.ordered.2.2.2)))
      (sub_pos.mpr D.ordered.2.2.2))

lemma quadratic_leading_nonneg_of_weak_signs
    {u v w x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hw : 0 ≤ w) (hqx : u * x ^ 2 - v * x + w ≤ 0)
    (hqy : 0 ≤ u * y ^ 2 - v * y + w) :
    0 ≤ u := by
  by_contra hu
  have hu' : u < 0 := lt_of_not_ge hu
  have hy : 0 < y := hx.trans hxy
  have hleft : (y - x) * (u * x * y - w) < 0 := by
    exact mul_neg_of_pos_of_neg (sub_pos.mpr hxy)
      (sub_neg.mpr (by
        have := mul_neg_of_neg_of_pos
          (mul_neg_of_neg_of_pos hu' hx) hy
        linarith))
  have hid : (y - x) * (u * x * y - w) =
      x * (u * y ^ 2 - v * y + w) -
        y * (u * x ^ 2 - v * x + w) := by ring
  rw [hid] at hleft
  have hright : 0 ≤
      x * (u * y ^ 2 - v * y + w) -
        y * (u * x ^ 2 - v * x + w) := by
    have hxq : 0 ≤ x * (u * y ^ 2 - v * y + w) :=
      mul_nonneg hx.le hqy
    have hyq : y * (u * x ^ 2 - v * x + w) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hy.le hqx
    linarith
  linarith

lemma quadratic_constant_nonneg_of_weak_signs
    {u v w x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hu : 0 ≤ u) (hqx : 0 ≤ u * x ^ 2 - v * x + w)
    (hqy : u * y ^ 2 - v * y + w ≤ 0) :
    0 ≤ w := by
  by_contra hw
  have hw' : w < 0 := lt_of_not_ge hw
  have hy : 0 < y := hx.trans hxy
  have hleft : 0 < (y - x) * (u * x * y - w) := by
    exact mul_pos (sub_pos.mpr hxy) (by
      have := mul_nonneg (mul_nonneg hu hx.le) hy.le
      linarith)
  have hid : (y - x) * (u * x * y - w) =
      x * (u * y ^ 2 - v * y + w) -
        y * (u * x ^ 2 - v * x + w) := by ring
  rw [hid] at hleft
  have hright :
      x * (u * y ^ 2 - v * y + w) -
        y * (u * x ^ 2 - v * x + w) ≤ 0 := by
    have h₁ := mul_nonpos_of_nonneg_of_nonpos hx.le hqy
    have h₂ := mul_nonneg hy.le hqx
    linarith
  linarith

lemma quadratic_middle_nonneg_of_weak_signs
    {u v w x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hu : 0 ≤ u) (hqx : 0 ≤ u * x ^ 2 - v * x + w)
    (hqy : u * y ^ 2 - v * y + w ≤ 0) :
    0 ≤ v := by
  by_contra hv
  have hv' : v < 0 := lt_of_not_ge hv
  have hy : 0 < y := hx.trans hxy
  have hleft : 0 < (y - x) * (u * (y + x) - v) := by
    exact mul_pos (sub_pos.mpr hxy) (by
      have := mul_nonneg hu (add_nonneg hy.le hx.le)
      linarith)
  have hid : (y - x) * (u * (y + x) - v) =
      (u * y ^ 2 - v * y + w) -
        (u * x ^ 2 - v * x + w) := by ring
  rw [hid] at hleft
  linarith

lemma ordered_quadratic_roots_eq_of_product_nonneg
    {x₁ x₂ y₁ y₂ : ℝ}
    (hx₁ : 0 < x₁) (hxx : x₁ < x₂)
    (hy₁ : 0 < y₁) (hyy : y₁ < y₂)
    (hnonneg : ∀ t : ℝ, 0 ≤ t →
      0 ≤ ((t - x₁) * (t - x₂)) * ((t - y₁) * (t - y₂))) :
    x₁ = y₁ ∧ x₂ = y₂ := by
  have hfirst : x₁ = y₁ := by
    apply le_antisymm
    · by_contra h
      have hyx : y₁ < x₁ := lt_of_not_ge h
      let u := min y₂ x₁
      have hyu : y₁ < u := lt_min hyy hyx
      let t := (y₁ + u) / 2
      have hyt : y₁ < t := by dsimp [t]; linarith
      have htu : t < u := by dsimp [t]; linarith
      have htx₁ : t < x₁ := htu.trans_le (min_le_right _ _)
      have htx₂ : t < x₂ := htx₁.trans hxx
      have hty₂ : t < y₂ := htu.trans_le (min_le_left _ _)
      have ht0 : 0 ≤ t := le_of_lt (hy₁.trans hyt)
      have hxpos : 0 < (t - x₁) * (t - x₂) :=
        mul_pos_of_neg_of_neg (sub_neg.mpr htx₁) (sub_neg.mpr htx₂)
      have hyneg : (t - y₁) * (t - y₂) < 0 :=
        mul_neg_of_pos_of_neg (sub_pos.mpr hyt) (sub_neg.mpr hty₂)
      exact (not_lt_of_ge (hnonneg t ht0))
        (mul_neg_of_pos_of_neg hxpos hyneg)
    · by_contra h
      have hxy : x₁ < y₁ := lt_of_not_ge h
      let u := min x₂ y₁
      have hxu : x₁ < u := lt_min hxx hxy
      let t := (x₁ + u) / 2
      have hxt : x₁ < t := by dsimp [t]; linarith
      have htu : t < u := by dsimp [t]; linarith
      have htx₂ : t < x₂ := htu.trans_le (min_le_left _ _)
      have hty₁ : t < y₁ := htu.trans_le (min_le_right _ _)
      have hty₂ : t < y₂ := hty₁.trans hyy
      have ht0 : 0 ≤ t := le_of_lt (hx₁.trans hxt)
      have hxneg : (t - x₁) * (t - x₂) < 0 :=
        mul_neg_of_pos_of_neg (sub_pos.mpr hxt) (sub_neg.mpr htx₂)
      have hypos : 0 < (t - y₁) * (t - y₂) :=
        mul_pos_of_neg_of_neg (sub_neg.mpr hty₁) (sub_neg.mpr hty₂)
      exact (not_lt_of_ge (hnonneg t ht0))
        (mul_neg_of_neg_of_pos hxneg hypos)
  subst y₁
  refine ⟨rfl, le_antisymm ?_ ?_⟩
  · by_contra h
    have hyx : y₂ < x₂ := lt_of_not_ge h
    let t := (y₂ + x₂) / 2
    have hyt : y₂ < t := by dsimp [t]; linarith
    have htx : t < x₂ := by dsimp [t]; linarith
    have hx₁t : x₁ < t := hyy.trans hyt
    have ht0 : 0 ≤ t := le_of_lt (hx₁.trans hx₁t)
    have hxneg : (t - x₁) * (t - x₂) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hx₁t) (sub_neg.mpr htx)
    have hypos : 0 < (t - x₁) * (t - y₂) :=
      mul_pos (sub_pos.mpr hx₁t) (sub_pos.mpr hyt)
    exact (not_lt_of_ge (hnonneg t ht0))
      (mul_neg_of_neg_of_pos hxneg hypos)
  · by_contra h
    have hxy : x₂ < y₂ := lt_of_not_ge h
    let t := (x₂ + y₂) / 2
    have hxt : x₂ < t := by dsimp [t]; linarith
    have hty : t < y₂ := by dsimp [t]; linarith
    have hx₁t : x₁ < t := hxx.trans hxt
    have ht0 : 0 ≤ t := le_of_lt (hx₁.trans hx₁t)
    have hxpos : 0 < (t - x₁) * (t - x₂) :=
      mul_pos (sub_pos.mpr hx₁t) (sub_pos.mpr hxt)
    have hyneg : (t - x₁) * (t - y₂) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hx₁t) (sub_neg.mpr hty)
    exact (not_lt_of_ge (hnonneg t ht0))
      (mul_neg_of_pos_of_neg hxpos hyneg)

lemma eq_zero_of_nonneg_left_nonpos_right
    {f : ℝ → ℝ} (hf : Continuous f) {a b c : ℝ}
    (hab : a < b) (hbc : b < c)
    (hleft : ∀ x ∈ Set.Ioo a b, 0 ≤ f x)
    (hright : ∀ x ∈ Set.Ioo b c, f x ≤ 0) :
    f b = 0 := by
  have hb_left : b ∈ closure (Set.Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact ⟨hab.le, le_rfl⟩
  have hb_right : b ∈ closure (Set.Ioo b c) := by
    rw [closure_Ioo hbc.ne]
    exact ⟨le_rfl, hbc.le⟩
  have hclosed_left : IsClosed {x : ℝ | 0 ≤ f x} :=
    isClosed_le continuous_const hf
  have hclosed_right : IsClosed {x : ℝ | f x ≤ 0} :=
    isClosed_le hf continuous_const
  have hnonneg : 0 ≤ f b :=
    (closure_minimal hleft hclosed_left) hb_left
  have hnonpos : f b ≤ 0 :=
    (closure_minimal hright hclosed_right) hb_right
  exact le_antisymm hnonpos hnonneg

lemma eq_zero_of_nonpos_left_nonneg_right
    {f : ℝ → ℝ} (hf : Continuous f) {a b c : ℝ}
    (hab : a < b) (hbc : b < c)
    (hleft : ∀ x ∈ Set.Ioo a b, f x ≤ 0)
    (hright : ∀ x ∈ Set.Ioo b c, 0 ≤ f x) :
    f b = 0 := by
  have h := eq_zero_of_nonneg_left_nonpos_right
    hf.neg hab hbc
    (fun x hx => neg_nonneg.mpr (hleft x hx))
    (fun x hx => neg_nonpos.mpr (hright x hx))
  simpa using (neg_eq_zero.mp h)

private lemma evalJW_sqrt_eq_zero_of_parts
    {p : MonicQuinticCoeff} {t : ℝ}
    (ht : 0 ≤ t) (he : p.evenPart t = 0)
    (ho : p.oddPart t = 0) :
    p.evalJW (Real.sqrt t) = 0 := by
  apply Complex.ext
  · simpa [evalJW_re, Real.sq_sqrt ht] using he
  · rw [evalJW_im, Real.sq_sqrt ht, ho]
    simp

private lemma evalJW_zero_of_det2_zero
    {p : MonicQuinticCoeff}
    (hc2 : 0 < p.c2)
    (hdisc : 0 ≤ p.c2 ^ 2 - 4 * p.c4)
    (hD : p.hurwitzDet2 = 0)
    (hM : p.gap = 0) :
    ∃ ω : ℝ, p.evalJW ω = 0 := by
  let s := Real.sqrt (p.c2 ^ 2 - 4 * p.c4)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = p.c2 ^ 2 - 4 * p.c4 :=
    Real.sq_sqrt hdisc
  let t := (p.c2 + s) / 2
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ho : p.oddPart t = 0 := by
    dsimp [oddPart, t]
    nlinarith [hs2]
  have he : p.evenPart t = 0 := by
    rw [p.evenPart_sub_oddPart t, ho, hD, hM]
    ring
  exact ⟨Real.sqrt t, evalJW_sqrt_eq_zero_of_parts ht he ho⟩

private lemma evalJW_zero_of_det4_zero
    {p : MonicQuinticCoeff}
    (hD : 0 < p.hurwitzDet2)
    (hM : 0 < p.gap)
    (hdet : p.hurwitzDet4 = 0) :
    ∃ ω : ℝ, p.evalJW ω = 0 := by
  let t := p.gap / p.hurwitzDet2
  have ht : 0 ≤ t := le_of_lt (div_pos hM hD)
  have hlin : p.hurwitzDet2 * t = p.gap := by
    dsimp [t]
    field_simp [ne_of_gt hD]
  have hresult : p.gap ^ 2 - p.c2 * p.hurwitzDet2 * p.gap +
      p.c4 * p.hurwitzDet2 ^ 2 = 0 := by
    have hid := p.det4_resultant_identity
    rw [hdet] at hid
    nlinarith
  have hscaled : p.hurwitzDet2 ^ 2 * p.oddPart t = 0 := by
    have heq : p.hurwitzDet2 ^ 2 * p.oddPart t =
        p.gap ^ 2 - p.c2 * p.hurwitzDet2 * p.gap +
          p.c4 * p.hurwitzDet2 ^ 2 := by
      dsimp [t, oddPart]
      field_simp [ne_of_gt hD]
      ring
    rw [heq, hresult]
  have ho : p.oddPart t = 0 := by
    exact (mul_eq_zero.mp hscaled).resolve_left
      (ne_of_gt (sq_pos_of_pos hD))
  have he : p.evenPart t = 0 := by
    rw [p.evenPart_sub_oddPart t, ho, hlin]
    ring
  exact ⟨Real.sqrt t, evalJW_sqrt_eq_zero_of_parts ht he ho⟩

structure WeakHurwitz (p : MonicQuinticCoeff) : Prop where
  c1_nonneg : 0 ≤ p.c1
  c2_nonneg : 0 ≤ p.c2
  c3_nonneg : 0 ≤ p.c3
  c4_nonneg : 0 ≤ p.c4
  c5_nonneg : 0 ≤ p.c5
  det2_nonneg : 0 ≤ p.hurwitzDet2
  det3_nonneg : 0 ≤ p.hurwitzDet3
  det4_nonneg : 0 ≤ p.hurwitzDet4
  gap_nonneg : 0 ≤ p.gap
  slope_nonneg : 0 ≤ p.slope
  odd_discriminant_nonneg : 0 ≤ p.c2 ^ 2 - 4 * p.c4

theorem hurwitz_of_weak_no_axis
    {p : MonicQuinticCoeff} (hw : p.WeakHurwitz)
    (hno : ∀ ω : ℝ, p.evalJW ω ≠ 0) : p.Hurwitz := by
  have hc5 : 0 < p.c5 := by
    by_contra hn
    have hz : p.c5 = 0 := le_antisymm (le_of_not_gt hn) hw.c5_nonneg
    apply hno 0
    simp [evalJW, jw, hz]
  have hc1 : 0 < p.c1 := by
    by_contra hn
    have hz : p.c1 = 0 := le_antisymm (le_of_not_gt hn) hw.c1_nonneg
    have hh := hw.gap_nonneg
    dsimp [gap] at hh
    rw [hz] at hh
    nlinarith
  have hc4 : 0 < p.c4 := by
    by_contra hn
    have hz : p.c4 = 0 := le_antisymm (le_of_not_gt hn) hw.c4_nonneg
    have hh := hw.gap_nonneg
    dsimp [gap] at hh
    rw [hz] at hh
    nlinarith
  have hc2 : 0 < p.c2 := by
    by_contra hn
    have hz : p.c2 = 0 := le_antisymm (le_of_not_gt hn) hw.c2_nonneg
    have hh := hw.odd_discriminant_nonneg
    rw [hz] at hh
    nlinarith
  have hc3 : 0 < p.c3 := by
    by_contra hn
    have hz : p.c3 = 0 := le_antisymm (le_of_not_gt hn) hw.c3_nonneg
    have hh := hw.slope_nonneg
    dsimp [slope] at hh
    rw [hz] at hh
    nlinarith [mul_pos hc2 hc5]
  have hD : 0 < p.hurwitzDet2 := by
    by_contra hn
    have hz : p.hurwitzDet2 = 0 :=
      le_antisymm (le_of_not_gt hn) hw.det2_nonneg
    have hid := p.det4_gap_identity
    rw [hz] at hid
    have hM : p.gap = 0 := by
      nlinarith [hw.det4_nonneg, sq_nonneg p.gap]
    obtain ⟨ω, hω⟩ :=
      evalJW_zero_of_det2_zero hc2
        hw.odd_discriminant_nonneg hz hM
    exact hno ω hω
  have hM : 0 < p.gap := by
    by_contra hn
    have hz : p.gap = 0 :=
      le_antisymm (le_of_not_gt hn) hw.gap_nonneg
    have hid := p.det4_resultant_identity
    rw [hz] at hid
    have hpos := mul_pos hc4 (sq_pos_of_pos hD)
    nlinarith [hw.det4_nonneg]
  have hdet4 : 0 < p.hurwitzDet4 := by
    by_contra hn
    have hz : p.hurwitzDet4 = 0 :=
      le_antisymm (le_of_not_gt hn) hw.det4_nonneg
    obtain ⟨ω, hω⟩ := evalJW_zero_of_det4_zero hD hM hz
    exact hno ω hω
  have hdet3 : 0 < p.hurwitzDet3 := by
    by_contra hn
    have hz : p.hurwitzDet3 = 0 :=
      le_antisymm (le_of_not_gt hn) hw.det3_nonneg
    have hlinear : p.hurwitzDet4 =
        p.c4 * p.hurwitzDet3 -
          p.c5 * (p.c2 * p.hurwitzDet2 - p.gap) := by
      dsimp [hurwitzDet4, hurwitzDet2, gap]
      ring
    rw [hz] at hlinear
    have hT : p.c2 * p.hurwitzDet2 - p.gap < 0 := by
      by_contra hnT
      have hT0 : 0 ≤ p.c2 * p.hurwitzDet2 - p.gap :=
        le_of_not_gt hnT
      have hprod := mul_nonneg (le_of_lt hc5) hT0
      nlinarith
    have hresult := p.det4_resultant_identity
    have hprod := mul_neg_of_pos_of_neg hM hT
    have hterm := mul_pos hc4 (sq_pos_of_pos hD)
    nlinarith
  exact ⟨hc1, hc2, hc3, hc4, hc5, hD, hdet3, hdet4⟩

private def stabilityMargin (p : MonicQuinticCoeff) : ℝ :=
  min p.c1 (min p.c2 (min p.c3 (min p.c4 (min p.c5
    (min p.hurwitzDet2 (min p.hurwitzDet3 (min p.hurwitzDet4
      (min p.gap (min p.slope (p.c2 ^ 2 - 4 * p.c4))))))))))

private lemma stabilityMargin_pos_of_hurwitz
    {p : MonicQuinticCoeff} (hp : p.Hurwitz) :
    0 < p.stabilityMargin := by
  simp only [stabilityMargin, lt_min_iff]
  exact ⟨hp.c1_pos, hp.c2_pos, hp.c3_pos, hp.c4_pos,
    hp.c5_pos, hp.det2_pos, hp.det3_pos, hp.det4_pos,
    gap_pos hp, slope_pos hp, odd_discriminant_pos hp⟩

private lemma hurwitz_of_stabilityMargin_pos
    {p : MonicQuinticCoeff} (h : 0 < p.stabilityMargin) :
    p.Hurwitz := by
  simp only [stabilityMargin, lt_min_iff] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

private lemma weak_of_stabilityMargin_nonneg
    {p : MonicQuinticCoeff} (h : 0 ≤ p.stabilityMargin) :
    p.WeakHurwitz := by
  simp only [stabilityMargin, le_min_iff] at h
  rcases h with ⟨h1, h2, h3, h4, h5, hD2, hD3, hD4,
    hgap, hslope, hdisc⟩
  exact ⟨h1, h2, h3, h4, h5, hD2, hD3, hD4,
    hgap, hslope, hdisc⟩

private lemma stabilityMargin_convex_continuous
    (p q : MonicQuinticCoeff) :
    Continuous (fun t : ℝ => (p.convex q t).stabilityMargin) := by
  dsimp [stabilityMargin, convex, hurwitzDet2, hurwitzDet3,
    hurwitzDet4, gap, slope]
  fun_prop

theorem allConvexHurwitz_of_no_axis
    {p q : MonicQuinticCoeff} (hp : p.Hurwitz)
    (hno : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∀ ω : ℝ, (p.convex q t).evalJW ω ≠ 0) :
    p.allConvexHurwitz q := by
  intro t ht0 ht1
  by_contra hn
  let f : ℝ → ℝ := fun r => (p.convex q r).stabilityMargin
  have hcont : Continuous f := stabilityMargin_convex_continuous p q
  have hf0 : 0 < f 0 := by
    simpa [f] using stabilityMargin_pos_of_hurwitz hp
  have hft : f t ≤ 0 := le_of_not_gt (fun hpos =>
    hn (hurwitz_of_stabilityMargin_pos hpos))
  have hmem : 0 ∈ Set.Icc (f t) (f 0) :=
    ⟨hft, le_of_lt hf0⟩
  obtain ⟨r, hrmem, hrzero⟩ :=
    (intermediate_value_Icc' ht0 hcont.continuousOn) hmem
  have hr0 : 0 ≤ r := hrmem.1
  have hr1 : r ≤ 1 := le_trans hrmem.2 ht1
  have hw : (p.convex q r).WeakHurwitz := by
    apply weak_of_stabilityMargin_nonneg
    change 0 ≤ f r
    rw [hrzero]
  have hstable : (p.convex q r).Hurwitz :=
    hurwitz_of_weak_no_axis hw (hno r hr0 hr1)
  have hpositive := stabilityMargin_pos_of_hurwitz hstable
  change 0 < f r at hpositive
  rw [hrzero] at hpositive
  linarith

theorem allConvexHurwitz_of_common_monicSPR5
    {p q : MonicQuinticCoeff}
    (hcommon : p.ExistsCommonMonicSPR5 q) :
    p.allConvexHurwitz q :=
  allConvexHurwitz_of_no_axis
    (by rcases hcommon with ⟨n, hp, hq⟩; exact hp.1)
    (fun t ht0 ht1 ω =>
      common_monicSPR5_segment_evalJW_ne_zero hcommon t ht0 ht1 ω)

/-! ## 2. 频率紧化：把公共分子写成凸分离问题 -/

abbrev QuinticNumeratorVector := Fin 6 → ℝ

def vectorNumeratorEven (b : QuinticNumeratorVector) (t : ℝ) : ℝ :=
  b 1 * t ^ 2 - b 3 * t + b 5

def vectorNumeratorOdd (b : QuinticNumeratorVector) (t : ℝ) : ℝ :=
  b 0 * t ^ 2 - b 2 * t + b 4

def vectorCross (p : MonicQuinticCoeff)
    (b : QuinticNumeratorVector) (t : ℝ) : ℝ :=
  p.evenPart t * vectorNumeratorEven b t +
    t * p.oddPart t * vectorNumeratorOdd b t

def monicNumeratorVector (n : MonicQuinticCoeff) :
    QuinticNumeratorVector :=
  fun i => match i.1 with
    | 0 => 1
    | 1 => n.c1
    | 2 => n.c2
    | 3 => n.c3
    | 4 => n.c4
    | _ => n.c5

@[simp] lemma monicNumeratorVector_zero (n : MonicQuinticCoeff) :
    n.monicNumeratorVector 0 = 1 := rfl

lemma vectorCross_monic
    (p n : MonicQuinticCoeff) (t : ℝ) :
    p.vectorCross n.monicNumeratorVector t = p.perturbCross n t := by
  unfold vectorCross vectorNumeratorEven vectorNumeratorOdd
    monicNumeratorVector perturbCross evenPart oddPart
  ring

def normalizedNumeratorVector (b : QuinticNumeratorVector) :
    MonicQuinticCoeff :=
  ⟨b 1 / b 0, b 2 / b 0, b 3 / b 0,
    b 4 / b 0, b 5 / b 0⟩

lemma perturbCross_normalizedNumeratorVector
    (p : MonicQuinticCoeff) (b : QuinticNumeratorVector)
    (hb : b 0 ≠ 0) (t : ℝ) :
    p.perturbCross (normalizedNumeratorVector b) t =
      p.vectorCross b t / b 0 := by
  unfold normalizedNumeratorVector perturbCross vectorCross
    vectorNumeratorEven vectorNumeratorOdd evenPart oddPart
  field_simp [hb]; ring
  all_goals simp

def quinticFrequencyFeature (p : MonicQuinticCoeff) (t : ℝ) :
    QuinticNumeratorVector :=
  fun i => match i.1 with
    | 0 => t ^ 3 * p.oddPart t
    | 1 => t ^ 2 * p.evenPart t
    | 2 => -(t ^ 2 * p.oddPart t)
    | 3 => -(t * p.evenPart t)
    | 4 => t * p.oddPart t
    | _ => p.evenPart t

def quinticDot (b v : QuinticNumeratorVector) : ℝ :=
  ∑ i, b i * v i

lemma quinticDot_frequencyFeature
    (p : MonicQuinticCoeff) (b : QuinticNumeratorVector) (t : ℝ) :
    quinticDot b (quinticFrequencyFeature p t) = p.vectorCross b t := by
  simp [quinticDot, quinticFrequencyFeature, vectorCross,
    vectorNumeratorEven, vectorNumeratorOdd, Fin.sum_univ_succ]
  ring

def compactEvenPart (p : MonicQuinticCoeff) (x : ℝ) : ℝ :=
  p.c1 * x ^ 2 - p.c3 * x * (1 - x) + p.c5 * (1 - x) ^ 2

def compactOddPart (p : MonicQuinticCoeff) (x : ℝ) : ℝ :=
  x ^ 2 - p.c2 * x * (1 - x) + p.c4 * (1 - x) ^ 2

def compactQuinticFeature (p : MonicQuinticCoeff) (x : ℝ) :
    QuinticNumeratorVector :=
  fun i => match i.1 with
    | 0 => x ^ 3 * p.compactOddPart x
    | 1 => x ^ 2 * (1 - x) * p.compactEvenPart x
    | 2 => -(x ^ 2 * (1 - x) * p.compactOddPart x)
    | 3 => -(x * (1 - x) ^ 2 * p.compactEvenPart x)
    | 4 => x * (1 - x) ^ 2 * p.compactOddPart x
    | _ => (1 - x) ^ 3 * p.compactEvenPart x

@[simp] lemma compactQuinticFeature_one (p : MonicQuinticCoeff) :
    p.compactQuinticFeature 1 = Pi.single 0 1 := by
  ext i
  fin_cases i <;>
    simp [compactQuinticFeature, compactEvenPart, compactOddPart,
      Pi.single_apply]

lemma continuous_compactQuinticFeature (p : MonicQuinticCoeff) :
    Continuous p.compactQuinticFeature := by
  apply continuous_pi
  intro i
  fin_cases i <;>
    simp only [compactQuinticFeature, compactEvenPart, compactOddPart] <;>
      fun_prop

lemma continuous_compactQuinticFeature_convex
    (p q : MonicQuinticCoeff) :
    Continuous (fun ux : ℝ × ℝ =>
      (p.convex q ux.1).compactQuinticFeature ux.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;>
    simp only [compactQuinticFeature, compactEvenPart, compactOddPart,
      convex] <;> fun_prop

lemma compactQuinticFeature_eq
    (p : MonicQuinticCoeff) {x : ℝ} (hx : x ≠ 1) :
    p.compactQuinticFeature x =
      (1 - x) ^ 5 • p.quinticFrequencyFeature (x / (1 - x)) := by
  have hd : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  ext i
  fin_cases i <;>
    simp only [compactQuinticFeature, quinticFrequencyFeature,
      compactEvenPart, compactOddPart, evenPart, oddPart,
      Pi.smul_apply, smul_eq_mul] <;> field_simp [hd] <;> ring

lemma quinticDot_smul
    (b v : QuinticNumeratorVector) (r : ℝ) :
    quinticDot b (r • v) = r * quinticDot b v := by
  simp only [quinticDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma compactQuinticPairing_eq
    (p : MonicQuinticCoeff) (b : QuinticNumeratorVector)
    {x : ℝ} (hx : x ≠ 1) :
    quinticDot b (p.compactQuinticFeature x) =
      (1 - x) ^ 5 * p.vectorCross b (x / (1 - x)) := by
  rw [compactQuinticFeature_eq p hx, quinticDot_smul,
    quinticDot_frequencyFeature]

lemma compactQuinticPairing_pos_iff
    (p : MonicQuinticCoeff) (b : QuinticNumeratorVector) :
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < quinticDot b (p.compactQuinticFeature x)) ↔
      0 < b 0 ∧ ∀ t : ℝ, 0 ≤ t → 0 < p.vectorCross b t := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [quinticDot, Fin.sum_univ_succ] using
        h 1 ⟨zero_le_one, le_rfl⟩
    · intro t ht
      have hd : 0 < 1 + t := by linarith
      have hx : t / (1 + t) < 1 :=
        (div_lt_one hd).mpr (by linarith)
      have hc := h (t / (1 + t))
        ⟨div_nonneg ht hd.le, hx.le⟩
      rw [compactQuinticPairing_eq p b (ne_of_lt hx)] at hc
      have hid : t / (1 + t) /
          (1 - t / (1 + t)) = t := by
        field_simp
      rw [hid] at hc
      exact (mul_pos_iff_of_pos_left
        (pow_pos (sub_pos.mpr hx) 5)).mp hc
  · rintro ⟨hb, hcross⟩ x ⟨hx0, hx1⟩
    by_cases hx : x = 1
    · subst x
      simpa [quinticDot, Fin.sum_univ_succ] using hb
    · have hlt : x < 1 := lt_of_le_of_ne hx1 hx
      rw [compactQuinticPairing_eq p b hx]
      exact mul_pos (pow_pos (sub_pos.mpr hlt) 5)
        (hcross _ (div_nonneg hx0 (sub_nonneg.mpr hx1)))

def endpointQuinticFeatureSet
    (p q : MonicQuinticCoeff) : Set QuinticNumeratorVector :=
  p.compactQuinticFeature '' Set.Icc (0 : ℝ) 1 ∪
    q.compactQuinticFeature '' Set.Icc (0 : ℝ) 1

def selectedEndpoint (p q : MonicQuinticCoeff) (right : Bool) :
    MonicQuinticCoeff :=
  if right then q else p

lemma mem_endpointQuinticFeatureSet_iff
    {p q : MonicQuinticCoeff} {v : QuinticNumeratorVector} :
    v ∈ p.endpointQuinticFeatureSet q ↔
      ∃ right : Bool, ∃ x ∈ Set.Icc (0 : ℝ) 1,
        v = (p.selectedEndpoint q right).compactQuinticFeature x := by
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨false, x, hx, by simp [selectedEndpoint]⟩
    · exact ⟨true, x, hx, by simp [selectedEndpoint]⟩
  · rintro ⟨right, x, hx, rfl⟩
    cases right <;> simp [selectedEndpoint, endpointQuinticFeatureSet,
      Set.mem_image_of_mem _ hx]

lemma compact_endpointQuinticFeatureSet (p q : MonicQuinticCoeff) :
    IsCompact (p.endpointQuinticFeatureSet q) := by
  exact (isCompact_Icc.image p.continuous_compactQuinticFeature).union
    (isCompact_Icc.image q.continuous_compactQuinticFeature)

lemma endpointQuinticFeatureSet_nonempty (p q : MonicQuinticCoeff) :
    (p.endpointQuinticFeatureSet q).Nonempty := by
  refine ⟨p.compactQuinticFeature 0, Or.inl ?_⟩
  exact Set.mem_image_of_mem _ ⟨le_rfl, zero_le_one⟩

def quinticDotCLM (b : QuinticNumeratorVector) :
    QuinticNumeratorVector →L[ℝ] ℝ :=
  ∑ i : Fin 6, b i • ContinuousLinearMap.proj i

lemma quinticDotCLM_apply
    (b v : QuinticNumeratorVector) :
    quinticDotCLM b v = quinticDot b v := by
  simp [quinticDotCLM, quinticDot, ContinuousLinearMap.sum_apply]

lemma quinticDual_eq_dot
    (f : QuinticNumeratorVector →L[ℝ] ℝ)
    (v : QuinticNumeratorVector) :
    f v = quinticDot (fun i => f (Pi.single i 1)) v := by
  have hbasis (i : Fin 6) :
      (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
    ext j
    by_cases h : i = j
    · subst j
      simp
    · simp [h]
  calc
    f v = f (∑ i, (v i) • fun j => if i = j then (1 : ℝ) else 0) := by
      rw [← pi_eq_sum_univ v]
    _ = ∑ i, (v i) • f (Pi.single i 1) := by
      simp only [map_sum, map_smul, hbasis]
    _ = quinticDot (fun i => f (Pi.single i 1)) v := by
      simp only [quinticDot, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem endpoint_cross_separator_iff
    (p q : MonicQuinticCoeff) :
    (∃ b : QuinticNumeratorVector, 0 < b 0 ∧
      (∀ t : ℝ, 0 ≤ t → 0 < p.vectorCross b t) ∧
      (∀ t : ℝ, 0 ≤ t → 0 < q.vectorCross b t)) ↔
      (0 : QuinticNumeratorVector) ∉
        closedConvexHull ℝ (p.endpointQuinticFeatureSet q) := by
  let S := p.endpointQuinticFeatureSet q
  have hcompact : IsCompact S := compact_endpointQuinticFeatureSet p q
  have hnonempty : S.Nonempty := endpointQuinticFeatureSet_nonempty p q
  have hsep :
      (∃ b : QuinticNumeratorVector, ∀ v ∈ S, 0 < quinticDot b v) ↔
        (0 : QuinticNumeratorVector) ∉ closedConvexHull ℝ S := by
    constructor
    · rintro ⟨b, hb⟩ hzero
      obtain ⟨v, hv, hmin⟩ := hcompact.exists_isMinOn hnonempty
        (quinticDotCLM b).continuous.continuousOn
      have hpos : 0 < quinticDotCLM b v := by
        simpa only [quinticDotCLM_apply] using hb v hv
      have hsub : closedConvexHull ℝ S ⊆
          {w | quinticDotCLM b v ≤ quinticDotCLM b w} := by
        apply closedConvexHull_min
        · simpa only [quinticDotCLM_apply] using hmin
        · exact convex_halfSpace_ge
            (quinticDotCLM b).toLinearMap.isLinear _
        · exact isClosed_le continuous_const (quinticDotCLM b).continuous
      have hz := hsub hzero
      simp only [Set.mem_setOf_eq, map_zero] at hz
      exact (not_le_of_gt hpos) hz
    · intro hzero
      obtain ⟨f, u, hu, hf⟩ := geometric_hahn_banach_point_closed
        (convex_closedConvexHull (𝕜 := ℝ) (s := S))
        isClosed_closedConvexHull hzero
      refine ⟨fun i => f (Pi.single i 1), ?_⟩
      intro v hv
      rw [← quinticDual_eq_dot]
      have hstrict := hu.trans (hf v (subset_closedConvexHull hv))
      simpa only [map_zero] using hstrict
  rw [← hsep]
  constructor
  · rintro ⟨b, hb0, hp, hq⟩
    refine ⟨b, ?_⟩
    intro v hv
    rcases hv with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · exact (compactQuinticPairing_pos_iff p b).2 ⟨hb0, hp⟩ x hx
    · exact (compactQuinticPairing_pos_iff q b).2 ⟨hb0, hq⟩ x hx
  · rintro ⟨b, hb⟩
    have hp := (compactQuinticPairing_pos_iff p b).1
      (fun x hx => hb _ (Or.inl (Set.mem_image_of_mem _ hx)))
    have hq := (compactQuinticPairing_pos_iff q b).1
      (fun x hx => hb _ (Or.inr (Set.mem_image_of_mem _ hx)))
    exact ⟨b, hp.1, hp.2, hq.2⟩

/-! ## 3. 无原子数上界的有限矩证书与留数插值工具 -/

structure EndpointMomentCertificate
    (p q : MonicQuinticCoeff) where
  atomCount : ℕ
  rightEndpoint : Fin atomCount → Bool
  compactFrequency : Fin atomCount → ℝ
  weight : Fin atomCount → ℝ
  frequency_mem : ∀ i, compactFrequency i ∈ Set.Icc (0 : ℝ) 1
  weight_pos : ∀ i, 0 < weight i
  weight_sum : (∑ i, weight i) = 1
  balance : (∑ i, weight i •
    (p.selectedEndpoint q (rightEndpoint i)).compactQuinticFeature
      (compactFrequency i)) = 0

lemma EndpointMomentCertificate.balance_coordinate
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    (j : Fin 6) :
    (∑ i, C.weight i *
      (p.selectedEndpoint q (C.rightEndpoint i)).compactQuinticFeature
        (C.compactFrequency i) j) = 0 := by
  have h := congrFun C.balance j
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply] using h

lemma EndpointMomentCertificate.exists_frequency_lt_one
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    ∃ i, C.compactFrequency i < 1 := by
  by_contra h
  push_neg at h
  have hx1 : ∀ i, C.compactFrequency i = 1 := by
    intro i
    exact le_antisymm (C.frequency_mem i).2 (h i)
  have hcoord := C.balance_coordinate 0
  simp only [hx1, compactQuinticFeature_one, Pi.single_apply,
    Fin.isValue, if_pos, mul_one] at hcoord
  rw [C.weight_sum] at hcoord
  norm_num at hcoord

def EndpointMomentCertificate.finiteIndices
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    Finset (Fin C.atomCount) :=
  Finset.univ.filter (fun i => C.compactFrequency i < 1)

def EndpointMomentCertificate.infiniteIndices
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    Finset (Fin C.atomCount) :=
  Finset.univ.filter (fun i => ¬ C.compactFrequency i < 1)

@[simp] lemma EndpointMomentCertificate.mem_finiteIndices
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    (i : Fin C.atomCount) :
    i ∈ C.finiteIndices ↔ C.compactFrequency i < 1 := by
  simp [finiteIndices]

@[simp] lemma EndpointMomentCertificate.mem_infiniteIndices
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    (i : Fin C.atomCount) :
    i ∈ C.infiniteIndices ↔ ¬ C.compactFrequency i < 1 := by
  simp [infiniteIndices]

lemma EndpointMomentCertificate.finiteIndices_nonempty
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    C.finiteIndices.Nonempty := by
  obtain ⟨i, hi⟩ := C.exists_frequency_lt_one
  exact ⟨i, by simp [finiteIndices, hi]⟩

def EndpointMomentCertificate.finiteFrequency
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    (i : Fin C.atomCount) : ℝ :=
  C.compactFrequency i / (1 - C.compactFrequency i)

def EndpointMomentCertificate.finiteWeight
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    (i : Fin C.atomCount) : ℝ :=
  C.weight i * (1 - C.compactFrequency i) ^ 5

lemma EndpointMomentCertificate.finiteFrequency_nonneg
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    {i : Fin C.atomCount} (_hi : i ∈ C.finiteIndices) :
    0 ≤ C.finiteFrequency i := by
  exact div_nonneg (C.frequency_mem i).1
    (sub_nonneg.mpr (C.frequency_mem i).2)

lemma EndpointMomentCertificate.finiteWeight_pos
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    {i : Fin C.atomCount} (hi : i ∈ C.finiteIndices) :
    0 < C.finiteWeight i := by
  exact mul_pos (C.weight_pos i)
    (pow_pos (sub_pos.mpr ((mem_finiteIndices C i).mp hi)) 5)

lemma EndpointMomentCertificate.decompactified_balance
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    (∑ i ∈ C.finiteIndices, C.finiteWeight i •
      (p.selectedEndpoint q (C.rightEndpoint i)).quinticFrequencyFeature
        (C.finiteFrequency i)) +
      (∑ i ∈ C.infiniteIndices, C.weight i) •
        (Pi.single (0 : Fin 6) (1 : ℝ) : QuinticNumeratorVector) = 0 := by
  calc
    _ = (∑ i ∈ C.finiteIndices, C.weight i •
          (p.selectedEndpoint q (C.rightEndpoint i)).compactQuinticFeature
            (C.compactFrequency i)) +
        (∑ i ∈ C.infiniteIndices, C.weight i •
          (p.selectedEndpoint q (C.rightEndpoint i)).compactQuinticFeature
            (C.compactFrequency i)) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        rw [compactQuinticFeature_eq _
          (ne_of_lt ((mem_finiteIndices C i).mp hi))]
        simp only [finiteWeight, finiteFrequency, smul_smul]
      · rw [Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro i hi
        have hxi : C.compactFrequency i = 1 := by
          exact le_antisymm (C.frequency_mem i).2
            (le_of_not_gt ((mem_infiniteIndices C i).mp hi))
        simp [hxi]
    _ = ∑ i, C.weight i •
          (p.selectedEndpoint q (C.rightEndpoint i)).compactQuinticFeature
            (C.compactFrequency i) := by
      exact Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i => C.compactFrequency i < 1)
        (fun i => C.weight i •
          (p.selectedEndpoint q (C.rightEndpoint i)).compactQuinticFeature
            (C.compactFrequency i))
    _ = 0 := C.balance

structure CriticalEndpointMomentCertificate
    (p q : MonicQuinticCoeff) where
  certificate : EndpointMomentCertificate p q
  support : QuinticNumeratorVector
  support_ne : support ≠ 0
  support_nonneg : ∀ right : Bool, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    0 ≤ quinticDot support
      ((p.selectedEndpoint q right).compactQuinticFeature x)
  contact : ∀ i, quinticDot support
    ((p.selectedEndpoint q (certificate.rightEndpoint i)).compactQuinticFeature
      (certificate.compactFrequency i)) = 0

lemma CriticalEndpointMomentCertificate.support_leading_nonneg
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q) :
    0 ≤ C.support 0 := by
  have h := C.support_nonneg false 1 ⟨zero_le_one, le_rfl⟩
  simpa [quinticDot, Fin.sum_univ_succ] using h

lemma CriticalEndpointMomentCertificate.support_cross_nonneg
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (right : Bool) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (p.selectedEndpoint q right).vectorCross C.support t := by
  have hd : 0 < 1 + t := by linarith
  have hxlt : t / (1 + t) < 1 :=
    (div_lt_one hd).mpr (by linarith)
  have hxmem : t / (1 + t) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht hd.le, hxlt.le⟩
  have h := C.support_nonneg right (t / (1 + t)) hxmem
  rw [compactQuinticPairing_eq _ C.support (ne_of_lt hxlt)] at h
  have harg : t / (1 + t) / (1 - t / (1 + t)) = t := by
    field_simp
  rw [harg] at h
  exact (mul_nonneg_iff_of_pos_left
    (pow_pos (sub_pos.mpr hxlt) 5)).mp h

lemma CriticalEndpointMomentCertificate.support_cross_nonneg_convex
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (p.convex q u).vectorCross C.support t := by
  have hp := C.support_cross_nonneg false t ht
  have hq := C.support_cross_nonneg true t ht
  simp only [selectedEndpoint, Bool.false_eq_true, if_false] at hp
  simp only [selectedEndpoint, if_true] at hq
  have hid : (p.convex q u).vectorCross C.support t =
      (1 - u) * p.vectorCross C.support t +
        u * q.vectorCross C.support t := by
    unfold vectorCross
    rw [evenPart_convex, oddPart_convex]
    ring
  rw [hid]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hu.2) hp)
    (mul_nonneg hu.1 hq)

lemma CriticalEndpointMomentCertificate.finite_contact_cross
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    {i : Fin C.certificate.atomCount}
    (hi : i ∈ C.certificate.finiteIndices) :
    (p.selectedEndpoint q (C.certificate.rightEndpoint i)).vectorCross
      C.support (C.certificate.finiteFrequency i) = 0 := by
  have hcontact := C.contact i
  have hxlt := (EndpointMomentCertificate.mem_finiteIndices
    C.certificate i).mp hi
  rw [compactQuinticPairing_eq _ C.support (ne_of_lt hxlt)] at hcontact
  exact (mul_eq_zero.mp hcontact).resolve_left
    (ne_of_gt (pow_pos (sub_pos.mpr hxlt) 5))

lemma CriticalEndpointMomentCertificate.support_constant_nonneg
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (hp : p.Hurwitz) :
    0 ≤ C.support 5 := by
  have h := C.support_cross_nonneg false 0 (by norm_num)
  simp only [selectedEndpoint, Bool.false_eq_true, if_false] at h
  unfold vectorCross vectorNumeratorEven vectorNumeratorOdd
    evenPart oddPart at h
  norm_num at h
  exact (mul_nonneg_iff_of_pos_left hp.c5_pos).mp h

lemma CriticalEndpointMomentCertificate.support_coefficients_nonneg
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (hp : p.Hurwitz) :
    0 ≤ C.support 0 ∧ 0 ≤ C.support 1 ∧
      0 ≤ C.support 2 ∧ 0 ≤ C.support 3 ∧
        0 ≤ C.support 4 ∧ 0 ≤ C.support 5 := by
  obtain ⟨D⟩ := denominator_interlacing_of_hurwitz hp
  have he₂pos : 0 < D.e₂ :=
    D.ordered.1.trans (D.ordered.2.1.trans D.ordered.2.2.1)
  have ho₁pos : 0 < D.o₁ := D.ordered.1.trans D.ordered.2.1
  have ho₂pos : 0 < D.o₂ := he₂pos.trans D.ordered.2.2.2
  have hOdd₁raw := C.support_cross_nonneg false D.e₁ D.ordered.1.le
  have hOdd₂raw := C.support_cross_nonneg false D.e₂ he₂pos.le
  have hEven₁raw := C.support_cross_nonneg false D.o₁ ho₁pos.le
  have hEven₂raw := C.support_cross_nonneg false D.o₂ ho₂pos.le
  simp only [selectedEndpoint, Bool.false_eq_true, if_false] at hOdd₁raw hOdd₂raw hEven₁raw hEven₂raw
  unfold vectorCross at hOdd₁raw hOdd₂raw hEven₁raw hEven₂raw
  rw [D.roots.1] at hOdd₁raw
  rw [D.roots.2.2.1] at hOdd₂raw
  rw [D.roots.2.1] at hEven₁raw
  rw [D.roots.2.2.2] at hEven₂raw
  simp only [zero_mul, zero_add, mul_zero, add_zero] at hOdd₁raw hOdd₂raw hEven₁raw hEven₂raw
  have hOdd₁ : 0 ≤ vectorNumeratorOdd C.support D.e₁ := by
    exact (mul_nonneg_iff_of_pos_left
      (mul_pos D.ordered.1 D.odd_e₁_pos)).mp hOdd₁raw
  have hOdd₂ : vectorNumeratorOdd C.support D.e₂ ≤ 0 := by
    apply le_of_not_gt
    intro hpos
    have hneg := mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg he₂pos D.odd_e₂_neg) hpos
    linarith
  have hEven₁ : vectorNumeratorEven C.support D.o₁ ≤ 0 := by
    apply le_of_not_gt
    intro hpos
    have hneg := mul_neg_of_neg_of_pos (D.even_o₁_neg hp) hpos
    linarith
  have hEven₂ : 0 ≤ vectorNumeratorEven C.support D.o₂ := by
    exact (mul_nonneg_iff_of_pos_left (D.even_o₂_pos hp)).mp hEven₂raw
  have hb0 := C.support_leading_nonneg
  have hb5 := C.support_constant_nonneg hp
  change 0 ≤ C.support 0 * D.e₁ ^ 2 - C.support 2 * D.e₁ +
    C.support 4 at hOdd₁
  change C.support 0 * D.e₂ ^ 2 - C.support 2 * D.e₂ +
    C.support 4 ≤ 0 at hOdd₂
  change C.support 1 * D.o₁ ^ 2 - C.support 3 * D.o₁ +
    C.support 5 ≤ 0 at hEven₁
  change 0 ≤ C.support 1 * D.o₂ ^ 2 - C.support 3 * D.o₂ +
    C.support 5 at hEven₂
  have hb1 : 0 ≤ C.support 1 :=
    quadratic_leading_nonneg_of_weak_signs ho₁pos
      (D.ordered.2.2.1.trans D.ordered.2.2.2) hb5 hEven₁ hEven₂
  have hb2 : 0 ≤ C.support 2 :=
    quadratic_middle_nonneg_of_weak_signs D.ordered.1
      (D.ordered.2.1.trans D.ordered.2.2.1) hb0 hOdd₁ hOdd₂
  have hb4 : 0 ≤ C.support 4 :=
    quadratic_constant_nonneg_of_weak_signs D.ordered.1
      (D.ordered.2.1.trans D.ordered.2.2.1) hb0 hOdd₁ hOdd₂
  have hb3 : 0 ≤ C.support 3 := by
    by_contra h
    have hb3neg : C.support 3 < 0 := lt_of_not_ge h
    have hlead := mul_nonneg hb1 (sq_nonneg D.o₁)
    have hmiddle : 0 < -(C.support 3) * D.o₁ :=
      mul_pos (neg_pos.mpr hb3neg) ho₁pos
    nlinarith
  exact ⟨hb0, hb1, hb2, hb3, hb4, hb5⟩

                                                                        

                                                              

open Polynomial Finset

lemma rootMultiplicity_two_le_of_nonneg_of_pos_root
    (P : Polynomial ℝ) (hP : P ≠ 0)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ P.eval t)
    {r : ℝ} (hrpos : 0 < r) (hrroot : P.eval r = 0) :
    2 ≤ P.rootMultiplicity r := by
  have hlocal : IsLocalMin P.eval r := by
    filter_upwards [Ioi_mem_nhds hrpos] with t ht
    rw [hrroot]
    exact hnonneg t ht.le
  have hderiv : P.derivative.eval r = 0 := by
    rw [← P.deriv]
    exact hlocal.deriv_eq_zero
  exact (P.one_lt_rootMultiplicity_iff_isRoot hP).mpr
    ⟨hrroot, hderiv⟩

def positiveRealRoots (P : Polynomial ℝ) : Finset ℝ :=
  P.roots.toFinset.filter (fun r => 0 < r)

lemma twice_card_positiveRealRoots_le_natDegree
    (P : Polynomial ℝ) (hP : P ≠ 0)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ P.eval t) :
    2 * (positiveRealRoots P).card ≤ P.natDegree := by
  have hcount : ∀ r ∈ positiveRealRoots P, 2 ≤ P.roots.count r := by
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    rw [Polynomial.count_roots]
    exact rootMultiplicity_two_le_of_nonneg_of_pos_root P hP hnonneg
      hr'.2 ((Polynomial.mem_roots hP).mp
        (Multiset.mem_toFinset.mp hr'.1))
  calc
    2 * (positiveRealRoots P).card =
        ∑ r ∈ positiveRealRoots P, 2 := by
      rw [mul_comm]
      simp
    _ ≤ ∑ r ∈ positiveRealRoots P, P.roots.count r :=
      Finset.sum_le_sum hcount
    _ ≤ ∑ r ∈ P.roots.toFinset, P.roots.count r := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)
    _ = P.roots.card := Multiset.toFinset_sum_count_eq P.roots
    _ ≤ P.natDegree := Polynomial.card_roots' P

def nonnegativeRealRoots (P : Polynomial ℝ) : Finset ℝ :=
  P.roots.toFinset.filter (fun r => 0 ≤ r)

lemma nonnegativeRealRoots_subset_insert_zero_positiveRealRoots
    (P : Polynomial ℝ) :
    nonnegativeRealRoots P ⊆ insert 0 (positiveRealRoots P) := by
  intro r hr
  have hr' := Finset.mem_filter.mp hr
  rw [Finset.mem_insert]
  rcases hr'.2.eq_or_lt with hrzero | hrpos
  · exact Or.inl hrzero.symm
  · exact Or.inr (Finset.mem_filter.mpr ⟨hr'.1, hrpos⟩)

lemma twice_card_positiveRealRoots_add_one_le_natDegree_of_zero_root
    (P : Polynomial ℝ) (hP : P ≠ 0)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ P.eval t)
    (hzero : P.eval 0 = 0) :
    2 * (positiveRealRoots P).card + 1 ≤ P.natDegree := by
  have hcount : ∀ r ∈ positiveRealRoots P, 2 ≤ P.roots.count r := by
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    rw [Polynomial.count_roots]
    exact rootMultiplicity_two_le_of_nonneg_of_pos_root P hP hnonneg
      hr'.2 ((Polynomial.mem_roots hP).mp
        (Multiset.mem_toFinset.mp hr'.1))
  have hpossum : 2 * (positiveRealRoots P).card ≤
      ∑ r ∈ positiveRealRoots P, P.roots.count r := by
    calc
      2 * (positiveRealRoots P).card =
          ∑ r ∈ positiveRealRoots P, 2 := by
        rw [mul_comm]
        simp
      _ ≤ _ := Finset.sum_le_sum hcount
  have hzeroMem : 0 ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact hzero
  have hzeroCount : 1 ≤ P.roots.count 0 :=
    Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hzeroMem)
  have hzeroNotPos : 0 ∉ positiveRealRoots P := by
    simp [positiveRealRoots]
  have hsubset : insert 0 (positiveRealRoots P) ⊆ P.roots.toFinset := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hzeroMem
    · exact (Finset.mem_filter.mp hr).1
  have hsumall :
      ∑ r ∈ insert 0 (positiveRealRoots P), P.roots.count r ≤
        P.roots.card := by
    calc
      _ ≤ ∑ r ∈ P.roots.toFinset, P.roots.count r :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun _ _ _ => Nat.zero_le _)
      _ = P.roots.card := Multiset.toFinset_sum_count_eq P.roots
  rw [Finset.sum_insert hzeroNotPos] at hsumall
  exact le_trans (by omega) (Polynomial.card_roots' P)

lemma nonnegativeRealRoots_card_le_two_of_degree_le_four
    (P : Polynomial ℝ) (hP : P ≠ 0)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ P.eval t)
    (hdegree : P.natDegree ≤ 4) :
    (nonnegativeRealRoots P).card ≤ 2 := by
  have hsub := nonnegativeRealRoots_subset_insert_zero_positiveRealRoots P
  by_cases hzero : P.eval 0 = 0
  · have hrootbound :=
      twice_card_positiveRealRoots_add_one_le_natDegree_of_zero_root
        P hP hnonneg hzero
    have hcard : (nonnegativeRealRoots P).card ≤
        (positiveRealRoots P).card + 1 := by
      calc
        _ ≤ (insert 0 (positiveRealRoots P)).card := Finset.card_le_card hsub
        _ ≤ (positiveRealRoots P).card + 1 := Finset.card_insert_le _ _
    omega
  · have hsubpos : nonnegativeRealRoots P ⊆ positiveRealRoots P := by
      intro r hr
      have hr' := Finset.mem_filter.mp hr
      apply Finset.mem_filter.mpr
      have hrne : r ≠ 0 := by
        intro hrzero
        subst r
        exact hzero ((Polynomial.mem_roots hP).mp
          (Multiset.mem_toFinset.mp hr'.1))
      exact ⟨hr'.1, lt_of_le_of_ne hr'.2 (Ne.symm hrne)⟩
    have htwice := twice_card_positiveRealRoots_le_natDegree P hP hnonneg
    have hcard := Finset.card_le_card hsubpos
    omega

lemma union_nonnegativeRealRoots_card_le_four_of_degree_le_four
    (P Q : Polynomial ℝ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hnonnegP : ∀ t : ℝ, 0 ≤ t → 0 ≤ P.eval t)
    (hnonnegQ : ∀ t : ℝ, 0 ≤ t → 0 ≤ Q.eval t)
    (hdegreeP : P.natDegree ≤ 4) (hdegreeQ : Q.natDegree ≤ 4) :
    (nonnegativeRealRoots P ∪ nonnegativeRealRoots Q).card ≤ 4 := by
  have hPcard := nonnegativeRealRoots_card_le_two_of_degree_le_four
    P hP hnonnegP hdegreeP
  have hQcard := nonnegativeRealRoots_card_le_two_of_degree_le_four
    Q hQ hnonnegQ hdegreeQ
  exact (Finset.card_union_le _ _).trans (by omega)

lemma union_nonnegativeRealRoots_card_le_five_of_degree_le_five
    (P Q : Polynomial ℝ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hnonnegP : ∀ t : ℝ, 0 ≤ t → 0 ≤ P.eval t)
    (hnonnegQ : ∀ t : ℝ, 0 ≤ t → 0 ≤ Q.eval t)
    (hdegreeP : P.natDegree ≤ 5) (hdegreeQ : Q.natDegree ≤ 5) :
    (nonnegativeRealRoots P ∪ nonnegativeRealRoots Q).card ≤ 5 := by
  have hPpos := twice_card_positiveRealRoots_le_natDegree P hP hnonnegP
  have hQpos := twice_card_positiveRealRoots_le_natDegree Q hQ hnonnegQ
  have hsub : nonnegativeRealRoots P ∪ nonnegativeRealRoots Q ⊆
      insert 0 (positiveRealRoots P ∪ positiveRealRoots Q) := by
    intro r hr
    rcases Finset.mem_union.mp hr with hrP | hrQ
    · have := nonnegativeRealRoots_subset_insert_zero_positiveRealRoots P hrP
      rcases Finset.mem_insert.mp this with rfl | hrpos
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_union_left _ hrpos))
    · have := nonnegativeRealRoots_subset_insert_zero_positiveRealRoots Q hrQ
      rcases Finset.mem_insert.mp this with rfl | hrpos
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_union_right _ hrpos))
  calc
    (nonnegativeRealRoots P ∪ nonnegativeRealRoots Q).card ≤
        (insert 0 (positiveRealRoots P ∪ positiveRealRoots Q)).card :=
      Finset.card_le_card hsub
    _ ≤ (positiveRealRoots P ∪ positiveRealRoots Q).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ (positiveRealRoots P).card + (positiveRealRoots Q).card + 1 := by
      exact Nat.add_le_add_right (Finset.card_union_le _ _) 1
    _ ≤ 5 := by omega

lemma polynomial_derivative_zero_nonneg
    (P : Polynomial ℝ)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ P.eval t)
    (hzero : P.eval 0 = 0) :
    0 ≤ P.derivative.eval 0 := by
  have hmin : IsMinOn P.eval (Set.Ici (0 : ℝ)) 0 := by
    intro t ht
    change P.eval 0 ≤ P.eval t
    rw [hzero]
    exact hnonneg t ht
  have hlocal : IsLocalMinOn P.eval (Set.Ici (0 : ℝ)) 0 := hmin.localize
  have htangent : (1 : ℝ) ∈ posTangentConeAt (Set.Ici (0 : ℝ)) 0 := by
    rw [one_mem_posTangentConeAt_iff_mem_closure]
    rw [show Set.Ioi (0 : ℝ) ∩ Set.Ici 0 = Set.Ioi 0 by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, h.le⟩]
    rw [closure_Ioi]
    simp
  have h := hlocal.hasFDerivWithinAt_nonneg
    ((P.hasDerivAt 0).hasDerivWithinAt.hasFDerivWithinAt) htangent
  simpa using h

lemma twice_card_positiveRealRoots_add_two_le_natDegree_of_double_zero
    (P : Polynomial ℝ) (hP : P ≠ 0)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ P.eval t)
    (hzero : P.eval 0 = 0) (hderiv : P.derivative.eval 0 = 0) :
    2 * (positiveRealRoots P).card + 2 ≤ P.natDegree := by
  have hcount : ∀ r ∈ positiveRealRoots P, 2 ≤ P.roots.count r := by
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    rw [Polynomial.count_roots]
    exact rootMultiplicity_two_le_of_nonneg_of_pos_root P hP hnonneg
      hr'.2 ((Polynomial.mem_roots hP).mp
        (Multiset.mem_toFinset.mp hr'.1))
  have hpossum : 2 * (positiveRealRoots P).card ≤
      ∑ r ∈ positiveRealRoots P, P.roots.count r := by
    calc
      2 * (positiveRealRoots P).card =
          ∑ r ∈ positiveRealRoots P, 2 := by
        rw [mul_comm]
        simp
      _ ≤ _ := Finset.sum_le_sum hcount
  have hzeroMem : 0 ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact hzero
  have hzeroCount : 2 ≤ P.roots.count 0 := by
    rw [Polynomial.count_roots]
    exact (P.one_lt_rootMultiplicity_iff_isRoot hP).mpr ⟨hzero, hderiv⟩
  have hzeroNotPos : 0 ∉ positiveRealRoots P := by
    simp [positiveRealRoots]
  have hsubset : insert 0 (positiveRealRoots P) ⊆ P.roots.toFinset := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hzeroMem
    · exact (Finset.mem_filter.mp hr).1
  have hsumall :
      ∑ r ∈ insert 0 (positiveRealRoots P), P.roots.count r ≤
        P.roots.card := by
    calc
      _ ≤ ∑ r ∈ P.roots.toFinset, P.roots.count r :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun _ _ _ => Nat.zero_le _)
      _ = P.roots.card := Multiset.toFinset_sum_count_eq P.roots
  rw [Finset.sum_insert hzeroNotPos] at hsumall
  exact le_trans (by omega) (Polynomial.card_roots' P)

lemma four_le_natDegree_of_three_roots_of_one_double
    (P : Polynomial ℝ) (hP : P ≠ 0) {r x y : ℝ}
    (hrx : r ≠ x) (hry : r ≠ y) (hxy : x ≠ y)
    (hr : P.eval r = 0) (hrderiv : P.derivative.eval r = 0)
    (hx : P.eval x = 0) (hy : P.eval y = 0) :
    4 ≤ P.natDegree := by
  have hrmem : r ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact hr
  have hxmem : x ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact hx
  have hymem : y ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact hy
  have hrCount : 2 ≤ P.roots.count r := by
    rw [Polynomial.count_roots]
    exact (P.one_lt_rootMultiplicity_iff_isRoot hP).mpr ⟨hr, hrderiv⟩
  have hxCount : 1 ≤ P.roots.count x :=
    Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hxmem)
  have hyCount : 1 ≤ P.roots.count y :=
    Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hymem)
  have hsubset : ({r, x, y} : Finset ℝ) ⊆ P.roots.toFinset := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hrmem
    · exact hxmem
    · exact hymem
  have hsumall :
      ∑ z ∈ ({r, x, y} : Finset ℝ), P.roots.count z ≤ P.roots.card := by
    calc
      _ ≤ ∑ z ∈ P.roots.toFinset, P.roots.count z :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun _ _ _ => Nat.zero_le _)
      _ = P.roots.card := Multiset.toFinset_sum_count_eq P.roots
  have hlower : 4 ≤
      ∑ z ∈ ({r, x, y} : Finset ℝ), P.roots.count z := by
    rw [Finset.sum_insert (by simp [hrx, hry]),
      Finset.sum_insert (by simp [hxy]), Finset.sum_singleton]
    omega
  exact (hlower.trans hsumall).trans (Polynomial.card_roots' P)

lemma union_nonnegativeRealRoots_card_le_four_of_shared_positive_root
    (P Q : Polynomial ℝ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hnonnegP : ∀ t : ℝ, 0 ≤ t → 0 ≤ P.eval t)
    (hnonnegQ : ∀ t : ℝ, 0 ≤ t → 0 ≤ Q.eval t)
    (hdegreeP : P.natDegree ≤ 5) (hdegreeQ : Q.natDegree ≤ 5)
    {r : ℝ} (hrpos : 0 < r) (hrP : P.eval r = 0) (hrQ : Q.eval r = 0) :
    (nonnegativeRealRoots P ∪ nonnegativeRealRoots Q).card ≤ 4 := by
  have hPpos := twice_card_positiveRealRoots_le_natDegree P hP hnonnegP
  have hQpos := twice_card_positiveRealRoots_le_natDegree Q hQ hnonnegQ
  have hPcard : (positiveRealRoots P).card ≤ 2 := by omega
  have hQcard : (positiveRealRoots Q).card ≤ 2 := by omega
  have hrPmem : r ∈ positiveRealRoots P := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hrpos⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact hrP
  have hrQmem : r ∈ positiveRealRoots Q := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hrpos⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ]
    exact hrQ
  have hinter : 1 ≤
      (positiveRealRoots P ∩ positiveRealRoots Q).card :=
    Finset.one_le_card.mpr ⟨r, Finset.mem_inter.mpr ⟨hrPmem, hrQmem⟩⟩
  have hposunion :
      (positiveRealRoots P ∪ positiveRealRoots Q).card ≤ 3 := by
    have hcard := Finset.card_union_add_card_inter
      (positiveRealRoots P) (positiveRealRoots Q)
    omega
  have hsub : nonnegativeRealRoots P ∪ nonnegativeRealRoots Q ⊆
      insert 0 (positiveRealRoots P ∪ positiveRealRoots Q) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxP | hxQ
    · rcases Finset.mem_insert.mp
          (nonnegativeRealRoots_subset_insert_zero_positiveRealRoots P hxP) with
        rfl | hxpos
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _ hxpos))
    · rcases Finset.mem_insert.mp
          (nonnegativeRealRoots_subset_insert_zero_positiveRealRoots Q hxQ) with
        rfl | hxpos
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_right _ hxpos))
  calc
    (nonnegativeRealRoots P ∪ nonnegativeRealRoots Q).card ≤
        (insert 0 (positiveRealRoots P ∪ positiveRealRoots Q)).card :=
      Finset.card_le_card hsub
    _ ≤ (positiveRealRoots P ∪ positiveRealRoots Q).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ 4 := by omega

lemma union_nonnegativeRealRoots_card_le_three_of_double_zero
    (P Q : Polynomial ℝ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hnonnegP : ∀ t : ℝ, 0 ≤ t → 0 ≤ P.eval t)
    (hnonnegQ : ∀ t : ℝ, 0 ≤ t → 0 ≤ Q.eval t)
    (hdegreeP : P.natDegree ≤ 5) (hdegreeQ : Q.natDegree ≤ 5)
    (hPzero : P.eval 0 = 0) (hQzero : Q.eval 0 = 0)
    (hPderiv : P.derivative.eval 0 = 0)
    (hQderiv : Q.derivative.eval 0 = 0) :
    (nonnegativeRealRoots P ∪ nonnegativeRealRoots Q).card ≤ 3 := by
  have hPbound :=
    twice_card_positiveRealRoots_add_two_le_natDegree_of_double_zero
      P hP hnonnegP hPzero hPderiv
  have hQbound :=
    twice_card_positiveRealRoots_add_two_le_natDegree_of_double_zero
      Q hQ hnonnegQ hQzero hQderiv
  have hsub : nonnegativeRealRoots P ∪ nonnegativeRealRoots Q ⊆
      insert 0 (positiveRealRoots P ∪ positiveRealRoots Q) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxP | hxQ
    · rcases Finset.mem_insert.mp
          (nonnegativeRealRoots_subset_insert_zero_positiveRealRoots P hxP) with
        rfl | hxpos
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _ hxpos))
    · rcases Finset.mem_insert.mp
          (nonnegativeRealRoots_subset_insert_zero_positiveRealRoots Q hxQ) with
        rfl | hxpos
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_right _ hxpos))
  calc
    (nonnegativeRealRoots P ∪ nonnegativeRealRoots Q).card ≤
        (insert 0 (positiveRealRoots P ∪ positiveRealRoots Q)).card :=
      Finset.card_le_card hsub
    _ ≤ (positiveRealRoots P ∪ positiveRealRoots Q).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ (positiveRealRoots P).card + (positiveRealRoots Q).card + 1 := by
      exact Nat.add_le_add_right (Finset.card_union_le _ _) 1
    _ ≤ 3 := by omega

def quinticResiduePolynomial {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z : ι → ℝ) : Polynomial ℝ :=
  ∑ i ∈ s, Polynomial.C (z i) * Lagrange.nodal (s.erase i) t

lemma eval_quinticResiduePolynomial
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {t z : ι → ℝ}
    (_ht : Set.InjOn t s) {i : ι} (hi : i ∈ s) :
    (quinticResiduePolynomial s t z).eval (t i) =
      z i * ∏ j ∈ s.erase i, (t i - t j) := by
  simp only [quinticResiduePolynomial, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C]
  rw [Finset.sum_eq_single i]
  · rw [Lagrange.eval_nodal]
  · intro j hj hji
    rw [Lagrange.eval_nodal_at_node
      (Finset.mem_erase.mpr ⟨hji.symm, hi⟩), mul_zero]
  · exact fun h => (h hi).elim

lemma quinticResiduePolynomial_ne_zero
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {t z : ι → ℝ}
    (ht : Set.InjOn t s) {i : ι} (hi : i ∈ s) (hz : z i ≠ 0) :
    quinticResiduePolynomial s t z ≠ 0 := by
  intro he
  have hv := eval_quinticResiduePolynomial (z := z) ht hi
  rw [he, Polynomial.eval_zero] at hv
  have hprod : (∏ j ∈ s.erase i, (t i - t j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun heq =>
      (Finset.mem_erase.mp hj).1
        ((ht hi (Finset.mem_erase.mp hj).2 heq).symm))
  exact mul_ne_zero hz hprod hv.symm

lemma degree_quinticResiduePolynomial_lt
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z : ι → ℝ) :
    (quinticResiduePolynomial s t z).degree <
      (s.card : WithBot ℕ) := by
  apply (Polynomial.degree_sum_le _ _).trans_lt
  have hbot : (⊥ : WithBot ℕ) < (s.card : WithBot ℕ) :=
    WithBot.bot_lt_coe s.card
  apply (Finset.sup_lt_iff hbot).mpr
  intro i hi
  calc
    (Polynomial.C (z i) * Lagrange.nodal (s.erase i) t).degree ≤
        (Lagrange.nodal (s.erase i) t).degree := by
      by_cases hz : z i = 0
      · simp [hz]
      · rw [Polynomial.degree_C_mul hz]
    _ = ((s.erase i).card : WithBot ℕ) := Lagrange.degree_nodal
    _ < (s.card : WithBot ℕ) := by
      exact_mod_cast Finset.card_erase_lt_of_mem hi

lemma X_mul_quinticResiduePolynomial
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z : ι → ℝ) :
    Polynomial.X * quinticResiduePolynomial s t z =
      Polynomial.C (∑ i ∈ s, z i) * Lagrange.nodal s t +
        quinticResiduePolynomial s t (fun i => t i * z i) := by
  simp only [quinticResiduePolynomial, map_sum, Finset.sum_mul, mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Lagrange.nodal_eq_mul_nodal_erase hi, map_mul]
  ring

lemma X_pow_mul_quinticResiduePolynomial_of_moments
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z : ι → ℝ) (k : ℕ)
    (hm : ∀ j < k, (∑ i ∈ s, (t i) ^ j * z i) = 0) :
    Polynomial.X ^ k * quinticResiduePolynomial s t z =
      quinticResiduePolynomial s t (fun i => (t i) ^ k * z i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc,
      ih (fun j hj => hm j (hj.trans (Nat.lt_succ_self k))),
      X_mul_quinticResiduePolynomial]
    have hs : (∑ i ∈ s, (t i) ^ k * z i) = 0 :=
      hm k (Nat.lt_succ_self k)
    rw [hs, map_zero, zero_mul, zero_add]
    congr 1
    funext i
    rw [pow_succ']
    ring

lemma degree_quinticResiduePolynomial_of_moments
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z : ι → ℝ) (k : ℕ)
    (hm : ∀ j < k, (∑ i ∈ s, (t i) ^ j * z i) = 0) :
    (quinticResiduePolynomial s t z).degree + k <
      (s.card : WithBot ℕ) := by
  have hd := degree_quinticResiduePolynomial_lt s t
    (fun i => (t i) ^ k * z i)
  rw [← X_pow_mul_quinticResiduePolynomial_of_moments s t z k hm,
    Polynomial.degree_mul, Polynomial.degree_X_pow, add_comm] at hd
  exact hd

lemma degree_mul_quinticResiduePolynomial_lt
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z : ι → ℝ) (P : Polynomial ℝ) {k : ℕ}
    (hP : P.degree ≤ k)
    (hm : ∀ j < k, (∑ i ∈ s, (t i) ^ j * z i) = 0) :
    (P * quinticResiduePolynomial s t z).degree <
      (s.card : WithBot ℕ) := by
  rw [Polynomial.degree_mul, add_comm]
  exact (_root_.add_le_add le_rfl hP).trans_lt
    (degree_quinticResiduePolynomial_of_moments s t z k hm)

lemma contact_quinticResiduePolynomial_identity
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z y : ι → ℝ) (ht : Set.InjOn t s)
    (E O : Polynomial ℝ) (hE : E.degree ≤ 2) (hO : O.degree ≤ 2)
    (hz : ∀ j < 2, (∑ i ∈ s, (t i) ^ j * z i) = 0)
    (hy : ∀ j < 2, (∑ i ∈ s, (t i) ^ j * y i) = 0)
    (hc : ∀ i ∈ s, E.eval (t i) * z i + O.eval (t i) * y i = 0) :
    E * quinticResiduePolynomial s t z +
      O * quinticResiduePolynomial s t y = 0 := by
  apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero s ht
  · exact (Polynomial.degree_add_le _ _).trans_lt (max_lt_iff.mpr
      ⟨degree_mul_quinticResiduePolynomial_lt s t z E hE hz,
        degree_mul_quinticResiduePolynomial_lt s t y O hO hy⟩)
  · intro i hi
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      eval_quinticResiduePolynomial ht hi]
    rw [← mul_assoc, ← mul_assoc, ← add_mul, hc i hi, zero_mul]

lemma coprime_quintic_contact_multiplier
    {E O U V : Polynomial ℝ}
    (hcop : IsCoprime E O) (hE : E ≠ 0)
    (h : E * U + O * V = 0) :
    ∃ Q : Polynomial ℝ, V = E * Q ∧ U = -(O * Q) := by
  have hd : E ∣ O * V := by
    rw [eq_neg_of_add_eq_zero_right h]
    exact dvd_neg.mpr (dvd_mul_right E U)
  obtain ⟨Q, hQ⟩ := hcop.dvd_of_dvd_mul_left hd
  refine ⟨Q, hQ, ?_⟩
  apply mul_left_cancel₀ hE
  rw [hQ] at h
  calc
    E * U = -(O * (E * Q)) := eq_neg_of_add_eq_zero_left h
    _ = E * -(O * Q) := by ring

lemma residues_zero_of_vanishing_moments
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {t z : ι → ℝ} (ht : Set.InjOn t s)
    {k : ℕ} (hk : s.card ≤ k)
    (hm : ∀ j < k, (∑ i ∈ s, (t i) ^ j * z i) = 0) :
    ∀ i ∈ s, z i = 0 := by
  intro i hi
  by_contra hz
  have hp : quinticResiduePolynomial s t z ≠ 0 :=
    quinticResiduePolynomial_ne_zero ht hi hz
  have hd := degree_quinticResiduePolynomial_of_moments s t z k hm
  rw [Polynomial.degree_eq_natDegree hp] at hd
  have hn : (quinticResiduePolynomial s t z).natDegree + k < s.card := by
    exact_mod_cast hd
  omega

def averageMonicQuintic {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (a : ι → MonicQuinticCoeff) : MonicQuinticCoeff where
  c1 := (∑ i ∈ s, w i)⁻¹ * ∑ i ∈ s, w i * (a i).c1
  c2 := (∑ i ∈ s, w i)⁻¹ * ∑ i ∈ s, w i * (a i).c2
  c3 := (∑ i ∈ s, w i)⁻¹ * ∑ i ∈ s, w i * (a i).c3
  c4 := (∑ i ∈ s, w i)⁻¹ * ∑ i ∈ s, w i * (a i).c4
  c5 := (∑ i ∈ s, w i)⁻¹ * ∑ i ∈ s, w i * (a i).c5

lemma averageMonicQuintic_evenPart
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (a : ι → MonicQuinticCoeff) (r : ℝ)
    (hW : (∑ i ∈ s, w i) ≠ 0) :
    (∑ i ∈ s, w i) * (averageMonicQuintic s w a).evenPart r =
      ∑ i ∈ s, w i * (a i).evenPart r := by
  simp only [averageMonicQuintic, evenPart, mul_add, mul_sub,
    sum_add_distrib, sum_sub_distrib, ← mul_assoc, ← sum_mul]
  field_simp [hW]

lemma averageMonicQuintic_oddPart
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (a : ι → MonicQuinticCoeff) (r : ℝ)
    (hW : (∑ i ∈ s, w i) ≠ 0) :
    (∑ i ∈ s, w i) * (averageMonicQuintic s w a).oddPart r =
      ∑ i ∈ s, w i * (a i).oddPart r := by
  simp only [averageMonicQuintic, oddPart, mul_add, mul_sub,
    sum_add_distrib, sum_sub_distrib, ← mul_assoc, ← sum_mul]
  field_simp [hW]

lemma averageMonicQuintic_frequencyFeature
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (a : ι → MonicQuinticCoeff) (r : ℝ)
    (hW : (∑ i ∈ s, w i) ≠ 0) :
    (∑ i ∈ s, w i) •
        (averageMonicQuintic s w a).quinticFrequencyFeature r =
      ∑ i ∈ s, w i • (a i).quinticFrequencyFeature r := by
  have hE := averageMonicQuintic_evenPart s w a r hW
  have hO := averageMonicQuintic_oddPart s w a r hW
  ext j
  fin_cases j <;>
    norm_num [quinticFrequencyFeature, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply, mul_left_comm (w _), ← Finset.mul_sum] <;>
    first | (rw [← hE]; ring) | (rw [← hO]; ring) | exact hE

lemma averageMonicQuintic_contact
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (a : ι → MonicQuinticCoeff) (b : QuinticNumeratorVector) (r : ℝ)
    (hW : (∑ i ∈ s, w i) ≠ 0)
    (hc : ∀ i ∈ s, (a i).vectorCross b r = 0) :
    (averageMonicQuintic s w a).vectorCross b r = 0 := by
  have hE := averageMonicQuintic_evenPart s w a r hW
  have hO := averageMonicQuintic_oddPart s w a r hW
  have hpair : (∑ i ∈ s, w i) *
        (averageMonicQuintic s w a).vectorCross b r =
      ∑ i ∈ s, w i * (a i).vectorCross b r := by
    calc
      _ = ((∑ i ∈ s, w i) *
            (averageMonicQuintic s w a).evenPart r) *
              vectorNumeratorEven b r +
          r * ((∑ i ∈ s, w i) *
            (averageMonicQuintic s w a).oddPart r) *
              vectorNumeratorOdd b r := by
            unfold vectorCross
            ring
      _ = (∑ i ∈ s, w i * (a i).evenPart r) *
              vectorNumeratorEven b r +
          r * (∑ i ∈ s, w i * (a i).oddPart r) *
              vectorNumeratorOdd b r := by rw [hE, hO]
      _ = _ := by
        simp only [vectorCross, mul_add, Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        · calc
            r * (∑ i ∈ s, w i * (a i).oddPart r) *
                vectorNumeratorOdd b r =
              (∑ i ∈ s, w i * (a i).oddPart r) *
                (r * vectorNumeratorOdd b r) := by ring
            _ = ∑ i ∈ s, (w i * (a i).oddPart r) *
                (r * vectorNumeratorOdd b r) := by rw [Finset.sum_mul]
            _ = _ := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
  have hz : (∑ i ∈ s, w i * (a i).vectorCross b r) = 0 :=
    Finset.sum_eq_zero (fun i hi => by rw [hc i hi, mul_zero])
  exact (mul_eq_zero.mp (hpair.trans hz)).resolve_left hW

def endpointIndicator (right : Bool) : ℝ :=
  if right then 1 else 0

lemma weighted_selectedEndpoint
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (right : ι → Bool)
    (x y : ℝ) :
    (∑ i ∈ s, w i * (if right i then y else x)) =
      (∑ i ∈ s, w i) * x +
        (∑ i ∈ s, w i * endpointIndicator (right i)) * (y - x) := by
  calc
    _ = ∑ i ∈ s, (w i * x +
        (w i * endpointIndicator (right i)) * (y - x)) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hright : right i
      · simp [hright, endpointIndicator]
        ring
      · simp [hright, endpointIndicator]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp_rw [← Finset.sum_mul]

def averageEndpointParameter {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (right : ι → Bool) : ℝ :=
  (∑ i ∈ s, w i * endpointIndicator (right i)) /
    (∑ i ∈ s, w i)

lemma averageEndpointParameter_mem
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (right : ι → Bool)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < ∑ i ∈ s, w i) :
    averageEndpointParameter s w right ∈ Set.Icc (0 : ℝ) 1 := by
  have hterm (i : ι) (hi : i ∈ s) :
      0 ≤ w i * endpointIndicator (right i) ∧
        w i * endpointIndicator (right i) ≤ w i := by
    by_cases hright : right i
    · simp [endpointIndicator, hright, hw i hi]
    · simp [endpointIndicator, hright, hw i hi]
  have hR0 : 0 ≤ ∑ i ∈ s, w i * endpointIndicator (right i) :=
    Finset.sum_nonneg (fun i hi => (hterm i hi).1)
  have hRW : (∑ i ∈ s, w i * endpointIndicator (right i)) ≤
      ∑ i ∈ s, w i :=
    Finset.sum_le_sum (fun i hi => (hterm i hi).2)
  constructor
  · exact div_nonneg hR0 hW.le
  · exact (div_le_one hW).2 hRW

lemma averageMonicQuintic_selectedEndpoint
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (right : ι → Bool)
    (p q : MonicQuinticCoeff) (hW : (∑ i ∈ s, w i) ≠ 0) :
    averageMonicQuintic s w (fun i => p.selectedEndpoint q (right i)) =
      p.convex q (averageEndpointParameter s w right) := by
  have hsel (x y : ℝ) := weighted_selectedEndpoint s w right x y
  cases p with
  | mk p1 p2 p3 p4 p5 =>
  cases q with
  | mk q1 q2 q3 q4 q5 =>
  simp only [averageMonicQuintic, selectedEndpoint, convex]
  congr 1
  all_goals
    simp only [apply_ite]
    simp_rw [← mul_ite]
    rw [hsel]
    unfold averageEndpointParameter
    field_simp [hW]
    ring

def EndpointMomentCertificate.finiteNodes
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    Finset ℝ :=
  C.finiteIndices.image C.finiteFrequency

def EndpointMomentCertificate.finiteFiber
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    (r : ℝ) : Finset (Fin C.atomCount) :=
  C.finiteIndices.filter (fun i => C.finiteFrequency i = r)

def EndpointMomentCertificate.mergedFiniteWeight
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    (r : ℝ) : ℝ :=
  ∑ i ∈ C.finiteFiber r, C.finiteWeight i

def EndpointMomentCertificate.mergedDenominator
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    (r : ℝ) : MonicQuinticCoeff :=
  averageMonicQuintic (C.finiteFiber r) C.finiteWeight
    (fun i => p.selectedEndpoint q (C.rightEndpoint i))

def EndpointMomentCertificate.mergedParameter
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    (r : ℝ) : ℝ :=
  averageEndpointParameter (C.finiteFiber r) C.finiteWeight C.rightEndpoint

def EndpointMomentCertificate.mergedInfinityWeight
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) : ℝ :=
  ∑ i ∈ C.infiniteIndices, C.weight i

lemma EndpointMomentCertificate.finiteNodes_nonempty
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    C.finiteNodes.Nonempty := by
  obtain ⟨i, hi⟩ := C.finiteIndices_nonempty
  exact ⟨C.finiteFrequency i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩

lemma EndpointMomentCertificate.finiteNode_nonneg
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    {r : ℝ} (hr : r ∈ C.finiteNodes) :
    0 ≤ r := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
  exact C.finiteFrequency_nonneg hi

lemma EndpointMomentCertificate.finiteFiber_nonempty
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    {r : ℝ} (hr : r ∈ C.finiteNodes) :
    (C.finiteFiber r).Nonempty := by
  obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp hr
  exact ⟨i, Finset.mem_filter.mpr ⟨hi, hir⟩⟩

lemma EndpointMomentCertificate.mergedFiniteWeight_pos
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    {r : ℝ} (hr : r ∈ C.finiteNodes) :
    0 < C.mergedFiniteWeight r := by
  apply Finset.sum_pos
  · intro i hi
    exact C.finiteWeight_pos (Finset.mem_filter.mp hi).1
  · exact C.finiteFiber_nonempty hr

lemma EndpointMomentCertificate.mergedParameter_mem
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    {r : ℝ} (hr : r ∈ C.finiteNodes) :
    C.mergedParameter r ∈ Set.Icc (0 : ℝ) 1 := by
  apply averageEndpointParameter_mem
  · intro i hi
    exact (C.finiteWeight_pos (Finset.mem_filter.mp hi).1).le
  · exact C.mergedFiniteWeight_pos hr

lemma EndpointMomentCertificate.mergedDenominator_eq_convex
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    {r : ℝ} (hr : r ∈ C.finiteNodes) :
    C.mergedDenominator r = p.convex q (C.mergedParameter r) := by
  exact averageMonicQuintic_selectedEndpoint
    (C.finiteFiber r) C.finiteWeight C.rightEndpoint p q
    (ne_of_gt (C.mergedFiniteWeight_pos hr))

lemma EndpointMomentCertificate.mergedDenominator_hurwitz
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    (hsegment : p.allConvexHurwitz q)
    {r : ℝ} (hr : r ∈ C.finiteNodes) :
    (C.mergedDenominator r).Hurwitz := by
  rw [C.mergedDenominator_eq_convex hr]
  exact hsegment _ (C.mergedParameter_mem hr).1
    (C.mergedParameter_mem hr).2

lemma CriticalEndpointMomentCertificate.merged_contact
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    {r : ℝ} (hr : r ∈ C.certificate.finiteNodes) :
    (C.certificate.mergedDenominator r).vectorCross C.support r = 0 := by
  apply averageMonicQuintic_contact
    (C.certificate.finiteFiber r) C.certificate.finiteWeight
    (fun i => p.selectedEndpoint q (C.certificate.rightEndpoint i))
    C.support r (ne_of_gt (C.certificate.mergedFiniteWeight_pos hr))
  intro i hi
  obtain ⟨hfinite, hfrequency⟩ := Finset.mem_filter.mp hi
  rw [← hfrequency]
  exact C.finite_contact_cross hfinite

lemma EndpointMomentCertificate.merged_feature
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    {r : ℝ} (hr : r ∈ C.finiteNodes) :
    C.mergedFiniteWeight r •
        (C.mergedDenominator r).quinticFrequencyFeature r =
      ∑ i ∈ C.finiteFiber r, C.finiteWeight i •
        (p.selectedEndpoint q (C.rightEndpoint i)).quinticFrequencyFeature
          (C.finiteFrequency i) := by
  rw [mergedFiniteWeight, mergedDenominator,
    averageMonicQuintic_frequencyFeature _ _ _ _
      (ne_of_gt (C.mergedFiniteWeight_pos hr))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

lemma EndpointMomentCertificate.merged_balance
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    (∑ r ∈ C.finiteNodes, C.mergedFiniteWeight r •
      (C.mergedDenominator r).quinticFrequencyFeature r) +
      C.mergedInfinityWeight •
        (Pi.single (0 : Fin 6) (1 : ℝ) : QuinticNumeratorVector) = 0 := by
  have hfinite :
      (∑ r ∈ C.finiteNodes, C.mergedFiniteWeight r •
        (C.mergedDenominator r).quinticFrequencyFeature r) =
      ∑ i ∈ C.finiteIndices, C.finiteWeight i •
        (p.selectedEndpoint q (C.rightEndpoint i)).quinticFrequencyFeature
          (C.finiteFrequency i) := by
    calc
      _ = ∑ r ∈ C.finiteNodes,
          ∑ i ∈ C.finiteFiber r, C.finiteWeight i •
            (p.selectedEndpoint q (C.rightEndpoint i)).quinticFrequencyFeature
              (C.finiteFrequency i) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact C.merged_feature hr
      _ = _ := by
        exact Finset.sum_fiberwise_of_maps_to
          (fun i hi => Finset.mem_image_of_mem C.finiteFrequency hi) _
  rw [hfinite]
  exact C.decompactified_balance

lemma EndpointMomentCertificate.mergedInfinityWeight_nonneg
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    0 ≤ C.mergedInfinityWeight := by
  exact Finset.sum_nonneg (fun i hi => (C.weight_pos i).le)

lemma CriticalEndpointMomentCertificate.infinity_contact
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q) :
    C.certificate.mergedInfinityWeight * C.support 0 = 0 := by
  unfold EndpointMomentCertificate.mergedInfinityWeight
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i hi
  have hxi : C.certificate.compactFrequency i = 1 :=
    le_antisymm (C.certificate.frequency_mem i).2
      (le_of_not_gt ((EndpointMomentCertificate.mem_infiniteIndices
        C.certificate i).mp hi))
  have hc := C.contact i
  rw [hxi, compactQuinticFeature_one] at hc
  have hb0 : C.support 0 = 0 := by
    simpa [quinticDot, Fin.sum_univ_succ] using hc
  rw [hb0, mul_zero]

lemma EndpointMomentCertificate.merged_finite_balance_coordinate
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    (j : Fin 6) (hj : j ≠ 0) :
    (∑ r ∈ C.finiteNodes, C.mergedFiniteWeight r *
      (C.mergedDenominator r).quinticFrequencyFeature r j) = 0 := by
  have h := congrFun C.merged_balance j
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.zero_apply] at h
  simpa [Pi.single_apply, hj] using h

lemma EndpointMomentCertificate.merged_leading_moment
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    (∑ r ∈ C.finiteNodes, C.mergedFiniteWeight r * r ^ 3 *
      (C.mergedDenominator r).oddPart r) +
      C.mergedInfinityWeight = 0 := by
  have h := congrFun C.merged_balance 0
  simpa [quinticFrequencyFeature, Pi.single_apply, mul_assoc] using h

lemma EndpointMomentCertificate.merged_even_moment_zero
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    (∑ r ∈ C.finiteNodes, C.mergedFiniteWeight r *
      (C.mergedDenominator r).evenPart r) = 0 := by
  simpa [quinticFrequencyFeature] using
    C.merged_finite_balance_coordinate (5 : Fin 6) (by decide)

lemma EndpointMomentCertificate.merged_even_moment_one
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    (∑ r ∈ C.finiteNodes, C.mergedFiniteWeight r * r *
      (C.mergedDenominator r).evenPart r) = 0 := by
  have h := C.merged_finite_balance_coordinate (3 : Fin 6) (by decide)
  simp only [quinticFrequencyFeature] at h
  rw [← neg_eq_zero]
  simpa only [Finset.sum_neg_distrib, neg_mul, mul_neg, neg_neg,
    mul_assoc] using h

lemma EndpointMomentCertificate.merged_even_moment_two
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    (∑ r ∈ C.finiteNodes, C.mergedFiniteWeight r * r ^ 2 *
      (C.mergedDenominator r).evenPart r) = 0 := by
  simpa [quinticFrequencyFeature, mul_assoc] using
    C.merged_finite_balance_coordinate (1 : Fin 6) (by decide)

lemma EndpointMomentCertificate.merged_odd_moment_one
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    (∑ r ∈ C.finiteNodes, C.mergedFiniteWeight r * r *
      (C.mergedDenominator r).oddPart r) = 0 := by
  simpa [quinticFrequencyFeature, mul_assoc] using
    C.merged_finite_balance_coordinate (4 : Fin 6) (by decide)

lemma EndpointMomentCertificate.merged_odd_moment_two
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    (∑ r ∈ C.finiteNodes, C.mergedFiniteWeight r * r ^ 2 *
      (C.mergedDenominator r).oddPart r) = 0 := by
  have h := C.merged_finite_balance_coordinate (2 : Fin 6) (by decide)
  simp only [quinticFrequencyFeature] at h
  rw [← neg_eq_zero]
  simpa only [Finset.sum_neg_distrib, neg_mul, mul_neg, neg_neg,
    mul_assoc] using h

def EndpointMomentCertificate.mergedEvenResidue
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    (r : ℝ) : ℝ :=
  C.mergedFiniteWeight r * (C.mergedDenominator r).evenPart r

def EndpointMomentCertificate.mergedOddResidue
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    (r : ℝ) : ℝ :=
  C.mergedFiniteWeight r * r * (C.mergedDenominator r).oddPart r

lemma EndpointMomentCertificate.mergedEvenResidue_moments
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    ∀ j < 3, (∑ r ∈ C.finiteNodes,
      r ^ j * C.mergedEvenResidue r) = 0 := by
  intro j hj
  interval_cases j
  · simpa [mergedEvenResidue] using C.merged_even_moment_zero
  · calc
      _ = ∑ r ∈ C.finiteNodes, C.mergedFiniteWeight r * r *
          (C.mergedDenominator r).evenPart r := by
        apply Finset.sum_congr rfl
        intro r hr
        simp [mergedEvenResidue]
        ring
      _ = 0 := C.merged_even_moment_one
  · calc
      _ = ∑ r ∈ C.finiteNodes, C.mergedFiniteWeight r * r ^ 2 *
          (C.mergedDenominator r).evenPart r := by
        apply Finset.sum_congr rfl
        intro r hr
        simp [mergedEvenResidue]
        ring
      _ = 0 := C.merged_even_moment_two

lemma EndpointMomentCertificate.mergedOddResidue_moments
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    ∀ j < 2, (∑ r ∈ C.finiteNodes,
      r ^ j * C.mergedOddResidue r) = 0 := by
  intro j hj
  interval_cases j
  · simpa [mergedOddResidue, mul_assoc] using C.merged_odd_moment_one
  · calc
      _ = ∑ r ∈ C.finiteNodes, C.mergedFiniteWeight r * r ^ 2 *
          (C.mergedDenominator r).oddPart r := by
        apply Finset.sum_congr rfl
        intro r hr
        simp [mergedOddResidue]
        ring
      _ = 0 := C.merged_odd_moment_two

lemma EndpointMomentCertificate.mergedOddResidue_third_moment
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    (∑ r ∈ C.finiteNodes, r ^ 2 * C.mergedOddResidue r) =
      -C.mergedInfinityWeight := by
  have hlead := C.merged_leading_moment
  have heq : (∑ r ∈ C.finiteNodes,
      C.mergedFiniteWeight r * r ^ 3 *
        (C.mergedDenominator r).oddPart r) =
      -C.mergedInfinityWeight := by
    linarith
  calc
    _ = ∑ r ∈ C.finiteNodes,
        C.mergedFiniteWeight r * r ^ 3 *
          (C.mergedDenominator r).oddPart r := by
      apply Finset.sum_congr rfl
      intro r hr
      simp [mergedOddResidue]
      ring
    _ = -C.mergedInfinityWeight := heq

lemma EndpointMomentCertificate.mergedOddResidue_three_moments
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    (hinfinity : C.mergedInfinityWeight = 0) :
    ∀ j < 3, (∑ r ∈ C.finiteNodes,
      r ^ j * C.mergedOddResidue r) = 0 := by
  intro j hj
  by_cases hj2 : j < 2
  · exact C.mergedOddResidue_moments j hj2
  · have heq : j = 2 := by omega
    subst j
    simpa [hinfinity] using C.mergedOddResidue_third_moment

def EndpointMomentCertificate.evenInterpolationPolynomial
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    Polynomial ℝ :=
  quinticResiduePolynomial C.finiteNodes id C.mergedEvenResidue

def EndpointMomentCertificate.oddInterpolationPolynomial
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    Polynomial ℝ :=
  quinticResiduePolynomial C.finiteNodes id C.mergedOddResidue

def vectorNumeratorEvenPolynomial (b : QuinticNumeratorVector) :
    Polynomial ℝ :=
  Polynomial.C (b 1) * Polynomial.X ^ 2 -
    Polynomial.C (b 3) * Polynomial.X + Polynomial.C (b 5)

def vectorNumeratorOddPolynomial (b : QuinticNumeratorVector) :
    Polynomial ℝ :=
  Polynomial.C (b 0) * Polynomial.X ^ 2 -
    Polynomial.C (b 2) * Polynomial.X + Polynomial.C (b 4)

lemma vectorNumeratorEvenPolynomial_eq_zero_iff
    (b : QuinticNumeratorVector) :
    vectorNumeratorEvenPolynomial b = 0 ↔
      b 1 = 0 ∧ b 3 = 0 ∧ b 5 = 0 := by
  constructor
  · intro h
    have h2 := congrArg (fun P : Polynomial ℝ => P.coeff 2) h
    have h1 := congrArg (fun P : Polynomial ℝ => P.coeff 1) h
    have h0 := congrArg (fun P : Polynomial ℝ => P.coeff 0) h
    simp [vectorNumeratorEvenPolynomial] at h2 h1 h0
    exact ⟨h2, by linarith, h0⟩
  · rintro ⟨h1, h3, h5⟩
    simp [vectorNumeratorEvenPolynomial, h1, h3, h5]

lemma vectorNumeratorOddPolynomial_eq_zero_iff
    (b : QuinticNumeratorVector) :
    vectorNumeratorOddPolynomial b = 0 ↔
      b 0 = 0 ∧ b 2 = 0 ∧ b 4 = 0 := by
  constructor
  · intro h
    have h2 := congrArg (fun P : Polynomial ℝ => P.coeff 2) h
    have h1 := congrArg (fun P : Polynomial ℝ => P.coeff 1) h
    have h0 := congrArg (fun P : Polynomial ℝ => P.coeff 0) h
    simp [vectorNumeratorOddPolynomial] at h2 h1 h0
    exact ⟨h2, by linarith, h0⟩
  · rintro ⟨h0, h2, h4⟩
    simp [vectorNumeratorOddPolynomial, h0, h2, h4]

/-! ## 4. 临界支撑、接触点次数预算与三个代数分支 -/

lemma CriticalEndpointMomentCertificate.pureOdd_support_at_hurwitz
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (hp : p.Hurwitz)
    (hEven : vectorNumeratorEvenPolynomial C.support = 0) :
    0 < C.support 0 ∧
      ∀ t : ℝ, vectorNumeratorOdd C.support t =
        C.support 0 * p.oddPart t := by
  obtain ⟨D⟩ := denominator_interlacing_of_hurwitz hp
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5⟩ :=
    C.support_coefficients_nonneg hp
  obtain ⟨hb1zero, hb3zero, hb5zero⟩ :=
    (vectorNumeratorEvenPolynomial_eq_zero_iff C.support).mp hEven
  have hcross (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ t * p.oddPart t * vectorNumeratorOdd C.support t := by
    have h := C.support_cross_nonneg false t ht
    simp only [selectedEndpoint, Bool.false_eq_true, if_false] at h
    unfold vectorCross at h
    have hNeven : vectorNumeratorEven C.support t = 0 := by
      simp [vectorNumeratorEven, hb1zero, hb3zero, hb5zero]
    rw [hNeven, mul_zero] at h
    simpa only [zero_add] using h
  have hcont : Continuous (vectorNumeratorOdd C.support) := by
    unfold vectorNumeratorOdd
    fun_prop
  have hleft : ∀ t ∈ Set.Ioo (0 : ℝ) D.o₁,
      0 ≤ vectorNumeratorOdd C.support t := by
    intro t ht
    have hO : 0 < p.oddPart t := by
      rw [D.odd_eval]
      exact mul_pos_of_neg_of_neg
        (sub_neg.mpr ht.2)
        (sub_neg.mpr (ht.2.trans
          (D.ordered.2.2.1.trans D.ordered.2.2.2)))
    exact (mul_nonneg_iff_of_pos_left (mul_pos ht.1 hO)).mp
      (hcross t ht.1.le)
  have hmiddle : ∀ t ∈ Set.Ioo D.o₁ D.o₂,
      vectorNumeratorOdd C.support t ≤ 0 := by
    intro t ht
    have ht0 : 0 < t :=
      (D.ordered.1.trans D.ordered.2.1).trans ht.1
    have hO : p.oddPart t < 0 := by
      rw [D.odd_eval]
      exact mul_neg_of_pos_of_neg
        (sub_pos.mpr ht.1) (sub_neg.mpr ht.2)
    apply le_of_not_gt
    intro hN
    have hneg := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ht0 hO) hN
    exact (not_lt_of_ge (hcross t ht0.le)) hneg
  have hright : ∀ t ∈ Set.Ioo D.o₂ (D.o₂ + 1),
      0 ≤ vectorNumeratorOdd C.support t := by
    intro t ht
    have ht0 : 0 < t :=
      (D.ordered.1.trans (D.ordered.2.1.trans
        (D.ordered.2.2.1.trans D.ordered.2.2.2))).trans ht.1
    have hO : 0 < p.oddPart t := by
      rw [D.odd_eval]
      exact mul_pos
        (sub_pos.mpr ((D.ordered.2.2.1.trans D.ordered.2.2.2).trans ht.1))
        (sub_pos.mpr ht.1)
    exact (mul_nonneg_iff_of_pos_left (mul_pos ht0 hO)).mp
      (hcross t ht0.le)
  have hNo₁ : vectorNumeratorOdd C.support D.o₁ = 0 :=
    eq_zero_of_nonneg_left_nonpos_right hcont
      (D.ordered.1.trans D.ordered.2.1)
      (D.ordered.2.2.1.trans D.ordered.2.2.2) hleft hmiddle
  have hNo₂ : vectorNumeratorOdd C.support D.o₂ = 0 :=
    eq_zero_of_nonpos_left_nonneg_right hcont
      (D.ordered.2.2.1.trans D.ordered.2.2.2)
      (by linarith) hmiddle hright
  have hb0ne : C.support 0 ≠ 0 := by
    intro hb0zero
    have hb2zero : C.support 2 = 0 := by
      by_contra h
      have hb2pos : 0 < C.support 2 := lt_of_le_of_ne hb2 (Ne.symm h)
      have hprod := mul_pos hb2pos
        (sub_pos.mpr (D.ordered.2.2.1.trans D.ordered.2.2.2))
      unfold vectorNumeratorOdd at hNo₁ hNo₂
      rw [hb0zero] at hNo₁ hNo₂
      nlinarith
    have hb4zero : C.support 4 = 0 := by
      unfold vectorNumeratorOdd at hNo₁
      rw [hb0zero, hb2zero] at hNo₁
      simpa using hNo₁
    apply C.support_ne
    funext i
    fin_cases i <;> simp_all
  have hb0pos : 0 < C.support 0 := lt_of_le_of_ne hb0 (Ne.symm hb0ne)
  have hsum : C.support 2 = C.support 0 * (D.o₁ + D.o₂) := by
    have hfac : (D.o₂ - D.o₁) *
        (C.support 0 * (D.o₁ + D.o₂) - C.support 2) = 0 := by
      calc
        _ = vectorNumeratorOdd C.support D.o₂ -
              vectorNumeratorOdd C.support D.o₁ := by
            unfold vectorNumeratorOdd
            ring
        _ = 0 := by rw [hNo₁, hNo₂]; ring
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left
      (sub_ne_zero.mpr
        (D.ordered.2.2.1.trans D.ordered.2.2.2).ne'))).symm
  have hprod : C.support 4 = C.support 0 * D.o₁ * D.o₂ := by
    unfold vectorNumeratorOdd at hNo₁
    rw [hsum] at hNo₁
    nlinarith
  refine ⟨hb0pos, ?_⟩
  intro t
  rw [D.odd_eval]
  unfold vectorNumeratorOdd
  rw [hsum, hprod]
  ring

lemma pureOdd_denominator_roots_locked
    {a p : MonicQuinticCoeff} (ha : a.Hurwitz)
    (Da : QuinticDenominatorInterlacing a)
    (Dp : QuinticDenominatorInterlacing p)
    {b : QuinticNumeratorVector} (hb0 : 0 < b 0)
    (hEven : ∀ t : ℝ, vectorNumeratorEven b t = 0)
    (hOdd : ∀ t : ℝ, vectorNumeratorOdd b t = b 0 * p.oddPart t)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ a.vectorCross b t) :
    Da.o₁ = Dp.o₁ ∧ Da.o₂ = Dp.o₂ := by
  have hproduct : ∀ t : ℝ, 0 ≤ t →
      0 ≤ a.oddPart t * p.oddPart t := by
    intro t ht
    by_cases htzero : t = 0
    · subst t
      have hp4 : 0 < p.c4 := by
        calc
          0 < (0 - Dp.o₁) * (0 - Dp.o₂) :=
            mul_pos_of_neg_of_neg
              (sub_neg.mpr (Dp.ordered.1.trans Dp.ordered.2.1))
              (sub_neg.mpr (Dp.ordered.1.trans
                (Dp.ordered.2.1.trans
                  (Dp.ordered.2.2.1.trans Dp.ordered.2.2.2))))
          _ = p.oddPart 0 := (Dp.odd_eval 0).symm
          _ = p.c4 := by simp [oddPart]
      simpa [oddPart] using mul_nonneg ha.c4_pos.le hp4.le
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
      have hcross := hnonneg t ht
      unfold vectorCross at hcross
      rw [hEven t, hOdd t, mul_zero, zero_add] at hcross
      have hfactor : 0 < t * b 0 := mul_pos htpos hb0
      have heq : t * a.oddPart t * (b 0 * p.oddPart t) =
          (t * b 0) * (a.oddPart t * p.oddPart t) := by ring
      rw [heq] at hcross
      exact (mul_nonneg_iff_of_pos_left hfactor).mp hcross
  apply ordered_quadratic_roots_eq_of_product_nonneg
    (Da.ordered.1.trans Da.ordered.2.1)
    (Da.ordered.2.2.1.trans Da.ordered.2.2.2)
    (Dp.ordered.1.trans Dp.ordered.2.1)
    (Dp.ordered.2.2.1.trans Dp.ordered.2.2.2)
  intro t ht
  rw [← Da.odd_eval, ← Dp.odd_eval]
  exact hproduct t ht

lemma evenPart_ne_zero_of_oddPart_zero
    {a : MonicQuinticCoeff} (ha : a.Hurwitz)
    {t : ℝ} (ht : 0 ≤ t) (ho : a.oddPart t = 0) :
    a.evenPart t ≠ 0 := by
  intro he
  exact evalJW_ne_zero ha (Real.sqrt t)
    (evalJW_sqrt_eq_zero_of_parts ht he ho)

lemma oddPart_ne_zero_of_evenPart_zero
    {a : MonicQuinticCoeff} (ha : a.Hurwitz)
    {t : ℝ} (ht : 0 ≤ t) (he : a.evenPart t = 0) :
    a.oddPart t ≠ 0 := by
  intro ho
  exact evalJW_ne_zero ha (Real.sqrt t)
    (evalJW_sqrt_eq_zero_of_parts ht he ho)

lemma CriticalEndpointMomentCertificate.even_support_component_ne_zero
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (hsegment : p.allConvexHurwitz q) :
    vectorNumeratorEvenPolynomial C.support ≠ 0 := by
  intro hEven
  have hp := allConvexHurwitz_left hsegment
  obtain ⟨hb0, hOdd⟩ := C.pureOdd_support_at_hurwitz hp hEven
  obtain ⟨Dp⟩ := denominator_interlacing_of_hurwitz hp
  obtain ⟨hb1zero, hb3zero, hb5zero⟩ :=
    (vectorNumeratorEvenPolynomial_eq_zero_iff C.support).mp hEven
  have hEvenfun : ∀ t : ℝ, vectorNumeratorEven C.support t = 0 := by
    intro t
    simp [vectorNumeratorEven, hb1zero, hb3zero, hb5zero]
  have hnode : ∀ r ∈ C.certificate.finiteNodes,
      r = 0 ∨ r = Dp.o₁ ∨ r = Dp.o₂ := by
    intro r hr
    have ha := C.certificate.mergedDenominator_hurwitz hsegment hr
    obtain ⟨Da⟩ := denominator_interlacing_of_hurwitz ha
    have hnonneg : ∀ t : ℝ, 0 ≤ t →
        0 ≤ (C.certificate.mergedDenominator r).vectorCross C.support t := by
      intro t ht
      rw [C.certificate.mergedDenominator_eq_convex hr]
      exact C.support_cross_nonneg_convex _
        (C.certificate.mergedParameter_mem hr) t ht
    obtain ⟨ho₁, ho₂⟩ := pureOdd_denominator_roots_locked
      ha Da Dp hb0 hEvenfun hOdd hnonneg
    have hc := C.merged_contact hr
    unfold vectorCross at hc
    rw [hEvenfun r, hOdd r, mul_zero, zero_add,
      Da.odd_eval, Dp.odd_eval, ho₁, ho₂] at hc
    let A := (r - Dp.o₁) * (r - Dp.o₂)
    have heq : r * A * (C.support 0 * A) = 0 := by
      simpa [A] using hc
    rcases mul_eq_zero.mp heq with hleft | hright
    · rcases mul_eq_zero.mp hleft with hrzero | hAzero
      · exact Or.inl hrzero
      · rcases mul_eq_zero.mp hAzero with h₁ | h₂
        · exact Or.inr (Or.inl (sub_eq_zero.mp h₁))
        · exact Or.inr (Or.inr (sub_eq_zero.mp h₂))
    · have hAzero := (mul_eq_zero.mp hright).resolve_left (ne_of_gt hb0)
      rcases mul_eq_zero.mp hAzero with h₁ | h₂
      · exact Or.inr (Or.inl (sub_eq_zero.mp h₁))
      · exact Or.inr (Or.inr (sub_eq_zero.mp h₂))
  have hcard : C.certificate.finiteNodes.card ≤ 3 := by
    have hsub : C.certificate.finiteNodes ⊆
        ({0, Dp.o₁, Dp.o₂} : Finset ℝ) := by
      intro r hr
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hnode r hr
    calc
      C.certificate.finiteNodes.card ≤ ({0, Dp.o₁, Dp.o₂} : Finset ℝ).card :=
        Finset.card_le_card hsub
      _ ≤ ({Dp.o₁, Dp.o₂} : Finset ℝ).card + 1 :=
        Finset.card_insert_le 0 ({Dp.o₁, Dp.o₂} : Finset ℝ)
      _ ≤ (({Dp.o₂} : Finset ℝ).card + 1) + 1 := by
        exact Nat.add_le_add_right
          (Finset.card_insert_le Dp.o₁ ({Dp.o₂} : Finset ℝ)) 1
      _ ≤ 3 := by simp
  obtain ⟨r, hr⟩ := C.certificate.finiteNodes_nonempty
  have ha := C.certificate.mergedDenominator_hurwitz hsegment hr
  obtain ⟨Da⟩ := denominator_interlacing_of_hurwitz ha
  have hnonneg : ∀ t : ℝ, 0 ≤ t →
      0 ≤ (C.certificate.mergedDenominator r).vectorCross C.support t := by
    intro t ht
    rw [C.certificate.mergedDenominator_eq_convex hr]
    exact C.support_cross_nonneg_convex _
      (C.certificate.mergedParameter_mem hr) t ht
  obtain ⟨ho₁, ho₂⟩ := pureOdd_denominator_roots_locked
    ha Da Dp hb0 hEvenfun hOdd hnonneg
  have hEne : (C.certificate.mergedDenominator r).evenPart r ≠ 0 := by
    rcases hnode r hr with rfl | hr₁ | hr₂
    · simpa [evenPart] using ne_of_gt ha.c5_pos
    · apply evenPart_ne_zero_of_oddPart_zero ha
        (C.certificate.finiteNode_nonneg hr)
      rw [Da.odd_eval, ho₁, ho₂]
      rw [hr₁]
      ring
    · apply evenPart_ne_zero_of_oddPart_zero ha
        (C.certificate.finiteNode_nonneg hr)
      rw [Da.odd_eval, ho₁, ho₂]
      rw [hr₂]
      ring
  have hz : C.certificate.mergedEvenResidue r ≠ 0 := by
    apply mul_ne_zero
    · exact ne_of_gt (C.certificate.mergedFiniteWeight_pos hr)
    · exact hEne
  have hall := residues_zero_of_vanishing_moments
    Function.injective_id.injOn hcard
      C.certificate.mergedEvenResidue_moments r hr
  exact hz hall

lemma CriticalEndpointMomentCertificate.support_one_pos
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (hsegment : p.allConvexHurwitz q) :
    0 < C.support 1 := by
  have hp := allConvexHurwitz_left hsegment
  obtain ⟨D⟩ := denominator_interlacing_of_hurwitz hp
  rcases C.support_coefficients_nonneg hp with
    ⟨hb0, hb1, hb2, hb3, hb4, hb5⟩
  have ho₁pos : 0 < D.o₁ := D.ordered.1.trans D.ordered.2.1
  have he₂pos : 0 < D.e₂ :=
    D.ordered.1.trans (D.ordered.2.1.trans D.ordered.2.2.1)
  have ho₂pos : 0 < D.o₂ := he₂pos.trans D.ordered.2.2.2
  have hEven₁raw := C.support_cross_nonneg false D.o₁ ho₁pos.le
  have hEven₂raw := C.support_cross_nonneg false D.o₂ ho₂pos.le
  simp only [selectedEndpoint, Bool.false_eq_true, if_false] at hEven₁raw hEven₂raw
  unfold vectorCross at hEven₁raw hEven₂raw
  rw [D.roots.2.1] at hEven₁raw
  rw [D.roots.2.2.2] at hEven₂raw
  simp only [zero_mul, zero_add, mul_zero, add_zero] at hEven₁raw hEven₂raw
  have hEven₁ : vectorNumeratorEven C.support D.o₁ ≤ 0 := by
    apply le_of_not_gt
    intro hpos
    have hneg := mul_neg_of_neg_of_pos (D.even_o₁_neg hp) hpos
    linarith
  have hEven₂ : 0 ≤ vectorNumeratorEven C.support D.o₂ := by
    exact (mul_nonneg_iff_of_pos_left (D.even_o₂_pos hp)).mp hEven₂raw
  by_contra hnot
  have hb1zero : C.support 1 = 0 :=
    le_antisymm (le_of_not_gt hnot) hb1
  change C.support 1 * D.o₁ ^ 2 - C.support 3 * D.o₁ +
    C.support 5 ≤ 0 at hEven₁
  change 0 ≤ C.support 1 * D.o₂ ^ 2 - C.support 3 * D.o₂ +
    C.support 5 at hEven₂
  have hb3zero : C.support 3 = 0 := by
    rw [hb1zero, zero_mul, zero_sub] at hEven₁ hEven₂
    by_contra hb3ne
    have hb3pos : 0 < C.support 3 := lt_of_le_of_ne hb3 (Ne.symm hb3ne)
    have ho₁o₂ : D.o₁ < D.o₂ :=
      D.ordered.2.2.1.trans D.ordered.2.2.2
    have hprod : 0 < C.support 3 * (D.o₂ - D.o₁) :=
      mul_pos hb3pos (sub_pos.mpr ho₁o₂)
    nlinarith
  have hb5zero : C.support 5 = 0 := by
    have hb5le : C.support 5 ≤ 0 := by
      simpa [hb1zero, hb3zero] using hEven₁
    exact le_antisymm hb5le hb5
  exact C.even_support_component_ne_zero hsegment
    ((vectorNumeratorEvenPolynomial_eq_zero_iff C.support).mpr
      ⟨hb1zero, hb3zero, hb5zero⟩)

lemma CriticalEndpointMomentCertificate.pureEven_support_at_hurwitz
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (hsegment : p.allConvexHurwitz q)
    (hOdd : vectorNumeratorOddPolynomial C.support = 0) :
    ∃ D : QuinticDenominatorInterlacing p,
      0 < C.support 1 ∧
        ∀ t : ℝ, vectorNumeratorEven C.support t =
          C.support 1 * ((t - D.e₁) * (t - D.e₂)) := by
  have hp := allConvexHurwitz_left hsegment
  obtain ⟨D⟩ := denominator_interlacing_of_hurwitz hp
  obtain ⟨hb0zero, hb2zero, hb4zero⟩ :=
    (vectorNumeratorOddPolynomial_eq_zero_iff C.support).mp hOdd
  have hb1pos := C.support_one_pos hsegment
  have hcross (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ p.evenPart t * vectorNumeratorEven C.support t := by
    have h := C.support_cross_nonneg false t ht
    simp only [selectedEndpoint, Bool.false_eq_true, if_false] at h
    unfold vectorCross at h
    have hNodd : vectorNumeratorOdd C.support t = 0 := by
      simp [vectorNumeratorOdd, hb0zero, hb2zero, hb4zero]
    rw [hNodd, mul_zero, add_zero] at h
    exact h
  have hcont : Continuous (vectorNumeratorEven C.support) := by
    unfold vectorNumeratorEven
    fun_prop
  have hleft : ∀ t ∈ Set.Ioo (0 : ℝ) D.e₁,
      0 ≤ vectorNumeratorEven C.support t := by
    intro t ht
    have hE : 0 < p.evenPart t := by
      rw [D.even_eval]
      exact mul_pos hp.c1_pos (mul_pos_of_neg_of_neg
        (sub_neg.mpr ht.2)
        (sub_neg.mpr (ht.2.trans
          (D.ordered.2.1.trans D.ordered.2.2.1))))
    exact (mul_nonneg_iff_of_pos_left hE).mp (hcross t ht.1.le)
  have hmiddle : ∀ t ∈ Set.Ioo D.e₁ D.e₂,
      vectorNumeratorEven C.support t ≤ 0 := by
    intro t ht
    have ht0 : 0 < t := D.ordered.1.trans ht.1
    have hE : p.evenPart t < 0 := by
      rw [D.even_eval]
      exact mul_neg_of_pos_of_neg hp.c1_pos
        (mul_neg_of_pos_of_neg (sub_pos.mpr ht.1) (sub_neg.mpr ht.2))
    apply le_of_not_gt
    intro hN
    exact (not_lt_of_ge (hcross t ht0.le))
      (mul_neg_of_neg_of_pos hE hN)
  have hright : ∀ t ∈ Set.Ioo D.e₂ (D.e₂ + 1),
      0 ≤ vectorNumeratorEven C.support t := by
    intro t ht
    have ht0 : 0 < t :=
      (D.ordered.1.trans (D.ordered.2.1.trans D.ordered.2.2.1)).trans ht.1
    have hE : 0 < p.evenPart t := by
      rw [D.even_eval]
      exact mul_pos hp.c1_pos (mul_pos
        (sub_pos.mpr ((D.ordered.2.1.trans D.ordered.2.2.1).trans ht.1))
        (sub_pos.mpr ht.1))
    exact (mul_nonneg_iff_of_pos_left hE).mp (hcross t ht0.le)
  have hNe₁ : vectorNumeratorEven C.support D.e₁ = 0 :=
    eq_zero_of_nonneg_left_nonpos_right hcont D.ordered.1
      (D.ordered.2.1.trans D.ordered.2.2.1) hleft hmiddle
  have hNe₂ : vectorNumeratorEven C.support D.e₂ = 0 :=
    eq_zero_of_nonpos_left_nonneg_right hcont
      (D.ordered.2.1.trans D.ordered.2.2.1) (by linarith) hmiddle hright
  have hsum : C.support 3 = C.support 1 * (D.e₁ + D.e₂) := by
    have hfac : (D.e₂ - D.e₁) *
        (C.support 1 * (D.e₁ + D.e₂) - C.support 3) = 0 := by
      calc
        _ = vectorNumeratorEven C.support D.e₂ -
              vectorNumeratorEven C.support D.e₁ := by
            unfold vectorNumeratorEven
            ring
        _ = 0 := by rw [hNe₁, hNe₂]; ring
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left
      (sub_ne_zero.mpr
        (D.ordered.2.1.trans D.ordered.2.2.1).ne'))).symm
  have hprod : C.support 5 = C.support 1 * D.e₁ * D.e₂ := by
    unfold vectorNumeratorEven at hNe₁
    rw [hsum] at hNe₁
    nlinarith
  refine ⟨D, hb1pos, ?_⟩
  intro t
  unfold vectorNumeratorEven
  rw [hsum, hprod]
  ring

lemma pureEven_denominator_roots_locked
    {a p : MonicQuinticCoeff} (ha : a.Hurwitz)
    (Da : QuinticDenominatorInterlacing a)
    (Dp : QuinticDenominatorInterlacing p)
    {b : QuinticNumeratorVector} (hb1 : 0 < b 1)
    (hOdd : ∀ t : ℝ, vectorNumeratorOdd b t = 0)
    (hEven : ∀ t : ℝ, vectorNumeratorEven b t =
      b 1 * ((t - Dp.e₁) * (t - Dp.e₂)))
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ a.vectorCross b t) :
    Da.e₁ = Dp.e₁ ∧ Da.e₂ = Dp.e₂ := by
  apply ordered_quadratic_roots_eq_of_product_nonneg
    Da.ordered.1
    (Da.ordered.2.1.trans Da.ordered.2.2.1)
    Dp.ordered.1
    (Dp.ordered.2.1.trans Dp.ordered.2.2.1)
  intro t ht
  have hcross := hnonneg t ht
  unfold vectorCross at hcross
  rw [hOdd t, mul_zero, add_zero, hEven t, Da.even_eval] at hcross
  have hfactor : 0 < a.c1 * b 1 := mul_pos ha.c1_pos hb1
  have heq :
      (a.c1 * ((t - Da.e₁) * (t - Da.e₂))) *
          (b 1 * ((t - Dp.e₁) * (t - Dp.e₂))) =
        (a.c1 * b 1) *
          (((t - Da.e₁) * (t - Da.e₂)) *
            ((t - Dp.e₁) * (t - Dp.e₂))) := by ring
  rw [heq] at hcross
  exact (mul_nonneg_iff_of_pos_left hfactor).mp hcross

lemma CriticalEndpointMomentCertificate.odd_support_component_ne_zero
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (hsegment : p.allConvexHurwitz q) :
    vectorNumeratorOddPolynomial C.support ≠ 0 := by
  intro hOdd
  obtain ⟨Dp, hb1, hEven⟩ := C.pureEven_support_at_hurwitz hsegment hOdd
  obtain ⟨hb0zero, hb2zero, hb4zero⟩ :=
    (vectorNumeratorOddPolynomial_eq_zero_iff C.support).mp hOdd
  have hOddfun : ∀ t : ℝ, vectorNumeratorOdd C.support t = 0 := by
    intro t
    simp [vectorNumeratorOdd, hb0zero, hb2zero, hb4zero]
  have hnode : ∀ r ∈ C.certificate.finiteNodes,
      r = Dp.e₁ ∨ r = Dp.e₂ := by
    intro r hr
    have ha := C.certificate.mergedDenominator_hurwitz hsegment hr
    obtain ⟨Da⟩ := denominator_interlacing_of_hurwitz ha
    have hnonneg : ∀ t : ℝ, 0 ≤ t →
        0 ≤ (C.certificate.mergedDenominator r).vectorCross C.support t := by
      intro t ht
      rw [C.certificate.mergedDenominator_eq_convex hr]
      exact C.support_cross_nonneg_convex _
        (C.certificate.mergedParameter_mem hr) t ht
    obtain ⟨he₁, he₂⟩ := pureEven_denominator_roots_locked
      ha Da Dp hb1 hOddfun hEven hnonneg
    have hc := C.merged_contact hr
    unfold vectorCross at hc
    rw [hOddfun r, mul_zero, add_zero, hEven r, Da.even_eval] at hc
    rw [he₁, he₂] at hc
    let A := (r - Dp.e₁) * (r - Dp.e₂)
    have hcA : ((C.certificate.mergedDenominator r).c1 * A) *
        (C.support 1 * A) = 0 := by
      simpa only [A] using hc
    have heq : (C.certificate.mergedDenominator r).c1 * C.support 1 *
        (A * A) = 0 := by
      calc
        _ = ((C.certificate.mergedDenominator r).c1 * A) *
            (C.support 1 * A) := by ring
        _ = 0 := hcA
    have hfactor : (C.certificate.mergedDenominator r).c1 *
        C.support 1 ≠ 0 := mul_ne_zero (ne_of_gt ha.c1_pos) (ne_of_gt hb1)
    have hAA : A * A = 0 := (mul_eq_zero.mp heq).resolve_left hfactor
    rcases mul_eq_zero.mp hAA with hA | hA
    · rcases mul_eq_zero.mp hA with h₁ | h₂
      · exact Or.inl (sub_eq_zero.mp h₁)
      · exact Or.inr (sub_eq_zero.mp h₂)
    · rcases mul_eq_zero.mp hA with h₁ | h₂
      · exact Or.inl (sub_eq_zero.mp h₁)
      · exact Or.inr (sub_eq_zero.mp h₂)
  have hcard : C.certificate.finiteNodes.card ≤ 2 := by
    have hsub : C.certificate.finiteNodes ⊆
        ({Dp.e₁, Dp.e₂} : Finset ℝ) := by
      intro r hr
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hnode r hr
    calc
      C.certificate.finiteNodes.card ≤ ({Dp.e₁, Dp.e₂} : Finset ℝ).card :=
        Finset.card_le_card hsub
      _ ≤ ({Dp.e₂} : Finset ℝ).card + 1 :=
        Finset.card_insert_le Dp.e₁ ({Dp.e₂} : Finset ℝ)
      _ ≤ 2 := by simp
  obtain ⟨r, hr⟩ := C.certificate.finiteNodes_nonempty
  have ha := C.certificate.mergedDenominator_hurwitz hsegment hr
  obtain ⟨Da⟩ := denominator_interlacing_of_hurwitz ha
  have hnonneg : ∀ t : ℝ, 0 ≤ t →
      0 ≤ (C.certificate.mergedDenominator r).vectorCross C.support t := by
    intro t ht
    rw [C.certificate.mergedDenominator_eq_convex hr]
    exact C.support_cross_nonneg_convex _
      (C.certificate.mergedParameter_mem hr) t ht
  obtain ⟨he₁, he₂⟩ := pureEven_denominator_roots_locked
    ha Da Dp hb1 hOddfun hEven hnonneg
  have hrpos : 0 < r := by
    rcases hnode r hr with hr₁ | hr₂
    · rw [hr₁]
      exact Dp.ordered.1
    · rw [hr₂]
      exact Dp.ordered.1.trans
        (Dp.ordered.2.1.trans Dp.ordered.2.2.1)
  have hEzero : (C.certificate.mergedDenominator r).evenPart r = 0 := by
    rw [Da.even_eval, he₁, he₂]
    rcases hnode r hr with hr₁ | hr₂
    · rw [hr₁]
      ring
    · rw [hr₂]
      ring
  have hOne : (C.certificate.mergedDenominator r).oddPart r ≠ 0 :=
    oddPart_ne_zero_of_evenPart_zero ha hrpos.le hEzero
  have hz : C.certificate.mergedOddResidue r ≠ 0 := by
    unfold EndpointMomentCertificate.mergedOddResidue
    exact mul_ne_zero
      (mul_ne_zero (ne_of_gt (C.certificate.mergedFiniteWeight_pos hr))
        (ne_of_gt hrpos)) hOne
  have hall := residues_zero_of_vanishing_moments
    Function.injective_id.injOn hcard
      C.certificate.mergedOddResidue_moments r hr
  exact hz hall

@[simp] lemma vectorNumeratorEvenPolynomial_eval
    (b : QuinticNumeratorVector) (r : ℝ) :
    (vectorNumeratorEvenPolynomial b).eval r =
      vectorNumeratorEven b r := by
  simp [vectorNumeratorEvenPolynomial, vectorNumeratorEven]

@[simp] lemma vectorNumeratorOddPolynomial_eval
    (b : QuinticNumeratorVector) (r : ℝ) :
    (vectorNumeratorOddPolynomial b).eval r =
      vectorNumeratorOdd b r := by
  simp [vectorNumeratorOddPolynomial, vectorNumeratorOdd]

lemma vectorNumeratorEvenPolynomial_degree_le_two
    (b : QuinticNumeratorVector) :
    (vectorNumeratorEvenPolynomial b).degree ≤ 2 := by
  unfold vectorNumeratorEvenPolynomial
  compute_degree!

lemma vectorNumeratorEvenPolynomial_natDegree
    (b : QuinticNumeratorVector) (hb1 : b 1 ≠ 0) :
    (vectorNumeratorEvenPolynomial b).natDegree = 2 := by
  unfold vectorNumeratorEvenPolynomial
  compute_degree!

lemma vectorNumeratorOddPolynomial_degree_le_two
    (b : QuinticNumeratorVector) :
    (vectorNumeratorOddPolynomial b).degree ≤ 2 := by
  unfold vectorNumeratorOddPolynomial
  compute_degree!

def vectorCrossPolynomial (a : MonicQuinticCoeff)
    (b : QuinticNumeratorVector) : Polynomial ℝ :=
  (Polynomial.C a.c1 * Polynomial.X ^ 2 -
      Polynomial.C a.c3 * Polynomial.X + Polynomial.C a.c5) *
      vectorNumeratorEvenPolynomial b +
    Polynomial.X *
      (Polynomial.X ^ 2 - Polynomial.C a.c2 * Polynomial.X +
        Polynomial.C a.c4) * vectorNumeratorOddPolynomial b

def firstOrderKernelPolynomial (a : MonicQuinticCoeff) (scale : ℝ) :
    Polynomial ℝ :=
  Polynomial.C a.c1 * Polynomial.X ^ 2 -
      Polynomial.C a.c3 * Polynomial.X + Polynomial.C a.c5 +
    Polynomial.C scale * Polynomial.X *
      (Polynomial.X ^ 2 - Polynomial.C a.c2 * Polynomial.X +
        Polynomial.C a.c4)

@[simp] lemma firstOrderKernelPolynomial_eval
    (a : MonicQuinticCoeff) (scale t : ℝ) :
    (firstOrderKernelPolynomial a scale).eval t =
      a.evenPart t + scale * t * a.oddPart t := by
  simp [firstOrderKernelPolynomial, evenPart, oddPart]

lemma firstOrderKernelPolynomial_natDegree
    (a : MonicQuinticCoeff) {scale : ℝ} (hscale : scale ≠ 0) :
    (firstOrderKernelPolynomial a scale).natDegree = 3 := by
  unfold firstOrderKernelPolynomial
  compute_degree!

@[simp] lemma vectorCrossPolynomial_eval
    (a : MonicQuinticCoeff) (b : QuinticNumeratorVector) (t : ℝ) :
    (vectorCrossPolynomial a b).eval t = a.vectorCross b t := by
  simp [vectorCrossPolynomial, vectorCross, evenPart, oddPart]

lemma vectorCrossPolynomial_natDegree_le_five
    (a : MonicQuinticCoeff) (b : QuinticNumeratorVector) :
    (vectorCrossPolynomial a b).natDegree ≤ 5 := by
  unfold vectorCrossPolynomial vectorNumeratorEvenPolynomial
    vectorNumeratorOddPolynomial
  compute_degree!

lemma vectorCrossPolynomial_natDegree_le_four_of_leading_zero
    (a : MonicQuinticCoeff) (b : QuinticNumeratorVector)
    (hb0 : b 0 = 0) :
    (vectorCrossPolynomial a b).natDegree ≤ 4 := by
  unfold vectorCrossPolynomial vectorNumeratorEvenPolynomial
    vectorNumeratorOddPolynomial
  simp [hb0]
  compute_degree!

lemma vectorCrossPolynomial_ne_zero_of_hurwitz
    {a : MonicQuinticCoeff} (ha : a.Hurwitz)
    {b : QuinticNumeratorVector} (hb1 : 0 < b 1) :
    vectorCrossPolynomial a b ≠ 0 := by
  intro hzero
  obtain ⟨D⟩ := denominator_interlacing_of_hurwitz ha
  have hcross₁ : a.vectorCross b D.o₁ = 0 := by
    rw [← vectorCrossPolynomial_eval, hzero, Polynomial.eval_zero]
  have hcross₂ : a.vectorCross b D.o₂ = 0 := by
    rw [← vectorCrossPolynomial_eval, hzero, Polynomial.eval_zero]
  unfold vectorCross at hcross₁ hcross₂
  simp only [D.roots.2.1, mul_zero, zero_mul, add_zero] at hcross₁
  simp only [D.roots.2.2.2, mul_zero, zero_mul, add_zero] at hcross₂
  have hE₁ : vectorNumeratorEven b D.o₁ = 0 :=
    (mul_eq_zero.mp hcross₁).resolve_left (ne_of_lt (D.even_o₁_neg ha))
  have hE₂ : vectorNumeratorEven b D.o₂ = 0 :=
    (mul_eq_zero.mp hcross₂).resolve_left (ne_of_gt (D.even_o₂_pos ha))
  have hsum : b 3 = b 1 * (D.o₁ + D.o₂) := by
    have hfac : (D.o₂ - D.o₁) *
        (b 1 * (D.o₁ + D.o₂) - b 3) = 0 := by
      calc
        _ = vectorNumeratorEven b D.o₂ -
              vectorNumeratorEven b D.o₁ := by
            unfold vectorNumeratorEven
            ring
        _ = 0 := by rw [hE₁, hE₂]; ring
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left
      (sub_ne_zero.mpr
        (D.ordered.2.2.1.trans D.ordered.2.2.2).ne'))).symm
  have hprod : b 5 = b 1 * D.o₁ * D.o₂ := by
    unfold vectorNumeratorEven at hE₁
    rw [hsum] at hE₁
    nlinarith
  have hb5pos : 0 < b 5 := by
    rw [hprod]
    exact mul_pos (mul_pos hb1 (D.ordered.1.trans D.ordered.2.1))
      (D.ordered.1.trans (D.ordered.2.1.trans
        (D.ordered.2.2.1.trans D.ordered.2.2.2)))
  have hcross0 : a.vectorCross b 0 = 0 := by
    rw [← vectorCrossPolynomial_eval, hzero, Polynomial.eval_zero]
  have hpos : 0 < a.vectorCross b 0 := by
    simpa [vectorCross, evenPart, vectorNumeratorEven] using
      mul_pos ha.c5_pos hb5pos
  linarith

lemma vectorNumeratorEven_eq_zero_of_proportional_kernel_zero
    {a : MonicQuinticCoeff} (ha : a.Hurwitz)
    {b : QuinticNumeratorVector} {scale : ℝ}
    (hscale : 0 < scale) (hb1 : 0 < b 1)
    (hprop : ∀ t : ℝ, vectorNumeratorOdd b t =
      scale * vectorNumeratorEven b t)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ a.vectorCross b t)
    {r : ℝ} (hr : 0 ≤ r)
    (hkernel : a.evenPart r + scale * r * a.oddPart r = 0) :
    vectorNumeratorEven b r = 0 := by
  obtain ⟨D⟩ := denominator_interlacing_of_hurwitz ha
  let E := vectorNumeratorEven b
  let K := fun t : ℝ => a.evenPart t + scale * t * a.oddPart t
  have hcrossfactor (t : ℝ) : a.vectorCross b t = E t * K t := by
    unfold vectorCross
    rw [hprop t]
    dsimp [E, K]
    ring
  have hKe₁ : 0 < K D.e₁ := by
    dsimp [K]
    rw [D.roots.1, zero_add]
    exact mul_pos (mul_pos hscale D.ordered.1) D.odd_e₁_pos
  have hKo₁ : K D.o₁ < 0 := by
    dsimp [K]
    rw [D.roots.2.1, mul_zero, add_zero]
    exact D.even_o₁_neg ha
  have hKe₂ : K D.e₂ < 0 := by
    dsimp [K]
    rw [D.roots.2.2.1, zero_add]
    have he₂pos : 0 < D.e₂ :=
      D.ordered.1.trans (D.ordered.2.1.trans D.ordered.2.2.1)
    exact mul_neg_of_pos_of_neg (mul_pos hscale he₂pos) D.odd_e₂_neg
  have hKo₂ : 0 < K D.o₂ := by
    dsimp [K]
    rw [D.roots.2.2.2, mul_zero, add_zero]
    exact D.even_o₂_pos ha
  have hEe₁ : 0 ≤ E D.e₁ := by
    have hc := hnonneg D.e₁ D.ordered.1.le
    rw [hcrossfactor] at hc
    apply le_of_not_gt
    intro hneg
    exact (not_lt_of_ge hc) (mul_neg_of_neg_of_pos hneg hKe₁)
  have hEo₁ : E D.o₁ ≤ 0 := by
    have hc := hnonneg D.o₁
      (D.ordered.1.trans D.ordered.2.1).le
    rw [hcrossfactor] at hc
    apply le_of_not_gt
    intro hpos
    exact (not_lt_of_ge hc) (mul_neg_of_pos_of_neg hpos hKo₁)
  have hEe₂ : E D.e₂ ≤ 0 := by
    have he₂pos : 0 < D.e₂ :=
      D.ordered.1.trans (D.ordered.2.1.trans D.ordered.2.2.1)
    have hc := hnonneg D.e₂ he₂pos.le
    rw [hcrossfactor] at hc
    apply le_of_not_gt
    intro hpos
    exact (not_lt_of_ge hc) (mul_neg_of_pos_of_neg hpos hKe₂)
  have hEo₂ : 0 ≤ E D.o₂ := by
    have ho₂pos : 0 < D.o₂ :=
      D.ordered.1.trans (D.ordered.2.1.trans
        (D.ordered.2.2.1.trans D.ordered.2.2.2))
    have hc := hnonneg D.o₂ ho₂pos.le
    rw [hcrossfactor] at hc
    apply le_of_not_gt
    intro hneg
    exact (not_lt_of_ge hc) (mul_neg_of_neg_of_pos hneg hKo₂)
  have hEcont : Continuous E := by
    dsimp [E]
    unfold vectorNumeratorEven
    fun_prop
  have hzero₁ : 0 ∈ Set.Icc (E D.o₁) (E D.e₁) := ⟨hEo₁, hEe₁⟩
  obtain ⟨x₁, hx₁mem, hx₁zero⟩ :=
    (intermediate_value_Icc' D.ordered.2.1.le hEcont.continuousOn) hzero₁
  have hzero₂ : 0 ∈ Set.Icc (E D.e₂) (E D.o₂) := ⟨hEe₂, hEo₂⟩
  obtain ⟨x₂, hx₂mem, hx₂zero⟩ :=
    (intermediate_value_Icc D.ordered.2.2.2.le hEcont.continuousOn) hzero₂
  have hx₁pos : 0 < x₁ := D.ordered.1.trans_le hx₁mem.1
  have hx₁x₂ : x₁ < x₂ :=
    hx₁mem.2.trans_lt (D.ordered.2.2.1.trans_le hx₂mem.1)
  have hsum : b 3 = b 1 * (x₁ + x₂) := by
    have hfac : (x₂ - x₁) * (b 1 * (x₁ + x₂) - b 3) = 0 := by
      calc
        _ = E x₂ - E x₁ := by
          dsimp [E]
          unfold vectorNumeratorEven
          ring
        _ = 0 := by rw [hx₁zero, hx₂zero]; ring
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left
      (sub_ne_zero.mpr hx₁x₂.ne'))).symm
  have hprod : b 5 = b 1 * x₁ * x₂ := by
    dsimp [E] at hx₁zero
    unfold vectorNumeratorEven at hx₁zero
    rw [hsum] at hx₁zero
    nlinarith
  have hEfactor (t : ℝ) : E t = b 1 * ((t - x₁) * (t - x₂)) := by
    dsimp [E]
    unfold vectorNumeratorEven
    rw [hsum, hprod]
    ring
  have hKleft : ∀ t ∈ Set.Ioo (0 : ℝ) x₁, 0 ≤ K t := by
    intro t ht
    have hEpos : 0 < E t := by
      rw [hEfactor]
      exact mul_pos hb1 (mul_pos_of_neg_of_neg
        (sub_neg.mpr ht.2) (sub_neg.mpr (ht.2.trans hx₁x₂)))
    have hc := hnonneg t ht.1.le
    rw [hcrossfactor] at hc
    exact (mul_nonneg_iff_of_pos_left hEpos).mp hc
  have hKmiddle : ∀ t ∈ Set.Ioo x₁ x₂, K t ≤ 0 := by
    intro t ht
    have hEneg : E t < 0 := by
      rw [hEfactor]
      exact mul_neg_of_pos_of_neg hb1
        (mul_neg_of_pos_of_neg (sub_pos.mpr ht.1) (sub_neg.mpr ht.2))
    have hc := hnonneg t (hx₁pos.trans ht.1).le
    rw [hcrossfactor] at hc
    apply le_of_not_gt
    intro hKpos
    exact (not_lt_of_ge hc) (mul_neg_of_neg_of_pos hEneg hKpos)
  have hKright : ∀ t ∈ Set.Ioo x₂ (x₂ + 1), 0 ≤ K t := by
    intro t ht
    have hEpos : 0 < E t := by
      rw [hEfactor]
      exact mul_pos hb1 (mul_pos
        (sub_pos.mpr (hx₁x₂.trans ht.1)) (sub_pos.mpr ht.1))
    have hc := hnonneg t (hx₁pos.trans (hx₁x₂.trans ht.1)).le
    rw [hcrossfactor] at hc
    exact (mul_nonneg_iff_of_pos_left hEpos).mp hc
  have hKcont : Continuous K := by
    dsimp [K]
    unfold evenPart oddPart
    fun_prop
  have hKx₁ : K x₁ = 0 :=
    eq_zero_of_nonneg_left_nonpos_right hKcont hx₁pos hx₁x₂
      hKleft hKmiddle
  have hKx₂ : K x₂ = 0 :=
    eq_zero_of_nonpos_left_nonneg_right hKcont hx₁x₂ (by linarith)
      hKmiddle hKright
  by_contra hEr
  have hrpos : 0 < r := by
    rcases hr.eq_or_lt with rfl | hrpos
    · have : 0 < K 0 := by
        dsimp [K]
        simpa [evenPart] using ha.c5_pos
      have hkzero : K 0 = 0 := by simpa [K] using hkernel
      exact False.elim ((ne_of_gt this) hkzero)
    · exact hrpos
  have hrx₁ : r ≠ x₁ := by
    intro heq
    apply hEr
    rw [heq]
    exact hx₁zero
  have hrx₂ : r ≠ x₂ := by
    intro heq
    apply hEr
    rw [heq]
    exact hx₂zero
  let KP := firstOrderKernelPolynomial a scale
  have hKPdegree : KP.natDegree = 3 :=
    firstOrderKernelPolynomial_natDegree a (ne_of_gt hscale)
  have hKPne : KP ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hKPdegree
    omega
  have hKPr : KP.eval r = 0 := by simpa [KP, K] using hkernel
  have hKPx₁ : KP.eval x₁ = 0 := by simpa [KP, K] using hKx₁
  have hKPx₂ : KP.eval x₂ = 0 := by simpa [KP, K] using hKx₂
  have hderiv : KP.derivative.eval r = 0 := by
    rcases lt_trichotomy r x₁ with hrleft | hrequal | hrright
    · have hlocal : IsLocalMin KP.eval r := by
        filter_upwards [Ioo_mem_nhds hrpos hrleft] with t ht
        rw [hKPr]
        simpa [KP, K] using hKleft t ht
      rw [← KP.deriv]
      exact hlocal.deriv_eq_zero
    · exact False.elim (hrx₁ hrequal)
    · rcases lt_trichotomy r x₂ with hrmiddle | hrequal | hrright₂
      · have hlocal : IsLocalMax KP.eval r := by
          filter_upwards [Ioo_mem_nhds hrright hrmiddle] with t ht
          rw [hKPr]
          simpa [KP, K] using hKmiddle t ht
        rw [← KP.deriv]
        exact hlocal.deriv_eq_zero
      · exact False.elim (hrx₂ hrequal)
      · have hlocal : IsLocalMin KP.eval r := by
          filter_upwards [Ioi_mem_nhds hrright₂] with t ht
          rw [hKPr]
          have ht' : x₂ < t := ht
          have hKt : 0 ≤ K t := by
            have hEpos : 0 < E t := by
              rw [hEfactor]
              exact mul_pos hb1 (mul_pos
                (sub_pos.mpr (hx₁x₂.trans ht'))
                (sub_pos.mpr ht'))
            have hc := hnonneg t
              (hx₁pos.trans (hx₁x₂.trans ht')).le
            rw [hcrossfactor] at hc
            exact (mul_nonneg_iff_of_pos_left hEpos).mp hc
          simpa [KP, K] using hKt
        rw [← KP.deriv]
        exact hlocal.deriv_eq_zero
  have hfour := four_le_natDegree_of_three_roots_of_one_double
    KP hKPne hrx₁ hrx₂ hx₁x₂.ne hKPr hderiv hKPx₁ hKPx₂
  omega

lemma noncoprime_vectorNumerator_components_cases
    (b : QuinticNumeratorVector) (hb1 : b 1 ≠ 0)
    (hncop : ¬ IsCoprime
      (vectorNumeratorEvenPolynomial b)
      (vectorNumeratorOddPolynomial b)) :
    (∃ r : ℝ, vectorNumeratorEven b r = 0 ∧
        vectorNumeratorOdd b r = 0) ∨
      (∃ scale : ℝ, ∀ t : ℝ, vectorNumeratorOdd b t =
        scale * vectorNumeratorEven b t) := by
  let E := vectorNumeratorEvenPolynomial b
  let O := vectorNumeratorOddPolynomial b
  let scale := b 0 / b 1
  let u := -b 2 + scale * b 3
  let v := b 4 - scale * b 5
  have hpoly : O = Polynomial.C scale * E +
      (Polynomial.C u * Polynomial.X + Polynomial.C v) := by
    apply Polynomial.funext
    intro t
    simp [O, E, scale, u, v, vectorNumeratorEvenPolynomial,
      vectorNumeratorOddPolynomial]
    field_simp [hb1]
    ring
  by_cases hu : u = 0
  · by_cases hv : v = 0
    · apply Or.inr
      refine ⟨scale, ?_⟩
      intro t
      have heval := congrArg (fun P : Polynomial ℝ => P.eval t) hpoly
      rw [hu, hv] at heval
      simpa [E, O] using heval
    · exfalso
      apply hncop
      have hunit : IsUnit (Polynomial.C v) :=
        Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hv)
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv'.mp hunit
      have hcop : IsCoprime E (Polynomial.C v) := by
        refine ⟨0, w, ?_⟩
        simpa using hw
      have hadd := hcop.add_mul_right_right (Polynomial.C scale)
      change IsCoprime E O
      rw [hpoly, hu]
      simpa [add_comm] using hadd
  · let r := -v / u
    have hlinear : Polynomial.C u * Polynomial.X + Polynomial.C v =
        Polynomial.C u * (Polynomial.X - Polynomial.C r) := by
      apply Polynomial.funext
      intro t
      simp [r]
      field_simp [hu]
      ring
    by_cases hEr : vectorNumeratorEven b r = 0
    · apply Or.inl
      refine ⟨r, hEr, ?_⟩
      have heval := congrArg (fun P : Polynomial ℝ => P.eval r) hpoly
      rw [hlinear] at heval
      simpa [E, O, hEr] using heval
    · exfalso
      apply hncop
      have hnotdvd : ¬ (Polynomial.X - Polynomial.C r) ∣ E := by
        intro hdvd
        have hroot := Polynomial.dvd_iff_isRoot.mp hdvd
        exact hEr (by simpa [E, vectorNumeratorEvenPolynomial] using hroot)
      have hcopLinear : IsCoprime E
          (Polynomial.X - Polynomial.C r) :=
        ((Polynomial.prime_X_sub_C r).coprime_iff_not_dvd.mpr hnotdvd).symm
      have hunit : IsUnit (Polynomial.C u) :=
        Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hu)
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv'.mp hunit
      have hcopUnit : IsCoprime E (Polynomial.C u) := by
        refine ⟨0, w, ?_⟩
        simpa using hw
      have hcopProduct := hcopUnit.mul_right hcopLinear
      have hadd := hcopProduct.add_mul_right_right (Polynomial.C scale)
      change IsCoprime E O
      rw [hpoly, hlinear]
      simpa [add_comm] using hadd

lemma CriticalEndpointMomentCertificate.finiteNodes_subset_endpointCross_roots
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (hsegment : p.allConvexHurwitz q) :
    C.certificate.finiteNodes ⊆
      nonnegativeRealRoots (vectorCrossPolynomial p C.support) ∪
        nonnegativeRealRoots (vectorCrossPolynomial q C.support) := by
  have hP : vectorCrossPolynomial p C.support ≠ 0 :=
    vectorCrossPolynomial_ne_zero_of_hurwitz
      (allConvexHurwitz_left hsegment) (C.support_one_pos hsegment)
  have hQ : vectorCrossPolynomial q C.support ≠ 0 :=
    vectorCrossPolynomial_ne_zero_of_hurwitz
      (allConvexHurwitz_right hsegment) (C.support_one_pos hsegment)
  intro r hr
  obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp hr
  subst r
  have hc := C.finite_contact_cross hi
  have ht := C.certificate.finiteFrequency_nonneg hi
  cases hright : C.certificate.rightEndpoint i with
  | false =>
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨?_, ht⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
      change (vectorCrossPolynomial p C.support).eval
        (C.certificate.finiteFrequency i) = 0
      rw [vectorCrossPolynomial_eval]
      simpa [selectedEndpoint, hright] using hc
  | true =>
      apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨?_, ht⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ]
      change (vectorCrossPolynomial q C.support).eval
        (C.certificate.finiteFrequency i) = 0
      rw [vectorCrossPolynomial_eval]
      simpa [selectedEndpoint, hright] using hc

lemma CriticalEndpointMomentCertificate.finiteNodes_card_le_five_by_contacts
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (hsegment : p.allConvexHurwitz q) :
    C.certificate.finiteNodes.card ≤ 5 := by
  let P := vectorCrossPolynomial p C.support
  let Q := vectorCrossPolynomial q C.support
  have hP : P ≠ 0 := vectorCrossPolynomial_ne_zero_of_hurwitz
    (allConvexHurwitz_left hsegment) (C.support_one_pos hsegment)
  have hQ : Q ≠ 0 := vectorCrossPolynomial_ne_zero_of_hurwitz
    (allConvexHurwitz_right hsegment) (C.support_one_pos hsegment)
  have hnonnegP : ∀ t : ℝ, 0 ≤ t → 0 ≤ P.eval t := by
    intro t ht
    rw [show P.eval t = p.vectorCross C.support t by
      simp [P, vectorCrossPolynomial_eval]]
    have h := C.support_cross_nonneg false t ht
    simpa only [selectedEndpoint, Bool.false_eq_true, if_false] using h
  have hnonnegQ : ∀ t : ℝ, 0 ≤ t → 0 ≤ Q.eval t := by
    intro t ht
    rw [show Q.eval t = q.vectorCross C.support t by
      simp [Q, vectorCrossPolynomial_eval]]
    have h := C.support_cross_nonneg true t ht
    simpa only [selectedEndpoint, if_true] using h
  have hrootCard := union_nonnegativeRealRoots_card_le_five_of_degree_le_five
    P Q hP hQ hnonnegP hnonnegQ
    (by simpa [P] using
      vectorCrossPolynomial_natDegree_le_five p C.support)
    (by simpa [Q] using
      vectorCrossPolynomial_natDegree_le_five q C.support)
  exact (Finset.card_le_card
    (C.finiteNodes_subset_endpointCross_roots hsegment)).trans hrootCard

lemma CriticalEndpointMomentCertificate.finiteNodes_card_le_four_of_support_zero
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (hsegment : p.allConvexHurwitz q) (hb0 : C.support 0 = 0) :
    C.certificate.finiteNodes.card ≤ 4 := by
  let P := vectorCrossPolynomial p C.support
  let Q := vectorCrossPolynomial q C.support
  have hP : P ≠ 0 := vectorCrossPolynomial_ne_zero_of_hurwitz
    (allConvexHurwitz_left hsegment) (C.support_one_pos hsegment)
  have hQ : Q ≠ 0 := vectorCrossPolynomial_ne_zero_of_hurwitz
    (allConvexHurwitz_right hsegment) (C.support_one_pos hsegment)
  have hnonnegP : ∀ t : ℝ, 0 ≤ t → 0 ≤ P.eval t := by
    intro t ht
    rw [show P.eval t = p.vectorCross C.support t by
      simp [P, vectorCrossPolynomial_eval]]
    have h := C.support_cross_nonneg false t ht
    simpa only [selectedEndpoint, Bool.false_eq_true, if_false] using h
  have hnonnegQ : ∀ t : ℝ, 0 ≤ t → 0 ≤ Q.eval t := by
    intro t ht
    rw [show Q.eval t = q.vectorCross C.support t by
      simp [Q, vectorCrossPolynomial_eval]]
    have h := C.support_cross_nonneg true t ht
    simpa only [selectedEndpoint, if_true] using h
  have hrootCard := union_nonnegativeRealRoots_card_le_four_of_degree_le_four
    P Q hP hQ hnonnegP hnonnegQ
    (by
      simpa [P] using
        (vectorCrossPolynomial_natDegree_le_four_of_leading_zero
          p C.support hb0))
    (by
      simpa [Q] using
        (vectorCrossPolynomial_natDegree_le_four_of_leading_zero
          q C.support hb0))
  exact (Finset.card_le_card
    (C.finiteNodes_subset_endpointCross_roots hsegment)).trans hrootCard

lemma CriticalEndpointMomentCertificate.finiteNodes_card_le_four_of_common_root
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (hsegment : p.allConvexHurwitz q) {r : ℝ} (hr : 0 ≤ r)
    (hEven : vectorNumeratorEven C.support r = 0)
    (hOdd : vectorNumeratorOdd C.support r = 0) :
    C.certificate.finiteNodes.card ≤ 4 := by
  let P := vectorCrossPolynomial p C.support
  let Q := vectorCrossPolynomial q C.support
  have hP : P ≠ 0 := vectorCrossPolynomial_ne_zero_of_hurwitz
    (allConvexHurwitz_left hsegment) (C.support_one_pos hsegment)
  have hQ : Q ≠ 0 := vectorCrossPolynomial_ne_zero_of_hurwitz
    (allConvexHurwitz_right hsegment) (C.support_one_pos hsegment)
  have hnonnegP : ∀ t : ℝ, 0 ≤ t → 0 ≤ P.eval t := by
    intro t ht
    rw [show P.eval t = p.vectorCross C.support t by
      simp [P, vectorCrossPolynomial_eval]]
    have h := C.support_cross_nonneg false t ht
    simpa only [selectedEndpoint, Bool.false_eq_true, if_false] using h
  have hnonnegQ : ∀ t : ℝ, 0 ≤ t → 0 ≤ Q.eval t := by
    intro t ht
    rw [show Q.eval t = q.vectorCross C.support t by
      simp [Q, vectorCrossPolynomial_eval]]
    have h := C.support_cross_nonneg true t ht
    simpa only [selectedEndpoint, if_true] using h
  have hProot : P.eval r = 0 := by
    rw [show P.eval r = p.vectorCross C.support r by
      simp [P, vectorCrossPolynomial_eval]]
    unfold vectorCross
    rw [hEven, hOdd, mul_zero, mul_zero, add_zero]
  have hQroot : Q.eval r = 0 := by
    rw [show Q.eval r = q.vectorCross C.support r by
      simp [Q, vectorCrossPolynomial_eval]]
    unfold vectorCross
    rw [hEven, hOdd, mul_zero, mul_zero, add_zero]
  have hrootCard :
      (nonnegativeRealRoots P ∪ nonnegativeRealRoots Q).card ≤ 4 := by
    rcases hr.eq_or_lt with rfl | hrpos
    · have hb5 : C.support 5 = 0 := by
        simpa [vectorNumeratorEven] using hEven
      have hb4 : C.support 4 = 0 := by
        simpa [vectorNumeratorOdd] using hOdd
      obtain ⟨_, _, _, hb3, _, _⟩ :=
        C.support_coefficients_nonneg (allConvexHurwitz_left hsegment)
      have hPderiv_nonneg :=
        polynomial_derivative_zero_nonneg P hnonnegP hProot
      have hPderiv_formula : P.derivative.eval 0 =
          -p.c5 * C.support 3 := by
        simp [P, vectorCrossPolynomial, vectorNumeratorEvenPolynomial,
          vectorNumeratorOddPolynomial, hb4, hb5]
      have hb3zero : C.support 3 = 0 := by
        rw [hPderiv_formula] at hPderiv_nonneg
        have hp5 := (allConvexHurwitz_left hsegment).c5_pos
        nlinarith
      have hPderiv : P.derivative.eval 0 = 0 := by
        rw [hPderiv_formula, hb3zero]
        ring
      have hQderiv : Q.derivative.eval 0 = 0 := by
        simp [Q, vectorCrossPolynomial, vectorNumeratorEvenPolynomial,
          vectorNumeratorOddPolynomial, hb3zero, hb4, hb5]
      exact (union_nonnegativeRealRoots_card_le_three_of_double_zero
        P Q hP hQ hnonnegP hnonnegQ
        (by simpa [P] using
          vectorCrossPolynomial_natDegree_le_five p C.support)
        (by simpa [Q] using
          vectorCrossPolynomial_natDegree_le_five q C.support)
        hProot hQroot hPderiv hQderiv).trans (by omega)
    · exact union_nonnegativeRealRoots_card_le_four_of_shared_positive_root
        P Q hP hQ hnonnegP hnonnegQ
        (by simpa [P] using
          vectorCrossPolynomial_natDegree_le_five p C.support)
        (by simpa [Q] using
          vectorCrossPolynomial_natDegree_le_five q C.support)
        hrpos hProot hQroot
  exact (Finset.card_le_card
    (C.finiteNodes_subset_endpointCross_roots hsegment)).trans hrootCard

lemma CriticalEndpointMomentCertificate.finiteNodes_card_le_three_of_common_root_of_support_zero
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (hsegment : p.allConvexHurwitz q) (hb0 : C.support 0 = 0)
    {r : ℝ} (hr : 0 ≤ r)
    (hEven : vectorNumeratorEven C.support r = 0)
    (hOdd : vectorNumeratorOdd C.support r = 0) :
    C.certificate.finiteNodes.card ≤ 3 := by
  let P := vectorCrossPolynomial p C.support
  let Q := vectorCrossPolynomial q C.support
  have hP : P ≠ 0 := vectorCrossPolynomial_ne_zero_of_hurwitz
    (allConvexHurwitz_left hsegment) (C.support_one_pos hsegment)
  have hQ : Q ≠ 0 := vectorCrossPolynomial_ne_zero_of_hurwitz
    (allConvexHurwitz_right hsegment) (C.support_one_pos hsegment)
  have hnonnegP : ∀ t : ℝ, 0 ≤ t → 0 ≤ P.eval t := by
    intro t ht
    rw [show P.eval t = p.vectorCross C.support t by
      simp [P, vectorCrossPolynomial_eval]]
    have h := C.support_cross_nonneg false t ht
    simpa only [selectedEndpoint, Bool.false_eq_true, if_false] using h
  have hnonnegQ : ∀ t : ℝ, 0 ≤ t → 0 ≤ Q.eval t := by
    intro t ht
    rw [show Q.eval t = q.vectorCross C.support t by
      simp [Q, vectorCrossPolynomial_eval]]
    have h := C.support_cross_nonneg true t ht
    simpa only [selectedEndpoint, if_true] using h
  have hPcard := nonnegativeRealRoots_card_le_two_of_degree_le_four
    P hP hnonnegP (by simpa [P] using
      (vectorCrossPolynomial_natDegree_le_four_of_leading_zero
        p C.support hb0))
  have hQcard := nonnegativeRealRoots_card_le_two_of_degree_le_four
    Q hQ hnonnegQ (by simpa [Q] using
      (vectorCrossPolynomial_natDegree_le_four_of_leading_zero
        q C.support hb0))
  have hProot : P.eval r = 0 := by
    rw [show P.eval r = p.vectorCross C.support r by
      simp [P, vectorCrossPolynomial_eval]]
    unfold vectorCross
    rw [hEven, hOdd, mul_zero, mul_zero, add_zero]
  have hQroot : Q.eval r = 0 := by
    rw [show Q.eval r = q.vectorCross C.support r by
      simp [Q, vectorCrossPolynomial_eval]]
    unfold vectorCross
    rw [hEven, hOdd, mul_zero, mul_zero, add_zero]
  have hrPmem : r ∈ nonnegativeRealRoots P := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hr⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact hProot
  have hrQmem : r ∈ nonnegativeRealRoots Q := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hr⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ]
    exact hQroot
  have hinter : 1 ≤
      (nonnegativeRealRoots P ∩ nonnegativeRealRoots Q).card :=
    Finset.one_le_card.mpr ⟨r, Finset.mem_inter.mpr ⟨hrPmem, hrQmem⟩⟩
  have hrootCard :
      (nonnegativeRealRoots P ∪ nonnegativeRealRoots Q).card ≤ 3 := by
    have hcard := Finset.card_union_add_card_inter
      (nonnegativeRealRoots P) (nonnegativeRealRoots Q)
    omega
  exact (Finset.card_le_card
    (C.finiteNodes_subset_endpointCross_roots hsegment)).trans hrootCard

lemma EndpointMomentCertificate.oddInterpolationPolynomial_degree
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q) :
    C.oddInterpolationPolynomial.degree + 2 <
      (C.finiteNodes.card : WithBot ℕ) := by
  exact degree_quinticResiduePolynomial_of_moments
    C.finiteNodes id C.mergedOddResidue 2 C.mergedOddResidue_moments

lemma CriticalEndpointMomentCertificate.oddInterpolationPolynomial_ne_zero
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (hsegment : p.allConvexHurwitz q) :
    C.certificate.oddInterpolationPolynomial ≠ 0 := by
  intro hV
  have hNeven := C.even_support_component_ne_zero hsegment
  have hsub : C.certificate.finiteNodes ⊆
      (vectorNumeratorEvenPolynomial C.support).roots.toFinset := by
    intro r hr
    have hzOdd : C.certificate.mergedOddResidue r = 0 := by
      by_contra hz
      exact (quinticResiduePolynomial_ne_zero
        Function.injective_id.injOn hr hz) hV
    have ha := C.certificate.mergedDenominator_hurwitz hsegment hr
    have hr_or_hO : r = 0 ∨
        (C.certificate.mergedDenominator r).oddPart r = 0 := by
      unfold EndpointMomentCertificate.mergedOddResidue at hzOdd
      rcases mul_eq_zero.mp hzOdd with hwr | hO
      · rcases mul_eq_zero.mp hwr with hw | hrzero
        · exact False.elim
            ((ne_of_gt (C.certificate.mergedFiniteWeight_pos hr)) hw)
        · exact Or.inl hrzero
      · exact Or.inr hO
    have hEne : (C.certificate.mergedDenominator r).evenPart r ≠ 0 := by
      rcases hr_or_hO with hrzero | hO
      · subst r
        simpa [evenPart] using ne_of_gt ha.c5_pos
      · exact evenPart_ne_zero_of_oddPart_zero ha
          (C.certificate.finiteNode_nonneg hr) hO
    have hoddterm : r * (C.certificate.mergedDenominator r).oddPart r *
        vectorNumeratorOdd C.support r = 0 := by
      rcases hr_or_hO with hrzero | hO
      · rw [hrzero, zero_mul, zero_mul]
      · rw [hO, mul_zero, zero_mul]
    have hc := C.merged_contact hr
    unfold vectorCross at hc
    rw [hoddterm, add_zero] at hc
    have hNzero : vectorNumeratorEven C.support r = 0 :=
      (mul_eq_zero.mp hc).resolve_left hEne
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hNeven]
    simpa using hNzero
  have hcard : C.certificate.finiteNodes.card ≤ 2 := by
    calc
      C.certificate.finiteNodes.card ≤
          (vectorNumeratorEvenPolynomial C.support).roots.toFinset.card :=
        Finset.card_le_card hsub
      _ ≤ (vectorNumeratorEvenPolynomial C.support).roots.card :=
        Multiset.toFinset_card_le _
      _ ≤ (vectorNumeratorEvenPolynomial C.support).natDegree :=
        Polynomial.card_roots' _
      _ = 2 := vectorNumeratorEvenPolynomial_natDegree C.support
        (ne_of_gt (C.support_one_pos hsegment))
  obtain ⟨r, hr⟩ := C.certificate.finiteNodes_nonempty
  have hzOdd : C.certificate.mergedOddResidue r = 0 := by
    by_contra hz
    exact (quinticResiduePolynomial_ne_zero
      Function.injective_id.injOn hr hz) hV
  have ha := C.certificate.mergedDenominator_hurwitz hsegment hr
  have hr_or_hO : r = 0 ∨
      (C.certificate.mergedDenominator r).oddPart r = 0 := by
    unfold EndpointMomentCertificate.mergedOddResidue at hzOdd
    rcases mul_eq_zero.mp hzOdd with hwr | hO
    · rcases mul_eq_zero.mp hwr with hw | hrzero
      · exact False.elim
          ((ne_of_gt (C.certificate.mergedFiniteWeight_pos hr)) hw)
      · exact Or.inl hrzero
    · exact Or.inr hO
  have hEne : (C.certificate.mergedDenominator r).evenPart r ≠ 0 := by
    rcases hr_or_hO with hrzero | hO
    · subst r
      simpa [evenPart] using ne_of_gt ha.c5_pos
    · exact evenPart_ne_zero_of_oddPart_zero ha
        (C.certificate.finiteNode_nonneg hr) hO
  have hzEven : C.certificate.mergedEvenResidue r ≠ 0 := by
    unfold EndpointMomentCertificate.mergedEvenResidue
    exact mul_ne_zero
      (ne_of_gt (C.certificate.mergedFiniteWeight_pos hr)) hEne
  have hall := residues_zero_of_vanishing_moments
    Function.injective_id.injOn (hcard.trans (by omega))
      C.certificate.mergedEvenResidue_moments r hr
  exact hzEven hall

lemma EndpointMomentCertificate.oddInterpolation_natDegree_add_two_lt_card
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    (hV : C.oddInterpolationPolynomial ≠ 0) :
    C.oddInterpolationPolynomial.natDegree + 2 < C.finiteNodes.card := by
  have hdegree := C.oddInterpolationPolynomial_degree
  rw [Polynomial.degree_eq_natDegree hV] at hdegree
  exact_mod_cast hdegree

lemma EndpointMomentCertificate.oddInterpolation_natDegree_add_three_lt_card
    {p q : MonicQuinticCoeff} (C : EndpointMomentCertificate p q)
    (hV : C.oddInterpolationPolynomial ≠ 0)
    (hinfinity : C.mergedInfinityWeight = 0) :
    C.oddInterpolationPolynomial.natDegree + 3 < C.finiteNodes.card := by
  have hdegree := degree_quinticResiduePolynomial_of_moments
    C.finiteNodes id C.mergedOddResidue 3
      (C.mergedOddResidue_three_moments hinfinity)
  change C.oddInterpolationPolynomial.degree + 3 <
    (C.finiteNodes.card : WithBot ℕ) at hdegree
  rw [Polynomial.degree_eq_natDegree hV] at hdegree
  exact_mod_cast hdegree

lemma CriticalEndpointMomentCertificate.interpolation_identity
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q) :
    vectorNumeratorEvenPolynomial C.support *
        C.certificate.evenInterpolationPolynomial +
      vectorNumeratorOddPolynomial C.support *
        C.certificate.oddInterpolationPolynomial = 0 := by
  apply contact_quinticResiduePolynomial_identity
    C.certificate.finiteNodes id
    C.certificate.mergedEvenResidue C.certificate.mergedOddResidue
    Function.injective_id.injOn
  · exact vectorNumeratorEvenPolynomial_degree_le_two C.support
  · exact vectorNumeratorOddPolynomial_degree_le_two C.support
  · intro j hj
    exact C.certificate.mergedEvenResidue_moments j (hj.trans (by omega))
  · exact C.certificate.mergedOddResidue_moments
  · intro r hr
    simp only [id_eq, vectorNumeratorEvenPolynomial_eval,
      vectorNumeratorOddPolynomial_eval, EndpointMomentCertificate.mergedEvenResidue,
      EndpointMomentCertificate.mergedOddResidue]
    have hc := C.merged_contact hr
    unfold vectorCross at hc
    calc
      _ = C.certificate.mergedFiniteWeight r *
          ((C.certificate.mergedDenominator r).evenPart r *
              vectorNumeratorEven C.support r +
            r * (C.certificate.mergedDenominator r).oddPart r *
              vectorNumeratorOdd C.support r) := by ring
      _ = 0 := by rw [hc, mul_zero]

lemma CriticalEndpointMomentCertificate.oddInterpolation_natDegree_pos_of_common_root
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (hsegment : p.allConvexHurwitz q) {r : ℝ}
    (hEven : vectorNumeratorEven C.support r = 0)
    (hOdd : vectorNumeratorOdd C.support r = 0)
    (hnotprop : ¬∃ scale : ℝ, ∀ t : ℝ,
      vectorNumeratorOdd C.support t =
        scale * vectorNumeratorEven C.support t) :
    1 ≤ C.certificate.oddInterpolationPolynomial.natDegree := by
  let E := vectorNumeratorEvenPolynomial C.support
  let O := vectorNumeratorOddPolynomial C.support
  let U := C.certificate.evenInterpolationPolynomial
  let V := C.certificate.oddInterpolationPolynomial
  let L : Polynomial ℝ := Polynomial.X - Polynomial.C r
  let E₁ : Polynomial ℝ :=
    Polynomial.C (C.support 1) * Polynomial.X +
      Polynomial.C (C.support 1 * r - C.support 3)
  let O₁ : Polynomial ℝ :=
    Polynomial.C (C.support 0) * Polynomial.X +
      Polynomial.C (C.support 0 * r - C.support 2)
  have hb1 : C.support 1 ≠ 0 := ne_of_gt (C.support_one_pos hsegment)
  have hEfac : E = L * E₁ := by
    apply Polynomial.funext
    intro t
    simp [E, L, E₁, vectorNumeratorEvenPolynomial]
    unfold vectorNumeratorEven at hEven
    nlinarith
  have hOfac : O = L * O₁ := by
    apply Polynomial.funext
    intro t
    simp [O, L, O₁, vectorNumeratorOddPolynomial]
    unfold vectorNumeratorOdd at hOdd
    nlinarith
  let delta : ℝ :=
    C.support 0 * C.support 3 - C.support 1 * C.support 2
  have hdelta : delta ≠ 0 := by
    intro hdelta0
    apply hnotprop
    let scale : ℝ := C.support 0 / C.support 1
    have hlinear : O₁ = Polynomial.C scale * E₁ := by
      apply Polynomial.funext
      intro t
      simp [O₁, E₁, scale]
      field_simp [hb1]
      dsimp [delta] at hdelta0
      nlinarith
    have hpoly : O = Polynomial.C scale * E := by
      rw [hOfac, hlinear, hEfac]
      ring
    refine ⟨scale, ?_⟩
    intro t
    have heval := congrArg (fun P : Polynomial ℝ => P.eval t) hpoly
    simpa [E, O] using heval
  have hcop : IsCoprime E₁ O₁ := by
    refine ⟨Polynomial.C (-C.support 0 / delta),
      Polynomial.C (C.support 1 / delta), ?_⟩
    apply Polynomial.funext
    intro t
    simp [E₁, O₁, delta]
    field_simp [hdelta]
    ring
  have hE₁degree : E₁.natDegree = 1 := by
    dsimp [E₁]
    compute_degree!
  have hE₁ne : E₁ ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hE₁degree
    omega
  have hLne : L ≠ 0 := by
    exact Polynomial.X_sub_C_ne_zero r
  have hid : E * U + O * V = 0 := by
    simpa [E, O, U, V] using C.interpolation_identity
  have hcancel : E₁ * U + O₁ * V = 0 := by
    have hmul : L * (E₁ * U + O₁ * V) = 0 := by
      calc
        L * (E₁ * U + O₁ * V) = E * U + O * V := by
          rw [hEfac, hOfac]
          ring
        _ = 0 := hid
    exact (mul_eq_zero.mp hmul).resolve_left hLne
  obtain ⟨R, hVfac, _⟩ :=
    coprime_quintic_contact_multiplier hcop hE₁ne hcancel
  have hVne := C.oddInterpolationPolynomial_ne_zero hsegment
  have hRne : R ≠ 0 := by
    intro hRzero
    apply hVne
    simpa [V, hRzero] using hVfac
  have hdegree : V.natDegree = 1 + R.natDegree := by
    rw [hVfac, Polynomial.natDegree_mul hE₁ne hRne, hE₁degree]
  simpa [V] using (show 1 ≤ V.natDegree by omega)

lemma CriticalEndpointMomentCertificate.false_of_common_root_nonproportional
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (hsegment : p.allConvexHurwitz q) {r : ℝ}
    (hEven : vectorNumeratorEven C.support r = 0)
    (hOdd : vectorNumeratorOdd C.support r = 0)
    (hnotprop : ¬∃ scale : ℝ, ∀ t : ℝ,
      vectorNumeratorOdd C.support t =
        scale * vectorNumeratorEven C.support t) :
    False := by
  have hr : 0 ≤ r := by
    by_contra hr
    have hrneg : r < 0 := lt_of_not_ge hr
    obtain ⟨_, _, _, hb3, _, hb5⟩ :=
      C.support_coefficients_nonneg (allConvexHurwitz_left hsegment)
    have hb1 := C.support_one_pos hsegment
    unfold vectorNumeratorEven at hEven
    have hsquare : 0 < r ^ 2 := sq_pos_of_ne_zero (ne_of_lt hrneg)
    have hlead : 0 < C.support 1 * r ^ 2 := mul_pos hb1 hsquare
    have hmiddle : 0 ≤ -(C.support 3) * r :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hb3) hrneg.le
    nlinarith
  have hVne := C.oddInterpolationPolynomial_ne_zero hsegment
  have hVdegree := C.oddInterpolation_natDegree_pos_of_common_root
    hsegment hEven hOdd hnotprop
  by_cases hinfinity : C.certificate.mergedInfinityWeight = 0
  · have hlower :=
      C.certificate.oddInterpolation_natDegree_add_three_lt_card
        hVne hinfinity
    have hupper := C.finiteNodes_card_le_four_of_common_root
      hsegment hr hEven hOdd
    omega
  · have hinfinitypos : 0 < C.certificate.mergedInfinityWeight :=
      lt_of_le_of_ne C.certificate.mergedInfinityWeight_nonneg
        (Ne.symm hinfinity)
    have hb0 : C.support 0 = 0 :=
      (mul_eq_zero.mp C.infinity_contact).resolve_left hinfinity
    have hlower :=
      C.certificate.oddInterpolation_natDegree_add_two_lt_card hVne
    have hupper :=
      C.finiteNodes_card_le_three_of_common_root_of_support_zero
        hsegment hb0 hr hEven hOdd
    omega

lemma CriticalEndpointMomentCertificate.false_of_support_proportional
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (hsegment : p.allConvexHurwitz q) {scale : ℝ}
    (hprop : ∀ t : ℝ, vectorNumeratorOdd C.support t =
      scale * vectorNumeratorEven C.support t) :
    False := by
  let E := vectorNumeratorEvenPolynomial C.support
  let O := vectorNumeratorOddPolynomial C.support
  let U := C.certificate.evenInterpolationPolynomial
  let V := C.certificate.oddInterpolationPolynomial
  have hEne : E ≠ 0 := C.even_support_component_ne_zero hsegment
  have hOne : O ≠ 0 := C.odd_support_component_ne_zero hsegment
  have hpoly : O = Polynomial.C scale * E := by
    apply Polynomial.funext
    intro t
    simpa [E, O] using hprop t
  have hb0eq : C.support 0 = scale * C.support 1 := by
    have hc := congrArg (fun P : Polynomial ℝ => P.coeff 2) hpoly
    simpa [E, O, vectorNumeratorEvenPolynomial,
      vectorNumeratorOddPolynomial] using hc
  have hscale_ne : scale ≠ 0 := by
    intro hzero
    apply hOne
    rw [hpoly, hzero, map_zero, zero_mul]
  have hb1pos := C.support_one_pos hsegment
  obtain ⟨hb0, _, _, _, _, _⟩ :=
    C.support_coefficients_nonneg (allConvexHurwitz_left hsegment)
  have hscale : 0 < scale := by
    have hnonneg : 0 ≤ scale := by
      rw [hb0eq] at hb0
      nlinarith
    exact lt_of_le_of_ne hnonneg (Ne.symm hscale_ne)
  have hb0pos : 0 < C.support 0 := by
    rw [hb0eq]
    exact mul_pos hscale hb1pos
  have hinfinity : C.certificate.mergedInfinityWeight = 0 :=
    (mul_eq_zero.mp C.infinity_contact).resolve_right (ne_of_gt hb0pos)
  have hid : E * U + O * V = 0 := by
    simpa [E, O, U, V] using C.interpolation_identity
  have hUV : U + Polynomial.C scale * V = 0 := by
    have hmul : E * (U + Polynomial.C scale * V) = 0 := by
      calc
        E * (U + Polynomial.C scale * V) = E * U + O * V := by
          rw [hpoly]
          ring
        _ = 0 := hid
    exact (mul_eq_zero.mp hmul).resolve_left hEne
  have hresidue (r : ℝ) (hr : r ∈ C.certificate.finiteNodes) :
      C.certificate.mergedEvenResidue r +
        scale * C.certificate.mergedOddResidue r = 0 := by
    have heval := congrArg (fun P : Polynomial ℝ => P.eval r) hUV
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_zero] at heval
    have hUeval := eval_quinticResiduePolynomial
      (s := C.certificate.finiteNodes) (t := id)
      (z := C.certificate.mergedEvenResidue)
      Function.injective_id.injOn hr
    have hVeval := eval_quinticResiduePolynomial
      (s := C.certificate.finiteNodes) (t := id)
      (z := C.certificate.mergedOddResidue)
      Function.injective_id.injOn hr
    change U.eval r = C.certificate.mergedEvenResidue r *
      ∏ j ∈ C.certificate.finiteNodes.erase r, (r - j) at hUeval
    change V.eval r = C.certificate.mergedOddResidue r *
      ∏ j ∈ C.certificate.finiteNodes.erase r, (r - j) at hVeval
    rw [hUeval, hVeval] at heval
    have hprod :
        (∏ j ∈ C.certificate.finiteNodes.erase r, (r - j)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      exact sub_ne_zero.mpr (Ne.symm (Finset.mem_erase.mp hj).1)
    have hfactored :
        (C.certificate.mergedEvenResidue r +
          scale * C.certificate.mergedOddResidue r) *
            (∏ j ∈ C.certificate.finiteNodes.erase r, (r - j)) = 0 := by
      calc
        _ = C.certificate.mergedEvenResidue r *
              (∏ j ∈ C.certificate.finiteNodes.erase r, (r - j)) +
            scale * (C.certificate.mergedOddResidue r *
              (∏ j ∈ C.certificate.finiteNodes.erase r, (r - j))) := by ring
        _ = 0 := heval
    exact (mul_eq_zero.mp hfactored).resolve_right hprod
  have hkernel (r : ℝ) (hr : r ∈ C.certificate.finiteNodes) :
      (C.certificate.mergedDenominator r).evenPart r +
        scale * r * (C.certificate.mergedDenominator r).oddPart r = 0 := by
    have hres := hresidue r hr
    unfold EndpointMomentCertificate.mergedEvenResidue
      EndpointMomentCertificate.mergedOddResidue at hres
    have hw : C.certificate.mergedFiniteWeight r ≠ 0 :=
      ne_of_gt (C.certificate.mergedFiniteWeight_pos hr)
    have hfactored : C.certificate.mergedFiniteWeight r *
        ((C.certificate.mergedDenominator r).evenPart r +
          scale * r * (C.certificate.mergedDenominator r).oddPart r) = 0 := by
      calc
        _ = C.certificate.mergedFiniteWeight r *
              (C.certificate.mergedDenominator r).evenPart r +
            scale * (C.certificate.mergedFiniteWeight r * r *
              (C.certificate.mergedDenominator r).oddPart r) := by ring
        _ = 0 := hres
    exact (mul_eq_zero.mp hfactored).resolve_left hw
  have hnode : ∀ r ∈ C.certificate.finiteNodes,
      vectorNumeratorEven C.support r = 0 := by
    intro r hr
    have ha := C.certificate.mergedDenominator_hurwitz hsegment hr
    have hnonneg : ∀ t : ℝ, 0 ≤ t →
        0 ≤ (C.certificate.mergedDenominator r).vectorCross C.support t := by
      intro t ht
      rw [C.certificate.mergedDenominator_eq_convex hr]
      exact C.support_cross_nonneg_convex _
        (C.certificate.mergedParameter_mem hr) t ht
    exact vectorNumeratorEven_eq_zero_of_proportional_kernel_zero
      ha hscale hb1pos hprop hnonneg
        (C.certificate.finiteNode_nonneg hr) (hkernel r hr)
  have hsub : C.certificate.finiteNodes ⊆
      (vectorNumeratorEvenPolynomial C.support).roots.toFinset := by
    intro r hr
    rw [Multiset.mem_toFinset, Polynomial.mem_roots
      (C.even_support_component_ne_zero hsegment)]
    simpa using hnode r hr
  have hcard : C.certificate.finiteNodes.card ≤ 2 := by
    calc
      C.certificate.finiteNodes.card ≤
          (vectorNumeratorEvenPolynomial C.support).roots.toFinset.card :=
        Finset.card_le_card hsub
      _ ≤ (vectorNumeratorEvenPolynomial C.support).roots.card :=
        Multiset.toFinset_card_le _
      _ ≤ (vectorNumeratorEvenPolynomial C.support).natDegree :=
        Polynomial.card_roots' _
      _ = 2 := vectorNumeratorEvenPolynomial_natDegree C.support
        (ne_of_gt hb1pos)
  obtain ⟨r, hr⟩ := C.certificate.finiteNodes_nonempty
  have hzEven := residues_zero_of_vanishing_moments
    Function.injective_id.injOn (hcard.trans (by omega))
      C.certificate.mergedEvenResidue_moments r hr
  have hzOdd : C.certificate.mergedOddResidue r = 0 := by
    have hres := hresidue r hr
    exact (mul_eq_zero.mp (by
      show scale * C.certificate.mergedOddResidue r = 0
      linarith)).resolve_left hscale_ne
  have ha := C.certificate.mergedDenominator_hurwitz hsegment hr
  have hEvenZero : (C.certificate.mergedDenominator r).evenPart r = 0 := by
    unfold EndpointMomentCertificate.mergedEvenResidue at hzEven
    exact (mul_eq_zero.mp hzEven).resolve_left
      (ne_of_gt (C.certificate.mergedFiniteWeight_pos hr))
  have hrne : r ≠ 0 := by
    intro hrzero
    subst r
    have hc5 : (C.certificate.mergedDenominator 0).c5 = 0 := by
      simpa [evenPart] using hEvenZero
    exact (ne_of_gt ha.c5_pos) hc5
  have hOddNe : (C.certificate.mergedDenominator r).oddPart r ≠ 0 :=
    oddPart_ne_zero_of_evenPart_zero ha
      (C.certificate.finiteNode_nonneg hr) hEvenZero
  have hOddResidueNe : C.certificate.mergedOddResidue r ≠ 0 := by
    unfold EndpointMomentCertificate.mergedOddResidue
    exact mul_ne_zero
      (mul_ne_zero (ne_of_gt (C.certificate.mergedFiniteWeight_pos hr)) hrne)
      hOddNe
  exact hOddResidueNe hzOdd

/-- 互素情形直接比较次数，不需要先证明至多六个原子。 -/
lemma CriticalEndpointMomentCertificate.false_of_support_coprime
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (hsegment : p.allConvexHurwitz q)
    (hcop : IsCoprime (vectorNumeratorEvenPolynomial C.support)
      (vectorNumeratorOddPolynomial C.support)) : False := by
  have hb1 := ne_of_gt (C.support_one_pos hsegment)
  have hE : vectorNumeratorEvenPolynomial C.support ≠ 0 := by
    intro hz
    have hd := vectorNumeratorEvenPolynomial_natDegree C.support hb1
    rw [hz, Polynomial.natDegree_zero] at hd
    omega
  obtain ⟨Q, hV, _⟩ := coprime_quintic_contact_multiplier hcop hE C.interpolation_identity
  have hVne := C.oddInterpolationPolynomial_ne_zero hsegment
  have hQne : Q ≠ 0 := by
    intro hz
    apply hVne
    simp [hV, hz]
  have hdegree : 2 ≤ C.certificate.oddInterpolationPolynomial.natDegree := by
    rw [hV, Polynomial.natDegree_mul hE hQne, vectorNumeratorEvenPolynomial_natDegree C.support hb1]
    omega
  by_cases hinfinity : C.certificate.mergedInfinityWeight = 0
  · have hgap := C.certificate.oddInterpolation_natDegree_add_three_lt_card hVne hinfinity
    have hbudget := C.finiteNodes_card_le_five_by_contacts hsegment
    omega
  · have hb0 : C.support 0 = 0 := (mul_eq_zero.mp C.infinity_contact).resolve_left hinfinity
    have hgap := C.certificate.oddInterpolation_natDegree_add_two_lt_card hVne
    have hbudget := C.finiteNodes_card_le_four_of_support_zero hsegment hb0
    omega

lemma CriticalEndpointMomentCertificate.support_not_coprime
    {p q : MonicQuinticCoeff} (C : CriticalEndpointMomentCertificate p q)
    (hsegment : p.allConvexHurwitz q) :
    ¬ IsCoprime
      (vectorNumeratorEvenPolynomial C.support)
      (vectorNumeratorOddPolynomial C.support) := by
  intro hcop
  exact C.false_of_support_coprime hsegment hcop

/-! ## 5. 用连续 max-min 直接取得临界证书 -/

private def combinationsOfLength
    {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E) (n : ℕ) : Set E :=
  (fun wz : (Fin n → ℝ) × (Fin n → E) => ∑ i : Fin n, wz.1 i • wz.2 i) ''
    (stdSimplex ℝ (Fin n) ×ˢ Set.pi univ (fun _ : Fin n => S))

private theorem combinationsOfLength_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (hS : IsCompact S) (n : ℕ) : IsCompact (combinationsOfLength S n) := by
  have hw : IsCompact (stdSimplex ℝ (Fin n)) := isCompact_stdSimplex (Fin n)
  have hz : IsCompact (Set.pi univ (fun _ : Fin n => S)) :=
    isCompact_univ_pi (fun _ : Fin n => hS)
  apply (hw.prod hz).image
  fun_prop

/-- Finite-dimensional Carathéodory reduction makes the convex hull of a compact
set compact. Lengths 0,...,dim(E)+1 suffice, so a finite union avoids padding. -/
theorem compact_convexHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : Set E) (hS : IsCompact S) : IsCompact (convexHull ℝ S) := by
  classical
  let N := Module.finrank ℝ E+1
  have heq : convexHull ℝ S =
      ⋃ n ∈ Finset.range (N+1), combinationsOfLength S n := by
    ext x
    constructor
    · intro hx
      obtain ⟨ι,hι,z,w,hz,hind,hw,hsum,hcombo⟩ := eq_pos_convex_span_of_mem_convexHull hx
      letI : Fintype ι := hι
      let n := Fintype.card ι
      let e : ι ≃ Fin n := Fintype.equivFin ι
      have hn : n ≤ N := hind.card_le_finrank_succ.trans
        (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      apply Set.mem_iUnion.mpr
      refine ⟨n,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩⟩
      refine ⟨((fun i => w (e.symm i)),(fun i => z (e.symm i))),?_,?_⟩
      · constructor
        · exact ⟨fun i => (hw (e.symm i)).le,(e.symm.sum_comp w).trans hsum⟩
        · intro i _
          exact hz ⟨e.symm i,rfl⟩
      · exact (e.symm.sum_comp (fun i => w i • z i)).trans hcombo
    · intro hx
      obtain ⟨n,hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨_,hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨⟨w,z⟩,⟨hw,hz⟩,rfl⟩ := hx
      exact mem_convexHull_of_exists_fintype w z hw.1 hw.2
        (fun i => hz i (mem_univ i)) rfl
  rw [heq]
  exact (Finset.range (N+1)).isCompact_biUnion
    (fun n _ => combinationsOfLength_compact S hS n)

theorem closedConvexHull_eq_convexHull_of_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : Set E) (hS : IsCompact S) : closedConvexHull ℝ S = convexHull ℝ S := by
  rw [closedConvexHull_eq_closure_convexHull,(compact_convexHull S hS).isClosed.closure_eq]

theorem balance_forces_contacts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (z : ι → E) (w : ι → ℝ) (f : E →L[ℝ] ℝ)
    (hw : ∀ i, 0 < w i) (hbalance : ∑ i, w i • z i = 0)
    (hsupport : ∀ i, 0 ≤ f (z i)) : ∀ i, f (z i) = 0 := by
  classical
  have hsum : (∑ i, w i*f (z i)) = 0 := by
    have h := congrArg f hbalance
    simpa only [map_sum,map_smul,map_zero,smul_eq_mul] using h
  have hnonneg (i : ι) : 0 ≤ w i*f (z i) := mul_nonneg (hw i).le (hsupport i)
  intro i
  have hzero : w i*f (z i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hsum i (Finset.mem_univ i)
  exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt (hw i))

theorem weak_support_at_transition
    {V K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
    [TopologicalSpace K] (S : Set K) (hS : IsCompact S) (hne : S.Nonempty)
    (B : ℝ → V → K → ℝ)
    (hB : Continuous (fun tvk : (ℝ × V) × K => B tvk.1.1 tvk.1.2 tvk.2))
    (hscale : ∀ t r v k, B t (r • v) k = r*B t v k)
    (hstart : ∃ v : V, ∀ k ∈ S, 0 < B 0 v k)
    (hfinish : ¬ ∃ v : V, ∀ k ∈ S, 0 < B 1 v k) :
    ∃ t ∈ Icc (0 : ℝ) 1, ∃ v : V, ‖v‖ = 1 ∧
      (∀ k ∈ S, 0 ≤ B t v k) ∧ ¬ ∃ w : V, ∀ k ∈ S, 0 < B t w k := by
  let sphere : Set V := Metric.sphere 0 1
  have hsphere : IsCompact sphere := isCompact_sphere 0 1
  have hzero (t : ℝ) (k : K) : B t 0 k = 0 := by
    simpa using hscale t 0 (0 : V) k
  have hnormalize (t : ℝ) (v : V) (hv : ∀ k ∈ S, 0 < B t v k) :
      ∃ u ∈ sphere, ∀ k ∈ S, 0 < B t u k := by
    have hvne : v ≠ 0 := by
      intro hz
      obtain ⟨k,hk⟩ := hne
      have hp := hv k hk
      simp [hz,hzero] at hp
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    refine ⟨‖v‖⁻¹ • v,?_,?_⟩
    · change dist (‖v‖⁻¹ • v) (0 : V) = 1
      rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hvnorm)]
      exact inv_mul_cancel₀ (ne_of_gt hvnorm)
    · intro k hk
      rw [hscale]
      exact mul_pos (inv_pos.mpr hvnorm) (hv k hk)
  have hsphere_ne : sphere.Nonempty := by
    obtain ⟨v,hv⟩ := hstart
    obtain ⟨u,hu,_⟩ := hnormalize 0 v hv
    exact ⟨u,hu⟩
  let margin : ℝ → V → ℝ := fun t v => sInf ((fun k => B t v k) '' S)
  have hmargin : Continuous (fun tv : ℝ × V => margin tv.1 tv.2) :=
    hS.continuous_sInf hB
  let quality : ℝ → ℝ := fun t => sSup (margin t '' sphere)
  have hquality : Continuous quality := hsphere.continuous_sSup hmargin
  have hmin (t : ℝ) (v : V) : ∃ k ∈ S,
      margin t v = B t v k ∧ ∀ j ∈ S, B t v k ≤ B t v j := by
    apply hS.exists_sInf_image_eq_and_le hne
    exact (hB.comp ((continuous_const.prodMk continuous_const).prodMk continuous_id)).continuousOn
  have hmax (t : ℝ) : ∃ v ∈ sphere,
      quality t = margin t v ∧ ∀ u ∈ sphere, margin t u ≤ margin t v := by
    apply hsphere.exists_sSup_image_eq_and_ge hsphere_ne
    exact (hmargin.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hpositive_iff (t : ℝ) :
      0 < quality t ↔ ∃ v : V, ∀ k ∈ S, 0 < B t v k := by
    constructor
    · intro ht
      obtain ⟨v,_,hv,_⟩ := hmax t
      obtain ⟨k,hk,hkval,hkle⟩ := hmin t v
      refine ⟨v,fun j hj => ?_⟩
      rw [hv,hkval] at ht
      exact ht.trans_le (hkle j hj)
    · rintro ⟨v,hv⟩
      obtain ⟨u,hu,huPos⟩ := hnormalize t v hv
      obtain ⟨k,hk,hkval,_⟩ := hmin t u
      have hmarginpos : 0 < margin t u := by rw [hkval]; exact huPos k hk
      obtain ⟨vmax,_,heq,hupper⟩ := hmax t
      rw [heq]
      exact hmarginpos.trans_le (hupper u hu)
  have hq0 : 0 < quality 0 := (hpositive_iff 0).mpr hstart
  have hq1 : quality 1 ≤ 0 := le_of_not_gt (fun h => hfinish ((hpositive_iff 1).mp h))
  obtain ⟨t,ht,heq⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
    hquality.continuousOn (show 0 ∈ Icc (quality 1) (quality 0) from ⟨hq1,hq0.le⟩)
  obtain ⟨v,hv,hval,_⟩ := hmax t
  refine ⟨t,ht,v,?_,?_,?_⟩
  · simpa [sphere,Metric.mem_sphere,dist_zero_right] using hv
  · obtain ⟨k,hk,hkval,hkle⟩ := hmin t v
    have hzeroVal : B t v k = 0 := by rw [← hkval,← hval]; exact heq
    intro j hj
    simpa [hzeroVal] using hkle j hj
  · intro h
    have hp := (hpositive_iff t).mpr h
    simp [heq] at hp

private def testDomain : Set (ℝ × ℝ) := ({0, 1} : Set ℝ) ×ˢ Icc (0 : ℝ) 1

private def supportTest (p q : MonicQuinticCoeff) (t : ℝ)
    (v : QuinticNumeratorVector) (sx : ℝ × ℝ) : ℝ :=
  quinticDot v ((p.convex q (sx.1 * t)).compactQuinticFeature sx.2)

private lemma supportTest_continuous (p q : MonicQuinticCoeff) :
    Continuous (fun tvx : (ℝ × QuinticNumeratorVector) × (ℝ × ℝ) =>
      supportTest p q tvx.1.1 tvx.1.2 tvx.2) := by
  have hF : Continuous (fun tvx : (ℝ × QuinticNumeratorVector) × (ℝ × ℝ) =>
      (p.convex q (tvx.2.1 * tvx.1.1)).compactQuinticFeature tvx.2.2) :=
    (continuous_compactQuinticFeature_convex p q).comp
      (show Continuous (fun tvx : (ℝ × QuinticNumeratorVector) × (ℝ × ℝ) =>
        (tvx.2.1 * tvx.1.1, tvx.2.2)) by fun_prop)
  simp only [supportTest, quinticDot]
  apply continuous_finset_sum
  intro i _
  exact ((continuous_apply i).comp (continuous_snd.comp continuous_fst)).mul
    ((continuous_apply i).comp hF)

private lemma supportTest_positive_iff (p q : MonicQuinticCoeff)
    (t : ℝ) (v : QuinticNumeratorVector) :
    (∀ sx ∈ testDomain, 0 < supportTest p q t v sx) ↔
      (∀ x ∈ Icc (0 : ℝ) 1, 0 < quinticDot v (p.compactQuinticFeature x)) ∧
      (∀ x ∈ Icc (0 : ℝ) 1,
        0 < quinticDot v ((p.convex q t).compactQuinticFeature x)) := by
  constructor
  · intro h
    constructor
    · intro x hx
      simpa [supportTest] using h (0, x) ⟨by simp, hx⟩
    · intro x hx
      simpa [supportTest] using h (1, x) ⟨by simp, hx⟩
  · rintro ⟨hP, hQ⟩ ⟨s, x⟩ ⟨hs, hx⟩
    rcases (show s = 0 ∨ s = 1 by simpa using hs) with rfl | rfl
    · simpa [supportTest] using hP x hx
    · simpa [supportTest] using hQ x hx

/-- 连续 max-min 为零的位置直接提供非零弱支撑及有限平衡证书。 -/
theorem critical_certificate_of_failed_segment {p q : MonicQuinticCoeff}
    (hsegment : p.allConvexHurwitz q) (hno : ¬ p.ExistsCommonMonicSPR5 q) :
    ∃ t ∈ Icc (0 : ℝ) 1, Nonempty (CriticalEndpointMomentCertificate p (p.convex q t)) := by
  have hp := allConvexHurwitz_left hsegment
  have hq := allConvexHurwitz_right hsegment
  have hS : IsCompact testDomain := (isCompact_singleton.insert (0 : ℝ)).prod isCompact_Icc
  have hSne : testDomain.Nonempty := ⟨(0, 0), by simp [testDomain]⟩
  have hscale : ∀ t r v sx, supportTest p q t (r • v) sx = r * supportTest p q t v sx := by
    intros
    simp only [supportTest, quinticDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hself : ∀ x ∈ Icc (0 : ℝ) 1,
      0 < quinticDot p.monicNumeratorVector (p.compactQuinticFeature x) := by
    apply (compactQuinticPairing_pos_iff p p.monicNumeratorVector).mpr
    refine ⟨by simp, ?_⟩
    intro t ht
    rw [vectorCross_monic]
    exact perturbCross_self_pos hp ht
  have hstart : ∃ v, ∀ sx ∈ testDomain, 0 < supportTest p q 0 v sx := by
    refine ⟨p.monicNumeratorVector, ?_⟩
    apply (supportTest_positive_iff p q 0 _).mpr
    simpa using And.intro hself hself
  have hfinish : ¬ ∃ v, ∀ sx ∈ testDomain, 0 < supportTest p q 1 v sx := by
    rintro ⟨v, hv⟩
    obtain ⟨hP, hQ⟩ := (supportTest_positive_iff p q 1 v).mp hv
    obtain ⟨hv0, hPc⟩ := (compactQuinticPairing_pos_iff p v).mp hP
    have hQc := ((compactQuinticPairing_pos_iff q v).mp (by simpa using hQ)).2
    apply hno
    apply existsCommonMonicSPR5_iff_cross_positive.mpr
    refine ⟨hp, hq, normalizedNumeratorVector v, fun t ht => ?_⟩
    rw [perturbCross_normalizedNumeratorVector p v (ne_of_gt hv0),
      perturbCross_normalizedNumeratorVector q v (ne_of_gt hv0)]
    exact ⟨div_pos (hPc t ht) hv0, div_pos (hQc t ht) hv0⟩
  obtain ⟨t, ht, v, hvnorm, hsupport, hfailed⟩ := weak_support_at_transition
    testDomain hS hSne (supportTest p q) (supportTest_continuous p q) hscale hstart hfinish
  have hzero : (0 : QuinticNumeratorVector) ∈
      closedConvexHull ℝ (p.endpointQuinticFeatureSet (p.convex q t)) := by
    by_contra hz
    obtain ⟨w, hw0, hwP, hwQ⟩ := (endpoint_cross_separator_iff p (p.convex q t)).mpr hz
    apply hfailed
    refine ⟨w, (supportTest_positive_iff p q t w).mpr ?_⟩
    exact ⟨(compactQuinticPairing_pos_iff p w).mpr ⟨hw0, hwP⟩,
      (compactQuinticPairing_pos_iff (p.convex q t) w).mpr ⟨hw0, hwQ⟩⟩
  rw [closedConvexHull_eq_convexHull_of_compact _
    (compact_endpointQuinticFeatureSet p (p.convex q t))] at hzero
  obtain ⟨ι, hι, z, w, hz, _, hw, hsum, hbalance⟩ := eq_pos_convex_span_of_mem_convexHull hzero
  letI : Fintype ι := hι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hpoints (i : Fin (Fintype.card ι)) :=
    mem_endpointQuinticFeatureSet_iff.mp (hz ⟨e.symm i, rfl⟩)
  choose right x hx heq using hpoints
  have hnonneg : ∀ right : Bool, ∀ x ∈ Icc (0 : ℝ) 1,
      0 ≤ quinticDot v ((p.selectedEndpoint (p.convex q t) right).compactQuinticFeature x) := by
    intro right x hx
    cases right
    · simpa [supportTest, selectedEndpoint] using hsupport (0, x) ⟨by simp, hx⟩
    · simpa [supportTest, selectedEndpoint] using hsupport (1, x) ⟨by simp, hx⟩
  have hnonneg_atoms (i : ι) : 0 ≤ quinticDotCLM v (z i) := by
    obtain ⟨side, u, hu, he⟩ := mem_endpointQuinticFeatureSet_iff.mp (hz ⟨i, rfl⟩)
    rw [he, quinticDotCLM_apply]
    exact hnonneg side u hu
  have hcontacts := balance_forces_contacts z w (quinticDotCLM v) hw hbalance hnonneg_atoms
  refine ⟨t, ht, ⟨{
    certificate := {
      atomCount := Fintype.card ι
      rightEndpoint := right
      compactFrequency := x
      weight := fun i => w (e.symm i)
      frequency_mem := hx
      weight_pos := fun i => hw (e.symm i)
      weight_sum := (e.symm.sum_comp w).trans hsum
      balance := ?_ }
    support := v
    support_ne := by
      intro hv
      rw [hv] at hvnorm
      norm_num at hvnorm
    support_nonneg := hnonneg
    contact := ?_ }⟩⟩
  · simpa only [heq] using (e.symm.sum_comp (fun i => w i • z i)).trans hbalance
  · intro i
    simpa only [quinticDotCLM_apply, heq] using hcontacts (e.symm i)

/-! ## 6. 排除全部临界证书，完成充分性并合并主定理 -/

def QuinticCriticalCertificateExclusion : Prop :=
  ∀ p q : MonicQuinticCoeff, p.allConvexHurwitz q →
    IsEmpty (CriticalEndpointMomentCertificate p q)

theorem quinticCriticalCertificateExclusion :
    QuinticCriticalCertificateExclusion := by
  intro p q hsegment
  refine ⟨?_⟩
  intro C
  have hb1 : C.support 1 ≠ 0 := ne_of_gt (C.support_one_pos hsegment)
  have hncop := C.support_not_coprime hsegment
  by_cases hprop : ∃ scale : ℝ, ∀ t : ℝ,
      vectorNumeratorOdd C.support t =
        scale * vectorNumeratorEven C.support t
  · obtain ⟨scale, hscale⟩ := hprop
    exact C.false_of_support_proportional hsegment hscale
  · rcases noncoprime_vectorNumerator_components_cases
      C.support hb1 hncop with hcommon | hproportional
    · obtain ⟨r, hEven, hOddRoot⟩ := hcommon
      exact C.false_of_common_root_nonproportional
        hsegment hEven hOddRoot hprop
    · exact False.elim (hprop hproportional)

/-- 五阶主定理：公共首一五阶 SPR 分子存在，当且仅当整个分母线段 Hurwitz。 -/
theorem fifth_order_main : ∀ p q : MonicQuinticCoeff,
    p.ExistsCommonMonicSPR5 q ↔ p.allConvexHurwitz q := by
  intro p q
  constructor
  · exact allConvexHurwitz_of_common_monicSPR5
  · intro hsegment
    by_contra hno
    obtain ⟨t, ht, ⟨C⟩⟩ := critical_certificate_of_failed_segment hsegment hno
    exact (quinticCriticalCertificateExclusion p (p.convex q t)
      (allConvexHurwitz_initial hsegment ht.1 ht.2)).false C

end

end MonicQuinticCoeff

end MKNumina.SPR.Simplified

#print axioms MKNumina.SPR.Simplified.MonicQuinticCoeff.fifth_order_main
