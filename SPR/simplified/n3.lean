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

/-!
# 三阶线段多项式的精简 SPR 综合证明

本文件独立整理 `SPR/n3.lean` 中主定理所需的证明，只导入 Mathlib。
不调用原文件的结论，也不调用任意阶定理。

设 a(s)=s³+a₁s²+a₂s+a₃，b(s)=s³+b₁s²+b₂s+b₃。
主定理：公共三阶 SPR 分子存在，当且仅当分母线段全部 Hurwitz。
`Hurwitz3Coeff` 沿用原文件的三阶 Routh–Hurwitz 系数条件；
`SPR3For` 沿用原文件的“分母 Hurwitz + 全频率实部严格为正”定义。

充分性只需以下路线：
稳定线段 → 两个开椭圆相交 → 公共二阶分子 q → 三阶分子 a+R*q。
在椭圆内部配方，直接得到频率分子统一正下界，省去椭圆与三角形
区域之间的 TE、ET、TT 分类以及这些分类的条件版本和汇总定理。
必要性独立证明，保留原定理的两个方向和正最高次系数的完整接口。

主要结果：
* `stable_segment_has_common_quadratic`：分母三阶、分子二阶的存在性；
* `n3_paper_main_spr`：首一三阶公共分子的充要条件；
* `paper_n3_full_spr_criterion`：允许任意正最高次系数的完整版本。
以上均位于 `MKNumina.SPR.Simplified` 命名空间，不影响原文件。
-/

namespace MKNumina.SPR.Simplified

noncomputable section
open scoped Real

/-! ## 1. 定义与虚轴上的代数恒等式 -/

def Hurwitz3Coeff (a1 a2 a3 : ℝ) : Prop :=
  0 < a1 ∧ 0 < a2 ∧ 0 < a3 ∧ a3 < a1 * a2

def conicE (a1 a2 a3 x y : ℝ) : ℝ :=
  a2^2 * x^2
  + 2 * (2*a3 - a1*a2) * x * y
  + a1^2 * y^2
  - 2 * a2 * a3 * x
  - 2 * a1 * a3 * y
  + a3^2

def freqNum (a1 a2 a3 x y ω : ℝ) : ℝ :=
  (a1 - x) * ω^4
  + (a2 * x - a1 * y - a3) * ω^2
  + a3 * y

def OmegaE (a1 a2 a3 x y : ℝ) : Prop :=
  conicE a1 a2 a3 x y < 0

def jw (ω : ℝ) : ℂ :=
  Complex.I * (ω : ℂ)

def aEval (a1 a2 a3 ω : ℝ) : ℂ :=
  jw ω ^ 3 + (a1 : ℂ) * jw ω ^ 2 + (a2 : ℂ) * jw ω + (a3 : ℂ)

def cEval (x y ω : ℝ) : ℂ :=
  jw ω ^ 2 + (x : ℂ) * jw ω + (y : ℂ)

lemma aEval_re
    (a1 a2 a3 ω : ℝ) :
    (aEval a1 a2 a3 ω).re = a3 - a1 * ω^2 := by
  norm_num [aEval, jw, pow_two, pow_succ]
  ring

lemma aEval_im
    (a1 a2 a3 ω : ℝ) :
    (aEval a1 a2 a3 ω).im = a2 * ω - ω^3 := by
  norm_num [aEval, jw, pow_two, pow_succ]
  ring

lemma cEval_re
    (x y ω : ℝ) :
    (cEval x y ω).re = y - ω^2 := by
  norm_num [cEval, jw, pow_two]
  ring

lemma cEval_im
    (x y ω : ℝ) :
    (cEval x y ω).im = x * ω := by
  norm_num [cEval, jw, pow_two]

lemma aEval_ne_zero
    {a1 a2 a3 ω : ℝ}
    (h : Hurwitz3Coeff a1 a2 a3) :
    aEval a1 a2 a3 ω ≠ 0 := by
  intro hz
  have hre : (aEval a1 a2 a3 ω).re = 0 := by
    rw [hz]
    simp
  have him : (aEval a1 a2 a3 ω).im = 0 := by
    rw [hz]
    simp
  rw [aEval_re] at hre
  rw [aEval_im] at him
  rcases h with ⟨ha1, ha2, ha3, hhur⟩
  by_cases hω : ω = 0
  · subst ω
    norm_num at hre
    linarith
  · have hfactor : ω * (a2 - ω^2) = 0 := by
      nlinarith
    have hzero : a2 - ω^2 = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left hω
    have hω2 : ω^2 = a2 := by linarith
    have ha3eq : a3 = a1 * a2 := by nlinarith
    nlinarith

lemma aEval_normSq_pos
    {a1 a2 a3 ω : ℝ}
    (h : Hurwitz3Coeff a1 a2 a3) :
    0 < Complex.normSq (aEval a1 a2 a3 ω) := by
  exact Complex.normSq_pos.mpr (aEval_ne_zero h)

lemma complex_div_re_eq
    (z w : ℂ) :
    (z / w).re
      = (z.re * w.re + z.im * w.im) / Complex.normSq w := by
  rw [Complex.div_re]
  ring

lemma re_numerator_eq_freqNum
    (a1 a2 a3 x y ω : ℝ) :
    (y - ω^2) * (a3 - a1 * ω^2)
      + (x * ω) * (a2 * ω - ω^3)
      = freqNum a1 a2 a3 x y ω := by
  unfold freqNum
  ring

lemma re_c_div_a_eq
    {a1 a2 a3 x y ω : ℝ} :
    ((cEval x y ω) / (aEval a1 a2 a3 ω)).re
      = freqNum a1 a2 a3 x y ω
          / Complex.normSq (aEval a1 a2 a3 ω) := by
  rw [complex_div_re_eq]
  rw [cEval_re, aEval_re, cEval_im, aEval_im]
  rw [re_numerator_eq_freqNum]

def RePosFor
    (a1 a2 a3 x y : ℝ) : Prop :=
  ∀ ω : ℝ,
    0 < ((cEval x y ω) / (aEval a1 a2 a3 ω)).re

def ExistsCommonRePos
    (a1 a2 a3 b1 b2 b3 : ℝ) : Prop :=
  ∃ x y : ℝ,
    RePosFor a1 a2 a3 x y ∧
    RePosFor b1 b2 b3 x y

def Intersects
    (S T : ℝ → ℝ → Prop) : Prop :=
  ∃ x y : ℝ, S x y ∧ T x y

def EllipseIntersects
    (a1 a2 a3 b1 b2 b3 : ℝ) : Prop :=
  Intersects
    (OmegaE a1 a2 a3)
    (OmegaE b1 b2 b3)

lemma Hurwitz3Coeff.a1_pos
    {a1 a2 a3 : ℝ}
    (h : Hurwitz3Coeff a1 a2 a3) :
    0 < a1 := by
  exact h.1

lemma Hurwitz3Coeff.a2_pos
    {a1 a2 a3 : ℝ}
    (h : Hurwitz3Coeff a1 a2 a3) :
    0 < a2 := by
  exact h.2.1

lemma Hurwitz3Coeff.a3_pos
    {a1 a2 a3 : ℝ}
    (h : Hurwitz3Coeff a1 a2 a3) :
    0 < a3 := by
  exact h.2.2.1

lemma Hurwitz3Coeff.det_pos
    {a1 a2 a3 : ℝ}
    (h : Hurwitz3Coeff a1 a2 a3) :
    0 < a1 * a2 - a3 := by
  rcases h with ⟨ha1, ha2, ha3, hhur⟩
  nlinarith

def ConvexC1 (a1 b1 t : ℝ) : ℝ :=
  t * b1 + (1 - t) * a1

/-- Second coefficient of the convex combination from `a` to `b`. -/
def ConvexC2 (a2 b2 t : ℝ) : ℝ :=
  t * b2 + (1 - t) * a2

/-- Third coefficient of the convex combination from `a` to `b`. -/
def ConvexC3 (a3 b3 t : ℝ) : ℝ :=
  t * b3 + (1 - t) * a3

def AllConvexCombHurwitz3
    (a1 a2 a3 b1 b2 b3 : ℝ) : Prop :=
  ∀ t : ℝ,
    0 ≤ t →
    t ≤ 1 →
    Hurwitz3Coeff
      (ConvexC1 a1 b1 t)
      (ConvexC2 a2 b2 t)
      (ConvexC3 a3 b3 t)

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

def cubicCrossNum
    (p1 p2 p3 q1 q2 q3 t : ℝ) : ℝ :=
  t^3
    + (p1 * q1 - p2 - q2) * t^2
    + (p2 * q2 - p3 * q1 - p1 * q3) * t
    + p3 * q3

lemma cubicCrossNum_comm
    (p1 p2 p3 q1 q2 q3 t : ℝ) :
    cubicCrossNum p1 p2 p3 q1 q2 q3 t
      = cubicCrossNum q1 q2 q3 p1 p2 p3 t := by
  unfold cubicCrossNum
  ring

lemma cubic_re_cross_identity
    (p1 p2 p3 q1 q2 q3 ω : ℝ) :
    (p3 - p1 * ω^2) * (q3 - q1 * ω^2)
      + (p2 * ω - ω^3) * (q2 * ω - ω^3)
      = cubicCrossNum p1 p2 p3 q1 q2 q3 (ω^2) := by
  unfold cubicCrossNum
  ring

lemma re_cubic_div_cubic_eq
    (p1 p2 p3 q1 q2 q3 ω : ℝ) :
    ((aEval p1 p2 p3 ω) / (aEval q1 q2 q3 ω)).re
      = cubicCrossNum p1 p2 p3 q1 q2 q3 (ω^2)
          / Complex.normSq (aEval q1 q2 q3 ω) := by
  rw [complex_div_re_eq]
  rw [aEval_re, aEval_im, aEval_re, aEval_im]
  rw [cubic_re_cross_identity]

/--
Coefficient-level strict positive realness for a quotient of two monic
cubics.  Equal degree and equal positive leading coefficients are built into
the monic representation; denominator analyticity is represented by the
Hurwitz condition.
-/
def SPR3For
    (q1 q2 q3 p1 p2 p3 : ℝ) : Prop :=
  Hurwitz3Coeff q1 q2 q3 ∧
  ∀ ω : ℝ,
    0 < ((aEval p1 p2 p3 ω) / (aEval q1 q2 q3 ω)).re

/-- There is one monic cubic numerator making both quotients SPR. -/
def ExistsCommonSPR3
    (a1 a2 a3 b1 b2 b3 : ℝ) : Prop :=
  ∃ c1 c2 c3 : ℝ,
    SPR3For a1 a2 a3 c1 c2 c3 ∧
    SPR3For b1 b2 b3 c1 c2 c3

lemma SPR3For.re_cross_pos
    {q1 q2 q3 p1 p2 p3 : ℝ}
    (h : SPR3For q1 q2 q3 p1 p2 p3) :
    ∀ ω : ℝ,
      0 < cubicCrossNum p1 p2 p3 q1 q2 q3 (ω^2) := by
  intro ω
  have hre := h.2 ω
  rw [re_cubic_div_cubic_eq] at hre
  have hden : 0 < Complex.normSq (aEval q1 q2 q3 ω) :=
    aEval_normSq_pos h.1
  exact (div_pos_iff_of_pos_right hden).mp hre

/-- The numerator of a monic cubic SPR quotient is itself Hurwitz. -/
theorem SPR3For.numerator_hurwitz
    {q1 q2 q3 p1 p2 p3 : ℝ}
    (h : SPR3For q1 q2 q3 p1 p2 p3) :
    Hurwitz3Coeff p1 p2 p3 := by
  have hq1 : 0 < q1 := Hurwitz3Coeff.a1_pos h.1
  have hq2 : 0 < q2 := Hurwitz3Coeff.a2_pos h.1
  have hq3 : 0 < q3 := Hurwitz3Coeff.a3_pos h.1
  have hqdet : 0 < q1 * q2 - q3 := Hurwitz3Coeff.det_pos h.1
  have hp3prod := h.re_cross_pos 0
  simp [cubicCrossNum] at hp3prod
  have hp3 : 0 < p3 := (mul_pos_iff_of_pos_right hq3).mp hp3prod
  let u := Real.sqrt (q3 / q1)
  have huArg : 0 < q3 / q1 := div_pos hq3 hq1
  have hu : 0 < u := by
    unfold u
    exact Real.sqrt_pos.2 huArg
  have huSq : u^2 = q3 / q1 := by
    unfold u
    exact Real.sq_sqrt (le_of_lt huArg)
  have hqRealZero : q3 - q1 * u^2 = 0 := by
    rw [huSq]
    field_simp [ne_of_gt hq1]
  have hqImagFactor : 0 < q2 - u^2 := by
    rw [huSq]
    apply (sub_pos.mpr)
    exact (div_lt_iff₀ hq1).2 (by nlinarith)
  have huCross := h.re_cross_pos u
  have huIdentity :
      cubicCrossNum p1 p2 p3 q1 q2 q3 (u^2)
        = u^2 * (p2 - u^2) * (q2 - u^2) := by
    rw [← cubic_re_cross_identity]
    rw [hqRealZero]
    ring
  rw [huIdentity] at huCross
  have huSqPos : 0 < u^2 := sq_pos_of_pos hu
  have hp2Factor : 0 < p2 - u^2 := by
    have hrest : 0 < (p2 - u^2) * (q2 - u^2) :=
      (mul_pos_iff_of_pos_left huSqPos).mp (by
        simpa [mul_assoc] using huCross)
    exact (mul_pos_iff_of_pos_right hqImagFactor).mp hrest
  have hp2 : 0 < p2 := by nlinarith [sq_nonneg u]
  let v := Real.sqrt p2
  have hv : 0 < v := by
    unfold v
    exact Real.sqrt_pos.2 hp2
  have hvSq : v^2 = p2 := by
    unfold v
    exact Real.sq_sqrt (le_of_lt hp2)
  have hpImagZero : p2 * v - v^3 = 0 := by
    nlinarith
  have hqRealNeg : q3 - q1 * v^2 < 0 := by
    rw [hvSq]
    have hp2gt : q3 / q1 < p2 := by
      rw [← huSq]
      linarith
    exact sub_neg.mpr (by
      simpa [mul_comm] using ((div_lt_iff₀ hq1).1 hp2gt))
  have hvCross := h.re_cross_pos v
  have hvIdentity :
      cubicCrossNum p1 p2 p3 q1 q2 q3 (v^2)
        = (p3 - p1 * v^2) * (q3 - q1 * v^2) := by
    rw [← cubic_re_cross_identity]
    rw [hpImagZero]
    ring
  rw [hvIdentity] at hvCross
  have hpRealNeg : p3 - p1 * v^2 < 0 := by
    rcases (mul_pos_iff.mp hvCross) with hpos | hneg
    · exact False.elim ((not_lt_of_ge (le_of_lt hpos.2)) hqRealNeg)
    · exact hneg.1
  have hpdet : p3 < p1 * p2 := by
    rw [hvSq] at hpRealNeg
    linarith
  have hp1 : 0 < p1 := by
    by_cases hp1pos : 0 < p1
    · exact hp1pos
    · have hp1nonpos : p1 ≤ 0 := le_of_not_gt hp1pos
      have hprod : p1 * p2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hp1nonpos (le_of_lt hp2)
      linarith
  exact ⟨hp1, hp2, hp3, hpdet⟩

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

lemma aEval_convex_coeff_identity
    (a1 a2 a3 b1 b2 b3 t ω : ℝ) :
    aEval
        (ConvexC1 a1 b1 t)
        (ConvexC2 a2 b2 t)
        (ConvexC3 a3 b3 t) ω
      = (t : ℂ) * aEval b1 b2 b3 ω
          + ((1 - t : ℝ) : ℂ) * aEval a1 a2 a3 ω := by
  unfold aEval ConvexC1 ConvexC2 ConvexC3
  push_cast
  ring

lemma re_convex_cubic_div
    {c1 c2 c3 : ℝ}
    (a1 a2 a3 b1 b2 b3 t ω : ℝ) :
    ((aEval
          (ConvexC1 a1 b1 t)
          (ConvexC2 a2 b2 t)
          (ConvexC3 a3 b3 t) ω)
        / aEval c1 c2 c3 ω).re
      = t * ((aEval b1 b2 b3 ω) / aEval c1 c2 c3 ω).re
        + (1 - t) * ((aEval a1 a2 a3 ω) / aEval c1 c2 c3 ω).re := by
  rw [aEval_convex_coeff_identity, add_div]
  rw [mul_div_assoc, mul_div_assoc]
  norm_num

/-- A common monic cubic SPR numerator forces every convex denominator Hurwitz. -/
theorem ExistsCommonSPR3_imp_AllConvexCombHurwitz3
    {a1 a2 a3 b1 b2 b3 : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3)
    (hb : Hurwitz3Coeff b1 b2 b3)
    (hcommon : ExistsCommonSPR3 a1 a2 a3 b1 b2 b3) :
    AllConvexCombHurwitz3 a1 a2 a3 b1 b2 b3 := by
  rcases hcommon with ⟨c1, c2, c3, hca, hcb⟩
  have hc : Hurwitz3Coeff c1 c2 c3 := hca.numerator_hurwitz
  intro t ht0 ht1
  let q1 := ConvexC1 a1 b1 t
  let q2 := ConvexC2 a2 b2 t
  let q3 := ConvexC3 a3 b3 t
  have haInv : ∀ ω : ℝ,
      0 < ((aEval a1 a2 a3 ω) / (aEval c1 c2 c3 ω)).re := by
    intro ω
    exact (complex_div_re_pos_comm
      (aEval_ne_zero hc) (aEval_ne_zero ha)).1 (hca.2 ω)
  have hbInv : ∀ ω : ℝ,
      0 < ((aEval b1 b2 b3 ω) / (aEval c1 c2 c3 ω)).re := by
    intro ω
    exact (complex_div_re_pos_comm
      (aEval_ne_zero hc) (aEval_ne_zero hb)).1 (hcb.2 ω)
  have hqRe : ∀ ω : ℝ,
      0 < ((aEval q1 q2 q3 ω) / (aEval c1 c2 c3 ω)).re := by
    intro ω
    dsimp [q1, q2, q3]
    rw [re_convex_cubic_div]
    exact convexCoeff_pos_of_pos (haInv ω) (hbInv ω) ht0 ht1
  exact (SPR3For.numerator_hurwitz ⟨hc, hqRe⟩)

/-! ## 2. 椭圆内部直接配方：获得全频率统一正下界 -/

/-- 椭圆内部必有 x<a₁；一个配方恒等式即可证明。 -/
lemma conicE_neg_imp_x_lt_a1 {a1 a2 a3 x y : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3) (hE : conicE a1 a2 a3 x y < 0) :
    x < a1 := by
  have hid : a1 ^ 2 * conicE a1 a2 a3 x y =
      (a1 ^ 2 * y + (2 * a3 - a1 * a2) * x - a1 * a3) ^ 2 -
        4 * a3 * (a1 * a2 - a3) * x * (a1 - x) := by
    unfold conicE
    ring
  have hneg := mul_neg_of_pos_of_neg (sq_pos_of_pos ha.a1_pos) hE
  have hprod : 0 < 4 * a3 * (a1 * a2 - a3) * x * (a1 - x) := by
    nlinarith [sq_nonneg (a1 ^ 2 * y + (2 * a3 - a1 * a2) * x - a1 * a3)]
  by_contra hx
  have hxge : a1 ≤ x := le_of_not_gt hx
  have hx0 : 0 ≤ x := le_trans ha.a1_pos.le hxge
  have hK : 0 ≤ 4 * a3 * (a1 * a2 - a3) := by
    exact le_of_lt (mul_pos (mul_pos (by norm_num) ha.a3_pos) ha.det_pos)
  have := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hK hx0) (sub_nonpos.mpr hxge)
  linarith

/-- 配方给出显式下界 m=-conicE/(4*(a₁-x))>0，对所有实频率成立。 -/
lemma ellipse_uniform_lower_bound {a1 a2 a3 x y : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3) (hE : OmegaE a1 a2 a3 x y) :
    ∃ m : ℝ, 0 < m ∧ ∀ ω : ℝ, m ≤ freqNum a1 a2 a3 x y ω := by
  have hA : 0 < a1 - x := sub_pos.mpr (conicE_neg_imp_x_lt_a1 ha hE)
  have hden : 0 < 4 * (a1 - x) := by positivity
  let m := -conicE a1 a2 a3 x y / (4 * (a1 - x))
  have hm : 0 < m := div_pos (neg_pos.mpr hE) hden
  refine ⟨m, hm, fun ω => ?_⟩
  have hmul : 4 * (a1 - x) * m = -conicE a1 a2 a3 x y := by
    dsimp [m]
    field_simp
    ring
  have hid : 4 * (a1 - x) * freqNum a1 a2 a3 x y ω =
      (2 * (a1 - x) * ω ^ 2 + (a2 * x - a1 * y - a3)) ^ 2 -
        conicE a1 a2 a3 x y := by
    unfold freqNum conicE
    ring
  nlinarith [sq_nonneg (2 * (a1 - x) * ω ^ 2 + (a2 * x - a1 * y - a3))]

lemma ellipse_implies_repos {a1 a2 a3 x y : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3) (hE : OmegaE a1 a2 a3 x y) :
    RePosFor a1 a2 a3 x y := by
  obtain ⟨m, hm, hlower⟩ := ellipse_uniform_lower_bound ha hE
  intro ω
  rw [re_c_div_a_eq]
  exact div_pos (lt_of_lt_of_le hm (hlower ω)) (aEval_normSq_pos ha)

/-! ## 3. 稳定线段迫使两个椭圆相交 -/

def CubicPrimalQuadratic
    (a1 a2 a3 X Y : ℝ) : ℝ :=
  a2 ^ 2 * X ^ 2 +
    2 * (2 * a3 - a1 * a2) * X * Y +
    a1 ^ 2 * Y ^ 2

/-- Dual quadratic form controlling supporting lines of the ellipse. -/
def CubicDualQuadratic
    (a1 a2 a3 A B : ℝ) : ℝ :=
  a1 ^ 2 * A ^ 2 -
    2 * (2 * a3 - a1 * a2) * A * B +
    a2 ^ 2 * B ^ 2

lemma conicE_centered
    (a1 a2 a3 X Y : ℝ) :
    conicE a1 a2 a3 (a1 / 2 + X) (a2 / 2 + Y) =
      CubicPrimalQuadratic a1 a2 a3 X Y -
        a3 * (a1 * a2 - a3) := by
  unfold conicE CubicPrimalQuadratic
  ring

lemma cubicPrimal_scaled_square
    (a1 a2 a3 X Y : ℝ) :
    a1 ^ 2 * CubicPrimalQuadratic a1 a2 a3 X Y =
      (a1 ^ 2 * Y + (2 * a3 - a1 * a2) * X) ^ 2 +
        4 * a3 * (a1 * a2 - a3) * X ^ 2 := by
  unfold CubicPrimalQuadratic
  ring

lemma cubicDual_scaled_square
    (a1 a2 a3 A B : ℝ) :
    a1 ^ 2 * CubicDualQuadratic a1 a2 a3 A B =
      (a1 ^ 2 * A - (2 * a3 - a1 * a2) * B) ^ 2 +
        4 * a3 * (a1 * a2 - a3) * B ^ 2 := by
  unfold CubicDualQuadratic
  ring

lemma cubicPrimal_nonneg
    {a1 a2 a3 : ℝ} (ha : Hurwitz3Coeff a1 a2 a3)
    (X Y : ℝ) :
    0 ≤ CubicPrimalQuadratic a1 a2 a3 X Y := by
  have hscaled := cubicPrimal_scaled_square a1 a2 a3 X Y
  have hright : 0 ≤
      (a1 ^ 2 * Y + (2 * a3 - a1 * a2) * X) ^ 2 +
        4 * a3 * (a1 * a2 - a3) * X ^ 2 := by
    have hterm : 0 ≤ 4 * a3 * (a1 * a2 - a3) * X ^ 2 :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt ha.a3_pos))
          (le_of_lt ha.det_pos))
        (sq_nonneg X)
    nlinarith [sq_nonneg
      (a1 ^ 2 * Y + (2 * a3 - a1 * a2) * X)]
  have hleft : 0 ≤ a1 ^ 2 * CubicPrimalQuadratic a1 a2 a3 X Y := by
    rw [hscaled]
    exact hright
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos ha.a1_pos)).mp hleft

lemma cubicDual_pos_of_normal_ne_zero
    {a1 a2 a3 A B : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3)
    (hnormal : A ≠ 0 ∨ B ≠ 0) :
    0 < CubicDualQuadratic a1 a2 a3 A B := by
  have hscaled := cubicDual_scaled_square a1 a2 a3 A B
  rcases hnormal with hA | hB
  · by_cases hB0 : B = 0
    · subst B
      unfold CubicDualQuadratic
      norm_num
      exact mul_pos (sq_pos_of_pos ha.a1_pos) (sq_pos_of_ne_zero hA)
    · have hterm : 0 < 4 * a3 * (a1 * a2 - a3) * B ^ 2 := by
        exact mul_pos
          (mul_pos (mul_pos (by norm_num) ha.a3_pos) ha.det_pos)
          (sq_pos_of_ne_zero hB0)
      have hleft : 0 < a1 ^ 2 * CubicDualQuadratic a1 a2 a3 A B := by
        rw [hscaled]
        nlinarith [sq_nonneg
          (a1 ^ 2 * A - (2 * a3 - a1 * a2) * B)]
      exact (mul_pos_iff_of_pos_left (sq_pos_of_pos ha.a1_pos)).mp hleft
  · have hterm : 0 < 4 * a3 * (a1 * a2 - a3) * B ^ 2 := by
      exact mul_pos
        (mul_pos (mul_pos (by norm_num) ha.a3_pos) ha.det_pos)
        (sq_pos_of_ne_zero hB)
    have hleft : 0 < a1 ^ 2 * CubicDualQuadratic a1 a2 a3 A B := by
      rw [hscaled]
      nlinarith [sq_nonneg
        (a1 ^ 2 * A - (2 * a3 - a1 * a2) * B)]
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos ha.a1_pos)).mp hleft

private def cubicSupportX
    (a1 a2 a3 A B : ℝ) : ℝ :=
  a1 ^ 2 * A - (2 * a3 - a1 * a2) * B

private def cubicSupportY
    (a1 a2 a3 A B : ℝ) : ℝ :=
  -(2 * a3 - a1 * a2) * A + a2 ^ 2 * B

private lemma cubicSupport_dot
    (a1 a2 a3 A B : ℝ) :
    A * cubicSupportX a1 a2 a3 A B +
        B * cubicSupportY a1 a2 a3 A B =
      CubicDualQuadratic a1 a2 a3 A B := by
  unfold cubicSupportX cubicSupportY CubicDualQuadratic
  ring

private lemma cubicSupport_primal
    (a1 a2 a3 A B : ℝ) :
    CubicPrimalQuadratic a1 a2 a3
        (cubicSupportX a1 a2 a3 A B)
        (cubicSupportY a1 a2 a3 A B) =
      4 * a3 * (a1 * a2 - a3) *
        CubicDualQuadratic a1 a2 a3 A B := by
  unfold CubicPrimalQuadratic CubicDualQuadratic
  unfold cubicSupportX cubicSupportY
  ring

private def cubicSupportRadius
    (a1 a2 a3 A B : ℝ) : ℝ :=
  Real.sqrt (CubicDualQuadratic a1 a2 a3 A B)

private lemma cubicSupportRadius_pos
    {a1 a2 a3 A B : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3)
    (hnormal : A ≠ 0 ∨ B ≠ 0) :
    0 < cubicSupportRadius a1 a2 a3 A B :=
  Real.sqrt_pos.2 (cubicDual_pos_of_normal_ne_zero ha hnormal)

private lemma cubicSupportRadius_sq
    {a1 a2 a3 A B : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3)
    (hnormal : A ≠ 0 ∨ B ≠ 0) :
    cubicSupportRadius a1 a2 a3 A B ^ 2 =
      CubicDualQuadratic a1 a2 a3 A B :=
  Real.sq_sqrt (le_of_lt (cubicDual_pos_of_normal_ne_zero ha hnormal))

private def cubicSupportPoint
    (a1 a2 a3 A B τ : ℝ) : ℝ × ℝ :=
  (a1 / 2 + τ * cubicSupportX a1 a2 a3 A B /
      (2 * cubicSupportRadius a1 a2 a3 A B),
    a2 / 2 + τ * cubicSupportY a1 a2 a3 A B /
      (2 * cubicSupportRadius a1 a2 a3 A B))

private lemma cubicSupportPoint_conic
    {a1 a2 a3 A B : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3)
    (hnormal : A ≠ 0 ∨ B ≠ 0) (τ : ℝ) :
    conicE a1 a2 a3
        (cubicSupportPoint a1 a2 a3 A B τ).1
        (cubicSupportPoint a1 a2 a3 A B τ).2 =
      a3 * (a1 * a2 - a3) * (τ ^ 2 - 1) := by
  rw [show (cubicSupportPoint a1 a2 a3 A B τ).1 =
      a1 / 2 + τ * cubicSupportX a1 a2 a3 A B /
        (2 * cubicSupportRadius a1 a2 a3 A B) from rfl]
  rw [show (cubicSupportPoint a1 a2 a3 A B τ).2 =
      a2 / 2 + τ * cubicSupportY a1 a2 a3 A B /
        (2 * cubicSupportRadius a1 a2 a3 A B) from rfl]
  rw [conicE_centered]
  have hr := cubicSupportRadius_pos ha hnormal
  have hrsq := cubicSupportRadius_sq ha hnormal
  have hprimal := cubicSupport_primal a1 a2 a3 A B
  have hhom :
      CubicPrimalQuadratic a1 a2 a3
          (τ * cubicSupportX a1 a2 a3 A B /
            (2 * cubicSupportRadius a1 a2 a3 A B))
          (τ * cubicSupportY a1 a2 a3 A B /
            (2 * cubicSupportRadius a1 a2 a3 A B)) =
        τ ^ 2 / (4 * cubicSupportRadius a1 a2 a3 A B ^ 2) *
          CubicPrimalQuadratic a1 a2 a3
            (cubicSupportX a1 a2 a3 A B)
            (cubicSupportY a1 a2 a3 A B) := by
    unfold CubicPrimalQuadratic
    ring
  rw [hhom, hprimal, ← hrsq]
  field_simp [ne_of_gt hr]
  ring

private lemma cubicSupportPoint_dot
    {a1 a2 a3 A B : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3)
    (hnormal : A ≠ 0 ∨ B ≠ 0) (τ : ℝ) :
    A * (cubicSupportPoint a1 a2 a3 A B τ).1 +
        B * (cubicSupportPoint a1 a2 a3 A B τ).2 =
      (a1 * A + a2 * B +
        τ * cubicSupportRadius a1 a2 a3 A B) / 2 := by
  have hr := cubicSupportRadius_pos ha hnormal
  have hrsq := cubicSupportRadius_sq ha hnormal
  have hdot := cubicSupport_dot a1 a2 a3 A B
  dsimp [cubicSupportPoint]
  calc
    A * (a1 / 2 + τ * cubicSupportX a1 a2 a3 A B /
          (2 * cubicSupportRadius a1 a2 a3 A B)) +
        B * (a2 / 2 + τ * cubicSupportY a1 a2 a3 A B /
          (2 * cubicSupportRadius a1 a2 a3 A B)) =
        (a1 * A + a2 * B) / 2 +
          τ / (2 * cubicSupportRadius a1 a2 a3 A B) *
            (A * cubicSupportX a1 a2 a3 A B +
              B * cubicSupportY a1 a2 a3 A B) := by ring
    _ = (a1 * A + a2 * B) / 2 +
          τ * cubicSupportRadius a1 a2 a3 A B / 2 := by
      rw [hdot, ← hrsq]
      field_simp [ne_of_gt hr]
      ring
    _ = (a1 * A + a2 * B +
          τ * cubicSupportRadius a1 a2 a3 A B) / 2 := by ring

private lemma cubicSupportPoint_mem
    {a1 a2 a3 A B τ : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3)
    (hnormal : A ≠ 0 ∨ B ≠ 0)
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    OmegaE a1 a2 a3
      (cubicSupportPoint a1 a2 a3 A B τ).1
      (cubicSupportPoint a1 a2 a3 A B τ).2 := by
  unfold OmegaE
  rw [cubicSupportPoint_conic ha hnormal]
  have hτsq : τ ^ 2 < 1 := by nlinarith
  exact mul_neg_of_pos_of_neg
    (mul_pos ha.a3_pos ha.det_pos) (sub_neg.mpr hτsq)

private lemma affine_bound_of_open_unit
    {c r U : ℝ} (hr : 0 < r)
    (h : ∀ τ : ℝ, 0 ≤ τ → τ < 1 → c + τ * r < U) :
    c + r ≤ U := by
  by_contra hnot
  have hU : U < c + r := lt_of_not_ge hnot
  by_cases hc : U ≤ c
  · have hzero := h 0 (by norm_num) (by norm_num)
    norm_num at hzero
    linarith
  · have hcU : c < U := lt_of_not_ge hc
    let τ : ℝ := (U - c + r) / (2 * r)
    have hτ0 : 0 ≤ τ := by
      dsimp [τ]
      exact le_of_lt (div_pos (by linarith) (by positivity))
    have hτ1 : τ < 1 := by
      dsimp [τ]
      apply (div_lt_iff₀ (by positivity : 0 < 2 * r)).2
      linarith
    have hτ := h τ hτ0 hτ1
    have heq : c + τ * r = (c + r + U) / 2 := by
      dsimp [τ]
      field_simp [ne_of_gt hr]
      ring
    rw [heq] at hτ
    linarith

private lemma cubicSupport_upper_bound
    {a1 a2 a3 A B C : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3)
    (hnormal : A ≠ 0 ∨ B ≠ 0)
    (hhalf : ∀ x y : ℝ,
      OmegaE a1 a2 a3 x y → A * x + B * y < C) :
    (a1 * A + a2 * B + cubicSupportRadius a1 a2 a3 A B) / 2 ≤ C := by
  have hr : 0 < cubicSupportRadius a1 a2 a3 A B / 2 :=
    div_pos (cubicSupportRadius_pos ha hnormal) (by norm_num)
  have hbound := affine_bound_of_open_unit hr
    (c := (a1 * A + a2 * B) / 2) (U := C)
    (fun τ hτ0 hτ1 => by
      have hmem := cubicSupportPoint_mem ha hnormal hτ0 hτ1
      have hsep := hhalf _ _ hmem
      rw [cubicSupportPoint_dot ha hnormal] at hsep
      convert hsep using 1; ring)
  convert hbound using 1; ring

private lemma cubicSupport_lower_bound
    {a1 a2 a3 A B C : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3)
    (hnormal : A ≠ 0 ∨ B ≠ 0)
    (hhalf : ∀ x y : ℝ,
      OmegaE a1 a2 a3 x y → C < A * x + B * y) :
    C ≤ (a1 * A + a2 * B - cubicSupportRadius a1 a2 a3 A B) / 2 := by
  have hnormneg : -A ≠ 0 ∨ -B ≠ 0 := by
    rcases hnormal with hA | hB
    · exact Or.inl (neg_ne_zero.mpr hA)
    · exact Or.inr (neg_ne_zero.mpr hB)
  have hupper := cubicSupport_upper_bound ha hnormneg
    (A := -A) (B := -B) (C := -C)
    (fun x y hxy => by have := hhalf x y hxy; linarith)
  have hrad : cubicSupportRadius a1 a2 a3 (-A) (-B) =
      cubicSupportRadius a1 a2 a3 A B := by
    unfold cubicSupportRadius CubicDualQuadratic
    congr 1
    ring
  rw [hrad] at hupper
  linarith

lemma conicE_convex_combo
    (a1 a2 a3 x1 y1 x2 y2 α β : ℝ)
    (hαβ : α + β = 1) :
    conicE a1 a2 a3
        (α * x1 + β * x2) (α * y1 + β * y2) =
      α * conicE a1 a2 a3 x1 y1 +
        β * conicE a1 a2 a3 x2 y2 -
        α * β * CubicPrimalQuadratic a1 a2 a3
          (x1 - x2) (y1 - y2) := by
  have hβ : β = 1 - α := by linarith
  subst β
  unfold conicE CubicPrimalQuadratic
  ring

def cubicEllipseSet (a1 a2 a3 : ℝ) : Set (ℝ × ℝ) :=
  {z | OmegaE a1 a2 a3 z.1 z.2}

lemma cubicEllipseSet_nonempty
    {a1 a2 a3 : ℝ} (ha : Hurwitz3Coeff a1 a2 a3) :
    (cubicEllipseSet a1 a2 a3).Nonempty := by
  refine ⟨(a1 / 2, a2 / 2), ?_⟩
  unfold cubicEllipseSet OmegaE
  change conicE a1 a2 a3 (a1 / 2) (a2 / 2) < 0
  have hcenter : conicE a1 a2 a3 (a1 / 2) (a2 / 2) =
      -a3 * (a1 * a2 - a3) := by
    simpa [CubicPrimalQuadratic] using
      (conicE_centered a1 a2 a3 0 0)
  rw [hcenter]
  nlinarith [mul_pos ha.a3_pos ha.det_pos]

lemma cubicEllipseSet_isOpen
    (a1 a2 a3 : ℝ) :
    IsOpen (cubicEllipseSet a1 a2 a3) := by
  have hcont : Continuous
      (fun z : ℝ × ℝ => conicE a1 a2 a3 z.1 z.2) := by
    unfold conicE
    fun_prop
  have hset : cubicEllipseSet a1 a2 a3 =
      (fun z : ℝ × ℝ => conicE a1 a2 a3 z.1 z.2) ⁻¹'
        (Set.Iio (0 : ℝ)) := by
    ext z
    simp [cubicEllipseSet, OmegaE]
  rw [hset]
  exact isOpen_Iio.preimage hcont

lemma cubicEllipseSet_convex
    {a1 a2 a3 : ℝ} (ha : Hurwitz3Coeff a1 a2 a3) :
    Convex ℝ (cubicEllipseSet a1 a2 a3) := by
  rw [convex_iff_forall_pos]
  intro z hz w hw α β hα hβ hαβ
  have hzQ : conicE a1 a2 a3 z.1 z.2 < 0 := hz
  have hwQ : conicE a1 a2 a3 w.1 w.2 < 0 := hw
  have hprimal := cubicPrimal_nonneg ha (z.1 - w.1) (z.2 - w.2)
  have hprod : 0 ≤ α * β *
      CubicPrimalQuadratic a1 a2 a3 (z.1 - w.1) (z.2 - w.2) :=
    mul_nonneg (mul_nonneg (le_of_lt hα) (le_of_lt hβ)) hprimal
  have hweighted : α * conicE a1 a2 a3 z.1 z.2 +
      β * conicE a1 a2 a3 w.1 w.2 < 0 :=
    add_neg (mul_neg_of_pos_of_neg hα hzQ)
      (mul_neg_of_pos_of_neg hβ hwQ)
  change OmegaE a1 a2 a3
    (α * z.1 + β * w.1) (α * z.2 + β * w.2)
  unfold OmegaE
  rw [conicE_convex_combo a1 a2 a3 _ _ _ _ α β hαβ]
  linarith

/-- The separating line used in the sufficient part of the paper's Lemma 6. -/
lemma cubic_separating_line_of_disjoint
    {a1 a2 a3 b1 b2 b3 : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3)
    (hb : Hurwitz3Coeff b1 b2 b3)
    (hdisjoint : ¬ EllipseIntersects a1 a2 a3 b1 b2 b3) :
    ∃ A B C : ℝ,
      (A ≠ 0 ∨ B ≠ 0) ∧
      (∀ x y : ℝ, OmegaE a1 a2 a3 x y → A * x + B * y < C) ∧
      (∀ x y : ℝ, OmegaE b1 b2 b3 x y → C < A * x + B * y) := by
  have hdisj : Disjoint
      (cubicEllipseSet a1 a2 a3) (cubicEllipseSet b1 b2 b3) := by
    rw [Set.disjoint_left]
    intro z hzA hzB
    exact hdisjoint ⟨z.1, z.2, hzA, hzB⟩
  obtain ⟨f, C, hfA, hfB⟩ :=
    geometric_hahn_banach_open_open
      (cubicEllipseSet_convex ha) (cubicEllipseSet_isOpen _ _ _)
      (cubicEllipseSet_convex hb) (cubicEllipseSet_isOpen _ _ _) hdisj
  let A : ℝ := f (1, 0)
  let B : ℝ := f (0, 1)
  have hrepr (x y : ℝ) : f (x, y) = A * x + B * y := by
    have hdecomp : (x, y) =
        x • ((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp [smul_eq_mul]
    rw [hdecomp, map_add, map_smul, map_smul]
    simp [A, B, smul_eq_mul, mul_comm]
  have hnormal : A ≠ 0 ∨ B ≠ 0 := by
    by_contra hnot
    push_neg at hnot
    obtain ⟨za, hza⟩ := cubicEllipseSet_nonempty ha
    obtain ⟨zb, hzb⟩ := cubicEllipseSet_nonempty hb
    have hfa := hfA za hza
    have hfb := hfB zb hzb
    rw [hrepr za.1 za.2, hnot.1, hnot.2] at hfa
    rw [hrepr zb.1 zb.2, hnot.1, hnot.2] at hfb
    norm_num at hfa hfb
    linarith
  refine ⟨A, B, C, hnormal, ?_, ?_⟩
  · intro x y hxy
    have h := hfA (x, y) hxy
    rw [hrepr] at h
    exact h
  · intro x y hxy
    have h := hfB (x, y) hxy
    rw [hrepr] at h
    exact h

lemma cubic_support_gap_of_disjoint
    {a1 a2 a3 b1 b2 b3 : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3)
    (hb : Hurwitz3Coeff b1 b2 b3)
    (hdisjoint : ¬ EllipseIntersects a1 a2 a3 b1 b2 b3) :
    ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧
      cubicSupportRadius a1 a2 a3 A B +
          cubicSupportRadius b1 b2 b3 A B ≤
        (b1 - a1) * A + (b2 - a2) * B := by
  obtain ⟨A, B, C, hnormal, hhalfA, hhalfB⟩ :=
    cubic_separating_line_of_disjoint ha hb hdisjoint
  have hupper := cubicSupport_upper_bound ha hnormal hhalfA
  have hlower := cubicSupport_lower_bound hb hnormal hhalfB
  refine ⟨A, B, hnormal, ?_⟩
  linarith

lemma cubicDual_convex_identity
    (a1 a2 a3 b1 b2 b3 t A B : ℝ) :
    CubicDualQuadratic
        (ConvexC1 a1 b1 t) (ConvexC2 a2 b2 t)
        (ConvexC3 a3 b3 t) A B =
      (1 - t) * CubicDualQuadratic a1 a2 a3 A B +
        t * CubicDualQuadratic b1 b2 b3 A B -
        t * (1 - t) *
          (((b1 - a1) * A + (b2 - a2) * B) ^ 2) := by
  unfold CubicDualQuadratic ConvexC1 ConvexC2 ConvexC3
  ring

theorem no_cubic_support_gap_of_hurwitz_segment
    {a1 a2 a3 b1 b2 b3 A B : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3)
    (hb : Hurwitz3Coeff b1 b2 b3)
    (hsegment : AllConvexCombHurwitz3 a1 a2 a3 b1 b2 b3)
    (hnormal : A ≠ 0 ∨ B ≠ 0)
    (hgap : cubicSupportRadius a1 a2 a3 A B +
        cubicSupportRadius b1 b2 b3 A B ≤
      (b1 - a1) * A + (b2 - a2) * B) : False := by
  let ra := cubicSupportRadius a1 a2 a3 A B
  let rb := cubicSupportRadius b1 b2 b3 A B
  let S := ra + rb
  let D := (b1 - a1) * A + (b2 - a2) * B
  have hra : 0 < ra := cubicSupportRadius_pos ha hnormal
  have hrb : 0 < rb := cubicSupportRadius_pos hb hnormal
  have hS : 0 < S := by dsimp [S]; linarith
  have hSD : S ≤ D := hgap
  have hDsq : S ^ 2 ≤ D ^ 2 := by nlinarith
  let t : ℝ := ra / S
  have ht0 : 0 ≤ t := le_of_lt (div_pos hra hS)
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ hS).2
    dsimp [S]
    linarith
  have hweight : 0 ≤ t * (1 - t) :=
    mul_nonneg ht0 (sub_nonneg.mpr ht1)
  have haQ : ra ^ 2 = CubicDualQuadratic a1 a2 a3 A B :=
    cubicSupportRadius_sq ha hnormal
  have hbQ : rb ^ 2 = CubicDualQuadratic b1 b2 b3 A B :=
    cubicSupportRadius_sq hb hnormal
  have hweighted :
      (1 - t) * CubicDualQuadratic a1 a2 a3 A B +
        t * CubicDualQuadratic b1 b2 b3 A B = ra * rb := by
    rw [← haQ, ← hbQ]
    dsimp [t, S]
    field_simp [ne_of_gt hS]
    ring
  have hweighted2 : t * (1 - t) * S ^ 2 = ra * rb := by
    dsimp [t, S]
    field_simp [ne_of_gt hS]
    ring
  have hmul : t * (1 - t) * S ^ 2 ≤
      t * (1 - t) * D ^ 2 :=
    mul_le_mul_of_nonneg_left hDsq hweight
  have htHurwitz := hsegment t ht0 ht1
  have hpositive : 0 < CubicDualQuadratic
      (ConvexC1 a1 b1 t) (ConvexC2 a2 b2 t)
      (ConvexC3 a3 b3 t) A B :=
    cubicDual_pos_of_normal_ne_zero htHurwitz hnormal
  rw [cubicDual_convex_identity] at hpositive
  dsimp [D] at hmul
  nlinarith

/-- Sufficient direction of Lemma 6, following the paper's separating-line
argument for two disjoint ellipses. -/
theorem AllConvexCombHurwitz3_imp_EllipseIntersects
    {a1 a2 a3 b1 b2 b3 : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3)
    (hb : Hurwitz3Coeff b1 b2 b3)
    (hsegment : AllConvexCombHurwitz3 a1 a2 a3 b1 b2 b3) :
    EllipseIntersects a1 a2 a3 b1 b2 b3 := by
  by_contra hnone
  obtain ⟨A, B, hnormal, hgap⟩ :=
    cubic_support_gap_of_disjoint ha hb hnone
  exact no_cubic_support_gap_of_hurwitz_segment
    ha hb hsegment hnormal hgap

/-! ## 4. 从公共二阶分子直接构造公共三阶分子 -/

/-- 分母保持三阶，公共分子是 q(s)=s²+x*s+y。 -/
theorem stable_segment_has_common_quadratic {a1 a2 a3 b1 b2 b3 : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3) (hb : Hurwitz3Coeff b1 b2 b3)
    (hsegment : AllConvexCombHurwitz3 a1 a2 a3 b1 b2 b3) :
    ExistsCommonRePos a1 a2 a3 b1 b2 b3 := by
  obtain ⟨x, y, hEa, hEb⟩ := AllConvexCombHurwitz3_imp_EllipseIntersects ha hb hsegment
  exact ⟨x, y, ellipse_implies_repos ha hEa, ellipse_implies_repos hb hEb⟩

lemma monic_cubic_uniform_lower_bound
    (A B C : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ t : ℝ, 0 ≤ t → -K < t^3 + A * t^2 + B * t + C := by
  let M := |A| + |B| + |C| + 1
  let K := 4 * |A| * M^2 + 2 * |B| * M + |C| + 1
  have hM : 0 < M := by
    unfold M
    positivity
  have hM1 : 1 ≤ M := by
    unfold M
    nlinarith [abs_nonneg A, abs_nonneg B, abs_nonneg C]
  have hK : 0 < K := by
    unfold K
    positivity
  refine ⟨K, hK, ?_⟩
  intro t ht
  have hAlo : -|A| ≤ A := neg_abs_le A
  have hBlo : -|B| ≤ B := neg_abs_le B
  have hClo : -|C| ≤ C := neg_abs_le C
  by_cases hlarge : 2 * M ≤ t
  · have ht1 : 1 ≤ t := by nlinarith
    have ht2 : 0 ≤ t^2 := sq_nonneg t
    have hAt : -|A| * t^2 ≤ A * t^2 :=
      mul_le_mul_of_nonneg_right hAlo ht2
    have hBt : -|B| * t ≤ B * t :=
      mul_le_mul_of_nonneg_right hBlo ht
    have ht_le_sq : t ≤ t^2 := by nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1)]
    have hsumAbs : |A| + |B| + |C| < M := by
      unfold M
      linarith
    have habc : |A| + |B| + |C| ≤ t / 2 := by nlinarith
    have htCube :
        (|A| + |B| + |C|) * t^2 ≤ t^3 / 2 := by
      have := mul_le_mul_of_nonneg_right habc ht2
      nlinarith
    have hCbound : |C| ≤ |C| * t^2 := by
      have htSq1 : 1 ≤ t^2 := by nlinarith
      nlinarith [mul_nonneg (abs_nonneg C) (sub_nonneg.mpr htSq1)]
    have hBbound : |B| * t ≤ |B| * t^2 :=
      mul_le_mul_of_nonneg_left ht_le_sq (abs_nonneg B)
    have hpolyNonneg : 0 ≤ t^3 + A * t^2 + B * t + C := by
      nlinarith
    exact lt_of_lt_of_le (neg_neg_of_pos hK) hpolyNonneg
  · have htM : t < 2 * M := lt_of_not_ge hlarge
    have ht2 : 0 ≤ t^2 := sq_nonneg t
    have hAt : -|A| * t^2 ≤ A * t^2 :=
      mul_le_mul_of_nonneg_right hAlo ht2
    have hBt : -|B| * t ≤ B * t :=
      mul_le_mul_of_nonneg_right hBlo ht
    have ht2bound : t^2 < 4 * M^2 := by nlinarith
    have hAtBound : -4 * |A| * M^2 ≤ A * t^2 := by
      have hmul :=
        mul_le_mul_of_nonneg_left (le_of_lt ht2bound) (abs_nonneg A)
      nlinarith
    have hBtBound : -2 * |B| * M ≤ B * t := by
      have hmul := mul_le_mul_of_nonneg_left (le_of_lt htM) (abs_nonneg B)
      nlinarith
    have ht3 : 0 ≤ t^3 := by positivity
    unfold K
    nlinarith

lemma cubicCrossNum_uniform_lower_bound
    (p1 p2 p3 q1 q2 q3 : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ t : ℝ, 0 ≤ t →
        -K < cubicCrossNum p1 p2 p3 q1 q2 q3 t := by
  simpa [cubicCrossNum] using
    (monic_cubic_uniform_lower_bound
      (p1 * q1 - p2 - q2)
      (p2 * q2 - p3 * q1 - p1 * q3)
      (p3 * q3))

lemma aEval_add_scaled_cEval
    (a1 a2 a3 x y R ω : ℝ) :
    aEval (a1 + R) (a2 + R * x) (a3 + R * y) ω
      = aEval a1 a2 a3 ω + (R : ℂ) * cEval x y ω := by
  unfold aEval cEval
  push_cast
  ring

lemma re_add_scaled_quadratic_over_self
    {a1 a2 a3 x y R ω : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3) :
    ((aEval (a1 + R) (a2 + R * x) (a3 + R * y) ω)
        / aEval a1 a2 a3 ω).re
      = 1 + R * ((cEval x y ω) / aEval a1 a2 a3 ω).re := by
  rw [aEval_add_scaled_cEval, add_div]
  rw [div_self (aEval_ne_zero ha), mul_div_assoc]
  norm_num

lemma re_add_scaled_quadratic_over_other
    {a1 a2 a3 b1 b2 b3 x y R ω : ℝ} :
    ((aEval (a1 + R) (a2 + R * x) (a3 + R * y) ω)
        / aEval b1 b2 b3 ω).re
      = (cubicCrossNum a1 a2 a3 b1 b2 b3 (ω^2)
          + R * freqNum b1 b2 b3 x y ω)
          / Complex.normSq (aEval b1 b2 b3 ω) := by
  rw [aEval_add_scaled_cEval, add_div, mul_div_assoc]
  norm_num
  rw [re_cubic_div_cubic_eq, re_c_div_a_eq]
  ring

/-- 取足够大的 R>0，使 c=a+R*q 同时适用于两个端点。 -/
theorem common_spr3_of_ellipse_intersects {a1 a2 a3 b1 b2 b3 : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3) (hb : Hurwitz3Coeff b1 b2 b3)
    (hcommon : EllipseIntersects a1 a2 a3 b1 b2 b3) :
    ExistsCommonSPR3 a1 a2 a3 b1 b2 b3 := by
  obtain ⟨x, y, hEa, hEb⟩ := hcommon
  obtain ⟨m, hm, hlower⟩ := ellipse_uniform_lower_bound hb hEb
  obtain ⟨K, hK, hcross⟩ := cubicCrossNum_uniform_lower_bound a1 a2 a3 b1 b2 b3
  let R := (K + 1) / m
  have hR : 0 < R := div_pos (by linarith) hm
  have hRm : R * m = K + 1 := by dsimp [R]; field_simp
  refine ⟨a1 + R, a2 + R * x, a3 + R * y, ⟨ha, ?_⟩, ⟨hb, ?_⟩⟩
  · intro ω
    rw [re_add_scaled_quadratic_over_self ha]
    have := mul_pos hR (ellipse_implies_repos ha hEa ω)
    linarith
  · intro ω
    rw [re_add_scaled_quadratic_over_other]
    apply div_pos _ (aEval_normSq_pos hb)
    have hscaled := mul_le_mul_of_nonneg_left (hlower ω) hR.le
    have hcrossω := hcross (ω ^ 2) (sq_nonneg ω)
    linarith

/-! ## 5. 主定理：必要性与充分性合并 -/

/-- 存在首一三阶公共 SPR 分子，当且仅当整条分母线段 Hurwitz。 -/
theorem n3_paper_main_spr {a1 a2 a3 b1 b2 b3 : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3) (hb : Hurwitz3Coeff b1 b2 b3) :
    ExistsCommonSPR3 a1 a2 a3 b1 b2 b3 ↔
      AllConvexCombHurwitz3 a1 a2 a3 b1 b2 b3 := by
  constructor
  · exact ExistsCommonSPR3_imp_AllConvexCombHurwitz3 ha hb
  · intro hsegment
    exact common_spr3_of_ellipse_intersects ha hb
      (AllConvexCombHurwitz3_imp_EllipseIntersects ha hb hsegment)

/-! ## 6. 保留原文件“任意正最高次系数”的完整三阶接口 -/

def cubicEvalGeneral
    (c0 c1 c2 c3 ω : ℝ) : ℂ :=
  (c0 : ℂ) * jw ω ^ 3
    + (c1 : ℂ) * jw ω ^ 2
    + (c2 : ℂ) * jw ω
    + (c3 : ℂ)

lemma cubicEvalGeneral_normalize
    {c0 c1 c2 c3 ω : ℝ}
    (hc0 : c0 ≠ 0) :
    cubicEvalGeneral c0 c1 c2 c3 ω
      = (c0 : ℂ) * aEval (c1 / c0) (c2 / c0) (c3 / c0) ω := by
  unfold cubicEvalGeneral aEval
  push_cast
  field_simp [hc0]
  ring

lemma cubicEvalGeneral_one
    (c1 c2 c3 ω : ℝ) :
    cubicEvalGeneral 1 c1 c2 c3 ω = aEval c1 c2 c3 ω := by
  unfold cubicEvalGeneral aEval
  norm_num

/--
Strict positive realness for an arbitrary cubic numerator over a monic cubic
denominator.  `0 < c0` states that the numerator really has degree three and
has the positive high-frequency gain forced by SPR.
-/
def SPRCubicFor
    (q1 q2 q3 c0 c1 c2 c3 : ℝ) : Prop :=
  0 < c0 ∧
  Hurwitz3Coeff q1 q2 q3 ∧
  ∀ ω : ℝ,
    0 < ((cubicEvalGeneral c0 c1 c2 c3 ω)
      / aEval q1 q2 q3 ω).re

/-- The paper's literal existence statement for one common cubic SPR numerator. -/
def ExistsCommonSPRCubic
    (a1 a2 a3 b1 b2 b3 : ℝ) : Prop :=
  ∃ c0 c1 c2 c3 : ℝ,
    SPRCubicFor a1 a2 a3 c0 c1 c2 c3 ∧
    SPRCubicFor b1 b2 b3 c0 c1 c2 c3

lemma re_general_cubic_div_eq_scale_normalized
    {q1 q2 q3 c0 c1 c2 c3 ω : ℝ}
    (hc0 : c0 ≠ 0) :
    ((cubicEvalGeneral c0 c1 c2 c3 ω) / aEval q1 q2 q3 ω).re
      = c0 *
        ((aEval (c1 / c0) (c2 / c0) (c3 / c0) ω)
          / aEval q1 q2 q3 ω).re := by
  rw [cubicEvalGeneral_normalize hc0, mul_div_assoc]
  norm_num

theorem existsCommonSPRCubic_iff_monic
    (a1 a2 a3 b1 b2 b3 : ℝ) :
    ExistsCommonSPRCubic a1 a2 a3 b1 b2 b3
      ↔ ExistsCommonSPR3 a1 a2 a3 b1 b2 b3 := by
  constructor
  · rintro ⟨c0, c1, c2, c3, hca, hcb⟩
    have hc0 : c0 ≠ 0 := ne_of_gt hca.1
    refine ⟨c1 / c0, c2 / c0, c3 / c0, ?_, ?_⟩
    · refine ⟨hca.2.1, ?_⟩
      intro ω
      have hscaled := hca.2.2 ω
      rw [re_general_cubic_div_eq_scale_normalized hc0] at hscaled
      exact (mul_pos_iff_of_pos_left hca.1).mp hscaled
    · refine ⟨hcb.2.1, ?_⟩
      intro ω
      have hscaled := hcb.2.2 ω
      rw [re_general_cubic_div_eq_scale_normalized hc0] at hscaled
      exact (mul_pos_iff_of_pos_left hca.1).mp hscaled
  · rintro ⟨c1, c2, c3, hca, hcb⟩
    refine ⟨1, c1, c2, c3, ?_, ?_⟩
    · refine ⟨by norm_num, hca.1, ?_⟩
      intro ω
      rw [cubicEvalGeneral_one]
      exact hca.2 ω
    · refine ⟨by norm_num, hcb.1, ?_⟩
      intro ω
      rw [cubicEvalGeneral_one]
      exact hcb.2 ω

/--
Literal coefficient-level form of the paper's third-order theorem: there is
one genuine degree-three numerator making both quotients strictly positive
real iff the complete convex segment of denominators is Hurwitz.
-/
theorem paper_n3_full_spr_criterion
    {a1 a2 a3 b1 b2 b3 : ℝ}
    (ha : Hurwitz3Coeff a1 a2 a3)
    (hb : Hurwitz3Coeff b1 b2 b3) :
    ExistsCommonSPRCubic a1 a2 a3 b1 b2 b3
      ↔ AllConvexCombHurwitz3 a1 a2 a3 b1 b2 b3 := by
  exact (existsCommonSPRCubic_iff_monic
    a1 a2 a3 b1 b2 b3).trans (n3_paper_main_spr ha hb)

end

end MKNumina.SPR.Simplified

#print axioms MKNumina.SPR.Simplified.stable_segment_has_common_quadratic
#print axioms MKNumina.SPR.Simplified.n3_paper_main_spr
#print axioms MKNumina.SPR.Simplified.paper_n3_full_spr_criterion
