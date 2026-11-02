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
# 四阶线段多项式的精简 SPR 综合证明

只导入 Mathlib，不导入 `SPR.n3`、`SPR.n4` 或任意阶定理。
沿用原文件的四阶 Routh–Hurwitz 系数判据和频率 SPR 定义。

主要简化：
1. 对椭圆方程直接配方，得到基准二次式的统一正下界。
2. 用一个 ε>0 同时补常数项和四次项，直接构造
   c(s)=ε*s⁴+s³+x*s²+y*s+ε。
   不再分别选择常数 z 和四次项系数 r。
3. 保留主定理两个方向，省去条件桥接定理、额外切线证明及特例。

充分性：稳定线段 → 开椭圆相交 → 统一正下界 → 一次同时扰动。
必要性：SPR 商的首一分子 Hurwitz → 倒数实部为正 → 分母凸组合 Hurwitz。
另保留分母四阶、分子三阶的公共分子存在性，以及任意正最高次系数接口。
命名空间为 `MKNumina.SPR.Simplified.MonicQuarticCoeff`。
-/

namespace MKNumina.SPR.Simplified

/-- Coefficients of `s⁴ + c₁ s³ + c₂ s² + c₃ s + c₄`. -/
structure MonicQuarticCoeff where
  c1 : ℝ
  c2 : ℝ
  c3 : ℝ
  c4 : ℝ

namespace MonicQuarticCoeff

noncomputable section

/-! ## 1. 定义与虚轴上的代数恒等式 -/

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

def Hurwitz (p : MonicQuarticCoeff) : Prop :=
  0 < p.c1 ∧ 0 < p.c2 ∧ 0 < p.c3 ∧ 0 < p.c4 ∧
    0 < p.c1 * p.c2 - p.c3 ∧
    0 < p.c1 * p.c2 * p.c3 - p.c3 ^ 2 - p.c1 ^ 2 * p.c4

/-- The coefficientwise convex combination `(1-t)p+tq`. -/
def convex (p q : MonicQuarticCoeff) (t : ℝ) : MonicQuarticCoeff where
  c1 := (1 - t) * p.c1 + t * q.c1
  c2 := (1 - t) * p.c2 + t * q.c2
  c3 := (1 - t) * p.c3 + t * q.c3
  c4 := (1 - t) * p.c4 + t * q.c4

def allConvexHurwitz (p q : MonicQuarticCoeff) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (convex p q t).Hurwitz

/-- The final principal Routh--Hurwitz determinant for a quartic. -/
def hurwitzDet (p : MonicQuarticCoeff) : ℝ :=
  p.c1 * p.c2 * p.c3 - p.c3 ^ 2 - p.c1 ^ 2 * p.c4

lemma Hurwitz.det_pos {p : MonicQuarticCoeff} (hp : p.Hurwitz) :
    0 < p.hurwitzDet := hp.2.2.2.2.2

lemma Hurwitz.of_pos_coeff_and_det {p : MonicQuarticCoeff}
    (h1 : 0 < p.c1) (h2 : 0 < p.c2)
    (h3 : 0 < p.c3) (h4 : 0 < p.c4)
    (hdet : 0 < p.hurwitzDet) : p.Hurwitz := by
  have hright : 0 < p.c1 ^ 2 * p.c4 :=
    mul_pos (sq_pos_of_pos h1) h4
  have hprod : 0 < (p.c1 * p.c2 - p.c3) * p.c3 := by
    dsimp [hurwitzDet] at hdet
    nlinarith
  have hmiddle : 0 < p.c1 * p.c2 - p.c3 :=
    (mul_pos_iff_of_pos_right h3).mp hprod
  exact ⟨h1, h2, h3, h4, hmiddle, hdet⟩

def evalJW (p : MonicQuarticCoeff) (ω : ℝ) : ℂ :=
  jw ω ^ 4 + (p.c1 : ℂ) * jw ω ^ 3 +
    (p.c2 : ℂ) * jw ω ^ 2 + (p.c3 : ℂ) * jw ω + (p.c4 : ℂ)

lemma evalJW_re (p : MonicQuarticCoeff) (ω : ℝ) :
    (p.evalJW ω).re = ω ^ 4 - p.c2 * ω ^ 2 + p.c4 := by
  norm_num [evalJW, jw, pow_two, pow_succ]
  ring

lemma evalJW_im (p : MonicQuarticCoeff) (ω : ℝ) :
    (p.evalJW ω).im = p.c3 * ω - p.c1 * ω ^ 3 := by
  norm_num [evalJW, jw, pow_two, pow_succ]
  ring

/-- The real cubic numerator `s³+x s²+y s+z` at `jω`. -/
def cubicEvalJW (x y z ω : ℝ) : ℂ :=
  jw ω ^ 3 + (x : ℂ) * jw ω ^ 2 + (y : ℂ) * jw ω + (z : ℂ)

lemma cubicEvalJW_re (x y z ω : ℝ) :
    (cubicEvalJW x y z ω).re = z - x * ω ^ 2 := by
  norm_num [cubicEvalJW, jw, pow_two, pow_succ]
  ring

lemma cubicEvalJW_im (x y z ω : ℝ) :
    (cubicEvalJW x y z ω).im = y * ω - ω ^ 3 := by
  norm_num [cubicEvalJW, jw, pow_two, pow_succ]
  ring

/-- Paper's quadratic in `t=ω²`, before adding a constant numerator term. -/
def baseQuadratic (p : MonicQuarticCoeff) (x y t : ℝ) : ℝ :=
  (p.c1 - x) * t ^ 2 + (p.c2 * x - p.c1 * y - p.c3) * t +
    (p.c3 * y - p.c4 * x)

/-- The quartic denominator's even part, expressed in `t=ω²`. -/
def evenPart (p : MonicQuarticCoeff) (t : ℝ) : ℝ :=
  t ^ 2 - p.c2 * t + p.c4

/-- Real numerator after clearing the positive squared denominator. -/
def cubicCross (p : MonicQuarticCoeff) (x y z t : ℝ) : ℝ :=
  t * p.baseQuadratic x y t + z * p.evenPart t

lemma cubicCross_identity (p : MonicQuarticCoeff) (x y z ω : ℝ) :
    (cubicEvalJW x y z ω).re * (p.evalJW ω).re +
      (cubicEvalJW x y z ω).im * (p.evalJW ω).im =
        p.cubicCross x y z (ω ^ 2) := by
  rw [cubicEvalJW_re, cubicEvalJW_im, evalJW_re, evalJW_im]
  unfold cubicCross baseQuadratic evenPart
  ring

/-- The conic equation from Lemma 1. -/
def conic4 (p : MonicQuarticCoeff) (x y : ℝ) : ℝ :=
  (p.c2 ^ 2 - 4 * p.c4) * x ^ 2 +
    2 * (2 * p.c3 - p.c1 * p.c2) * x * y +
    p.c1 ^ 2 * y ^ 2 -
    2 * (p.c2 * p.c3 - 2 * p.c1 * p.c4) * x -
    2 * p.c1 * p.c3 * y + p.c3 ^ 2

lemma conic4_eq_discriminant (p : MonicQuarticCoeff) (x y : ℝ) :
    p.conic4 x y =
      (p.c2 * x - p.c1 * y - p.c3) ^ 2 -
      4 * (p.c1 - x) * (p.c3 * y - p.c4 * x) := by
  unfold conic4
  ring

lemma evalJW_ne_zero {p : MonicQuarticCoeff} (hp : p.Hurwitz) (ω : ℝ) :
    p.evalJW ω ≠ 0 := by
  intro hzero
  have hre : ω ^ 4 - p.c2 * ω ^ 2 + p.c4 = 0 := by
    simpa [evalJW_re] using congrArg Complex.re hzero
  have him : p.c3 * ω - p.c1 * ω ^ 3 = 0 := by
    simpa [evalJW_im] using congrArg Complex.im hzero
  by_cases hω : ω = 0
  · subst ω
    have hc4 : 0 < p.c4 := hp.2.2.2.1
    norm_num at hre
    linarith
  · have himfactor : ω * (p.c3 - p.c1 * ω ^ 2) = 0 := by
      nlinarith [him]
    have hpivot : p.c3 = p.c1 * ω ^ 2 := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp himfactor).resolve_left hω)
    have hdet := hp.2.2.2.2.2
    rw [hpivot] at hdet
    have hscaled := congrArg (fun v : ℝ => p.c1 ^ 2 * v) hre
    nlinarith

lemma evalJW_normSq_pos {p : MonicQuarticCoeff} (hp : p.Hurwitz) (ω : ℝ) :
    0 < Complex.normSq (p.evalJW ω) :=
  Complex.normSq_pos.mpr (evalJW_ne_zero hp ω)

lemma re_cubic_div_quartic (p : MonicQuarticCoeff) (x y z ω : ℝ) :
    ((cubicEvalJW x y z ω) / p.evalJW ω).re =
      p.cubicCross x y z (ω ^ 2) / Complex.normSq (p.evalJW ω) := by
  rw [complex_div_re_eq, cubicCross_identity]

/-- The frequency condition for the strictly proper cubic numerator. -/
def cubicRePos (p : MonicQuarticCoeff) (x y z : ℝ) : Prop :=
  ∀ ω : ℝ, 0 < ((cubicEvalJW x y z ω) / p.evalJW ω).re

lemma cubicRePos_of_cross_pos {p : MonicQuarticCoeff} {x y z : ℝ}
    (hp : p.Hurwitz)
    (hcross : ∀ t : ℝ, 0 ≤ t → 0 < p.cubicCross x y z t) :
    p.cubicRePos x y z := by
  intro ω
  rw [re_cubic_div_quartic]
  exact div_pos (hcross (ω ^ 2) (sq_nonneg ω)) (evalJW_normSq_pos hp ω)

def quarticNumEvalJW (r x y z ω : ℝ) : ℂ :=
  (r : ℂ) * jw ω ^ 4 + cubicEvalJW x y z ω

lemma quarticNumEvalJW_re (r x y z ω : ℝ) :
    (quarticNumEvalJW r x y z ω).re =
      r * ω ^ 4 + z - x * ω ^ 2 := by
  norm_num [quarticNumEvalJW, cubicEvalJW, jw, pow_two, pow_succ]
  ring

lemma quarticNumEvalJW_im (r x y z ω : ℝ) :
    (quarticNumEvalJW r x y z ω).im = y * ω - ω ^ 3 := by
  norm_num [quarticNumEvalJW, cubicEvalJW, jw, pow_two, pow_succ]
  ring

/-- Real cross product for the equal-degree quotient. -/
def quarticCross (p : MonicQuarticCoeff) (r x y z t : ℝ) : ℝ :=
  p.cubicCross x y z t + r * t ^ 2 * p.evenPart t

lemma quarticCross_identity (p : MonicQuarticCoeff) (r x y z ω : ℝ) :
    (quarticNumEvalJW r x y z ω).re * (p.evalJW ω).re +
      (quarticNumEvalJW r x y z ω).im * (p.evalJW ω).im =
        p.quarticCross r x y z (ω ^ 2) := by
  rw [quarticNumEvalJW_re, quarticNumEvalJW_im,
    evalJW_re, evalJW_im]
  unfold quarticCross cubicCross baseQuadratic evenPart
  ring

lemma re_quartic_div_quartic (p : MonicQuarticCoeff) (r x y z ω : ℝ) :
    ((quarticNumEvalJW r x y z ω) / p.evalJW ω).re =
      p.quarticCross r x y z (ω ^ 2) / Complex.normSq (p.evalJW ω) := by
  rw [complex_div_re_eq, quarticCross_identity]

/-- The paper's equal-degree SPR predicate, at coefficient level. -/
def SPR4For (p : MonicQuarticCoeff) (r x y z : ℝ) : Prop :=
  p.Hurwitz ∧ 0 < r ∧
    ∀ ω : ℝ, 0 < ((quarticNumEvalJW r x y z ω) / p.evalJW ω).re

def ExistsCommonSPR4 (p q : MonicQuarticCoeff) : Prop :=
  ∃ r x y z : ℝ, p.SPR4For r x y z ∧ q.SPR4For r x y z

/-- An arbitrary positive-leading quartic numerator can be divided by its
    leading coefficient; this is the resulting monic numerator interface. -/
def MonicSPR4For (p n : MonicQuarticCoeff) : Prop :=
  p.Hurwitz ∧ ∀ ω : ℝ, 0 < ((n.evalJW ω) / p.evalJW ω).re

def ExistsCommonMonicSPR4 (p q : MonicQuarticCoeff) : Prop :=
  ∃ n : MonicQuarticCoeff, p.MonicSPR4For n ∧ q.MonicSPR4For n

/-! ## 2. 直接配方：椭圆内部的基准二次式有统一正下界 -/

lemma conic4_neg_implies_quadratic_signs {p : MonicQuarticCoeff}
    (hp : p.Hurwitz) {x y : ℝ} (hE : p.conic4 x y < 0) :
    x < p.c1 ∧ 0 < p.c3 * y - p.c4 * x := by
  have hid : p.c1 ^ 2 * p.conic4 x y =
      (p.c1 ^ 2 * y + (2 * p.c3 - p.c1 * p.c2) * x - p.c1 * p.c3) ^ 2 -
        4 * p.hurwitzDet * x * (p.c1 - x) := by
    unfold conic4 hurwitzDet
    ring
  have hneg := mul_neg_of_pos_of_neg (sq_pos_of_pos hp.1) hE
  have hprod : 0 < 4 * p.hurwitzDet * x * (p.c1 - x) := by
    nlinarith [sq_nonneg
      (p.c1 ^ 2 * y + (2 * p.c3 - p.c1 * p.c2) * x - p.c1 * p.c3)]
  have hx : x < p.c1 := by
    by_contra hnot
    have hge : p.c1 ≤ x := le_of_not_gt hnot
    have hx0 : 0 ≤ x := le_trans hp.1.le hge
    have hK : 0 ≤ 4 * p.hurwitzDet := mul_nonneg (by norm_num) hp.det_pos.le
    have := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hK hx0) (sub_nonpos.mpr hge)
    linarith
  refine ⟨hx, ?_⟩
  rw [conic4_eq_discriminant] at hE
  have hAC : 0 < (p.c1 - x) * (p.c3 * y - p.c4 * x) := by
    nlinarith [sq_nonneg (p.c2 * x - p.c1 * y - p.c3)]
  exact (mul_pos_iff_of_pos_left (sub_pos.mpr hx)).mp hAC

/-- The algebraic form of the open region used in Lemmas 1--3. -/
def omega4 (p : MonicQuarticCoeff) (x y : ℝ) : Prop :=
  x < p.c1 ∧ 0 < p.c3 * y - p.c4 * x ∧ p.conic4 x y < 0

lemma omega4_iff_conic4_neg {p : MonicQuarticCoeff}
    (hp : p.Hurwitz) (x y : ℝ) :
    p.omega4 x y ↔ p.conic4 x y < 0 := by
  constructor
  · exact fun h => h.2.2
  · intro h
    exact ⟨(conic4_neg_implies_quadratic_signs hp h).1,
      (conic4_neg_implies_quadratic_signs hp h).2, h⟩

/-- 显式下界 m=-conic4/(4*(c₁-x))>0，对所有实数 t 成立。 -/
lemma omega4_baseQuadratic_uniform {p : MonicQuarticCoeff} {x y : ℝ}
    (h : p.omega4 x y) :
    ∃ m : ℝ, 0 < m ∧ ∀ t : ℝ, m ≤ p.baseQuadratic x y t := by
  have hden : 0 < 4 * (p.c1 - x) := mul_pos (by norm_num) (sub_pos.mpr h.1)
  let m := -p.conic4 x y / (4 * (p.c1 - x))
  refine ⟨m, div_pos (neg_pos.mpr h.2.2) hden, fun t => ?_⟩
  have hm : 4 * (p.c1 - x) * m = -p.conic4 x y := by
    dsimp [m]
    field_simp
    ring
  have hid : 4 * (p.c1 - x) * p.baseQuadratic x y t =
      (2 * (p.c1 - x) * t + (p.c2 * x - p.c1 * y - p.c3)) ^ 2 -
        p.conic4 x y := by
    unfold baseQuadratic conic4
    ring
  nlinarith [sq_nonneg (2 * (p.c1 - x) * t + (p.c2 * x - p.c1 * y - p.c3))]

/-! ## 3. 稳定线段迫使两个开椭圆相交 -/

def dualQuadratic (p : MonicQuarticCoeff) (u v : ℝ) : ℝ :=
  p.c1 ^ 2 * v ^ 2 -
    2 * (2 * p.c3 - p.c1 * p.c2) * u * v +
    (p.c2 ^ 2 - 4 * p.c4) * u ^ 2

/-- The center of the conic is `(a₁/2,a₂/2)`, and its value there is
    the negative Hurwitz determinant. -/
lemma conic4_center (p : MonicQuarticCoeff) :
    p.conic4 (p.c1 / 2) (p.c2 / 2) = -p.hurwitzDet := by
  unfold conic4 hurwitzDet
  ring

lemma omega4_center {p : MonicQuarticCoeff} (hp : p.Hurwitz) :
    p.omega4 (p.c1 / 2) (p.c2 / 2) := by
  apply (omega4_iff_conic4_neg hp _ _).2
  rw [conic4_center]
  exact neg_neg_of_pos hp.det_pos

/-- The quadratic part of the conic after translation to its center. -/
def primalQuadratic (p : MonicQuarticCoeff) (X Y : ℝ) : ℝ :=
  (p.c2 ^ 2 - 4 * p.c4) * X ^ 2 +
    2 * (2 * p.c3 - p.c1 * p.c2) * X * Y +
    p.c1 ^ 2 * Y ^ 2

lemma conic4_centered (p : MonicQuarticCoeff) (X Y : ℝ) :
    p.conic4 (p.c1 / 2 + X) (p.c2 / 2 + Y) =
      p.primalQuadratic X Y - p.hurwitzDet := by
  unfold conic4 primalQuadratic hurwitzDet
  ring

lemma primalQuadratic_scaled_square (p : MonicQuarticCoeff) (X Y : ℝ) :
    p.c1 ^ 2 * p.primalQuadratic X Y =
      (p.c1 ^ 2 * Y + (2 * p.c3 - p.c1 * p.c2) * X) ^ 2 +
        4 * p.hurwitzDet * X ^ 2 := by
  unfold primalQuadratic hurwitzDet
  ring

lemma dualQuadratic_scaled_square (p : MonicQuarticCoeff) (u v : ℝ) :
    p.c1 ^ 2 * p.dualQuadratic u v =
      (p.c1 ^ 2 * v - (2 * p.c3 - p.c1 * p.c2) * u) ^ 2 +
        4 * p.hurwitzDet * u ^ 2 := by
  unfold dualQuadratic hurwitzDet
  ring

lemma dualQuadratic_pos_of_u_ne_zero
    {p : MonicQuarticCoeff} (hp : p.Hurwitz)
    {u v : ℝ} (hu : u ≠ 0) :
    0 < p.dualQuadratic u v := by
  have hu2 : 0 < u ^ 2 := sq_pos_of_ne_zero hu
  have hdet : 0 < p.hurwitzDet := hp.det_pos
  have hsquare : 0 ≤
      (p.c1 ^ 2 * v - (2 * p.c3 - p.c1 * p.c2) * u) ^ 2 := sq_nonneg _
  have hscaled : 0 < p.c1 ^ 2 * p.dualQuadratic u v := by
    rw [dualQuadratic_scaled_square]
    nlinarith [mul_pos hdet hu2]
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hp.1)).mp hscaled

lemma dualQuadratic_pos_of_normal_ne_zero
    {p : MonicQuarticCoeff} (hp : p.Hurwitz)
    {A B : ℝ} (hnormal : A ≠ 0 ∨ B ≠ 0) :
    0 < p.dualQuadratic B A := by
  rcases hnormal with hA | hB
  · by_cases hB : B = 0
    · subst B
      unfold dualQuadratic
      norm_num
      exact mul_pos (sq_pos_of_pos hp.1) (sq_pos_of_ne_zero hA)
    · exact dualQuadratic_pos_of_u_ne_zero hp hB
  · exact dualQuadratic_pos_of_u_ne_zero hp hB

private def supportX (p : MonicQuarticCoeff) (A B : ℝ) : ℝ :=
  p.c1 ^ 2 * A - (2 * p.c3 - p.c1 * p.c2) * B

private def supportY (p : MonicQuarticCoeff) (A B : ℝ) : ℝ :=
  -(2 * p.c3 - p.c1 * p.c2) * A +
    (p.c2 ^ 2 - 4 * p.c4) * B

private lemma support_dot (p : MonicQuarticCoeff) (A B : ℝ) :
    A * supportX p A B + B * supportY p A B =
      p.dualQuadratic B A := by
  unfold supportX supportY dualQuadratic
  ring

private lemma support_primal (p : MonicQuarticCoeff) (A B : ℝ) :
    p.primalQuadratic (supportX p A B) (supportY p A B) =
      4 * p.hurwitzDet * p.dualQuadratic B A := by
  unfold primalQuadratic supportX supportY dualQuadratic hurwitzDet
  ring

private def supportRadius (p : MonicQuarticCoeff) (A B : ℝ) : ℝ :=
  Real.sqrt (p.dualQuadratic B A)

private lemma supportRadius_pos {p : MonicQuarticCoeff}
    (hp : p.Hurwitz) {A B : ℝ}
    (hnormal : A ≠ 0 ∨ B ≠ 0) :
    0 < supportRadius p A B :=
  Real.sqrt_pos.2 (dualQuadratic_pos_of_normal_ne_zero hp hnormal)

private lemma supportRadius_sq {p : MonicQuarticCoeff}
    (hp : p.Hurwitz) {A B : ℝ}
    (hnormal : A ≠ 0 ∨ B ≠ 0) :
    supportRadius p A B ^ 2 = p.dualQuadratic B A :=
  Real.sq_sqrt (le_of_lt (dualQuadratic_pos_of_normal_ne_zero hp hnormal))

/-- An interior point approaching the supporting boundary in direction
    `(A,B)` as `τ` approaches one from below. -/
private def supportPoint (p : MonicQuarticCoeff)
    (A B τ : ℝ) : ℝ × ℝ :=
  (p.c1 / 2 + τ * supportX p A B / (2 * supportRadius p A B),
    p.c2 / 2 + τ * supportY p A B / (2 * supportRadius p A B))

private lemma supportPoint_conic
    {p : MonicQuarticCoeff} (hp : p.Hurwitz)
    {A B : ℝ} (hnormal : A ≠ 0 ∨ B ≠ 0) (τ : ℝ) :
    p.conic4 (supportPoint p A B τ).1 (supportPoint p A B τ).2 =
      p.hurwitzDet * (τ ^ 2 - 1) := by
  rw [show (supportPoint p A B τ).1 =
      p.c1 / 2 + τ * supportX p A B / (2 * supportRadius p A B) from rfl]
  rw [show (supportPoint p A B τ).2 =
      p.c2 / 2 + τ * supportY p A B / (2 * supportRadius p A B) from rfl]
  rw [conic4_centered]
  have hr : 0 < supportRadius p A B := supportRadius_pos hp hnormal
  have hrsq := supportRadius_sq hp hnormal
  have hprimal := support_primal p A B
  have hhom :
      p.primalQuadratic
          (τ * supportX p A B / (2 * supportRadius p A B))
          (τ * supportY p A B / (2 * supportRadius p A B)) =
        τ ^ 2 / (4 * supportRadius p A B ^ 2) *
          p.primalQuadratic (supportX p A B) (supportY p A B) := by
    unfold primalQuadratic
    ring
  rw [hhom, hprimal, ← hrsq]
  field_simp [ne_of_gt hr]
  ring

private lemma supportPoint_dot
    {p : MonicQuarticCoeff} (hp : p.Hurwitz)
    {A B : ℝ} (hnormal : A ≠ 0 ∨ B ≠ 0) (τ : ℝ) :
    A * (supportPoint p A B τ).1 + B * (supportPoint p A B τ).2 =
      (p.c1 * A + p.c2 * B + τ * supportRadius p A B) / 2 := by
  have hr : 0 < supportRadius p A B := supportRadius_pos hp hnormal
  have hrsq := supportRadius_sq hp hnormal
  have hdot := support_dot p A B
  dsimp [supportPoint]
  calc
    A * (p.c1 / 2 + τ * supportX p A B / (2 * supportRadius p A B)) +
        B * (p.c2 / 2 + τ * supportY p A B / (2 * supportRadius p A B)) =
        (p.c1 * A + p.c2 * B) / 2 +
          τ / (2 * supportRadius p A B) *
            (A * supportX p A B + B * supportY p A B) := by ring
    _ = (p.c1 * A + p.c2 * B) / 2 +
          τ * supportRadius p A B / 2 := by
      rw [hdot, ← hrsq]
      field_simp [ne_of_gt hr]
      ring
    _ = (p.c1 * A + p.c2 * B + τ * supportRadius p A B) / 2 := by ring

private lemma supportPoint_mem_omega
    {p : MonicQuarticCoeff} (hp : p.Hurwitz)
    {A B : ℝ} (hnormal : A ≠ 0 ∨ B ≠ 0)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    p.omega4 (supportPoint p A B τ).1 (supportPoint p A B τ).2 := by
  apply (omega4_iff_conic4_neg hp _ _).2
  rw [supportPoint_conic hp hnormal]
  have hτsq : τ ^ 2 < 1 := by nlinarith
  exact mul_neg_of_pos_of_neg hp.det_pos (sub_neg.mpr hτsq)

private lemma affine_bound_of_unit_interval
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

/-- Upper support value of an open quartic ellipse in direction `(A,B)`. -/
lemma support_upper_bound_of_halfspace
    {p : MonicQuarticCoeff} (hp : p.Hurwitz)
    {A B C : ℝ} (hnormal : A ≠ 0 ∨ B ≠ 0)
    (hhalf : ∀ x y : ℝ, p.omega4 x y → A * x + B * y < C) :
    (p.c1 * A + p.c2 * B + supportRadius p A B) / 2 ≤ C := by
  have hr : 0 < supportRadius p A B / 2 :=
    div_pos (supportRadius_pos hp hnormal) (by norm_num)
  have hbound := affine_bound_of_unit_interval hr (c := (p.c1 * A + p.c2 * B) / 2)
    (U := C) (fun τ hτ0 hτ1 => by
      have hmem := supportPoint_mem_omega hp hnormal hτ0 hτ1
      have hsep := hhalf _ _ hmem
      rw [supportPoint_dot hp hnormal] at hsep
      convert hsep using 1; ring)
  convert hbound using 1; ring

/-- Lower support value, obtained by reversing the direction. -/
lemma support_lower_bound_of_halfspace
    {p : MonicQuarticCoeff} (hp : p.Hurwitz)
    {A B C : ℝ} (hnormal : A ≠ 0 ∨ B ≠ 0)
    (hhalf : ∀ x y : ℝ, p.omega4 x y → C < A * x + B * y) :
    C ≤ (p.c1 * A + p.c2 * B - supportRadius p A B) / 2 := by
  have hnormneg : -A ≠ 0 ∨ -B ≠ 0 := by
    rcases hnormal with hA | hB
    · exact Or.inl (neg_ne_zero.mpr hA)
    · exact Or.inr (neg_ne_zero.mpr hB)
  have hupper := support_upper_bound_of_halfspace hp hnormneg
    (A := -A) (B := -B) (C := -C)
    (fun x y hxy => by have := hhalf x y hxy; linarith)
  have hrad : supportRadius p (-A) (-B) = supportRadius p A B := by
    unfold supportRadius dualQuadratic
    congr 1
    ring
  rw [hrad] at hupper
  linarith

/-! ## Convexity and separation of the quartic ellipses -/

lemma primalQuadratic_nonneg {p : MonicQuarticCoeff}
    (hp : p.Hurwitz) (X Y : ℝ) :
    0 ≤ p.primalQuadratic X Y := by
  have hscaled := p.primalQuadratic_scaled_square X Y
  have hright : 0 ≤
      (p.c1 ^ 2 * Y + (2 * p.c3 - p.c1 * p.c2) * X) ^ 2 +
        4 * p.hurwitzDet * X ^ 2 := by
    have hterm := mul_nonneg (le_of_lt hp.det_pos) (sq_nonneg X)
    nlinarith [sq_nonneg
      (p.c1 ^ 2 * Y + (2 * p.c3 - p.c1 * p.c2) * X)]
  have hleft : 0 ≤ p.c1 ^ 2 * p.primalQuadratic X Y := by
    rw [hscaled]
    exact hright
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos hp.1)).mp hleft

lemma conic4_convex_combo (p : MonicQuarticCoeff)
    (x₁ y₁ x₂ y₂ a b : ℝ) (hab : a + b = 1) :
    p.conic4 (a * x₁ + b * x₂) (a * y₁ + b * y₂) =
      a * p.conic4 x₁ y₁ + b * p.conic4 x₂ y₂ -
        a * b * p.primalQuadratic (x₁ - x₂) (y₁ - y₂) := by
  have hb : b = 1 - a := by linarith
  subst b
  unfold conic4 primalQuadratic
  ring

def ellipseSet (p : MonicQuarticCoeff) : Set (ℝ × ℝ) :=
  {z | p.omega4 z.1 z.2}

lemma ellipseSet_nonempty {p : MonicQuarticCoeff}
    (hp : p.Hurwitz) : (ellipseSet p).Nonempty :=
  ⟨(p.c1 / 2, p.c2 / 2), omega4_center hp⟩

lemma ellipseSet_isOpen {p : MonicQuarticCoeff}
    (hp : p.Hurwitz) : IsOpen (ellipseSet p) := by
  have hcont : Continuous (fun z : ℝ × ℝ => p.conic4 z.1 z.2) := by
    unfold conic4
    fun_prop
  have hset : ellipseSet p =
      (fun z : ℝ × ℝ => p.conic4 z.1 z.2) ⁻¹' (Set.Iio (0 : ℝ)) := by
    ext z
    simp only [ellipseSet, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio]
    exact omega4_iff_conic4_neg hp z.1 z.2
  rw [hset]
  exact isOpen_Iio.preimage hcont

lemma ellipseSet_convex {p : MonicQuarticCoeff}
    (hp : p.Hurwitz) : Convex ℝ (ellipseSet p) := by
  rw [convex_iff_forall_pos]
  intro z hz w hw a b ha hb hab
  have hzQ : p.conic4 z.1 z.2 < 0 :=
    (omega4_iff_conic4_neg hp _ _).1 hz
  have hwQ : p.conic4 w.1 w.2 < 0 :=
    (omega4_iff_conic4_neg hp _ _).1 hw
  have hprimal := primalQuadratic_nonneg hp (z.1 - w.1) (z.2 - w.2)
  have habnonneg : 0 ≤ a * b := mul_nonneg (le_of_lt ha) (le_of_lt hb)
  have hprod : 0 ≤ a * b * p.primalQuadratic (z.1 - w.1) (z.2 - w.2) :=
    mul_nonneg habnonneg hprimal
  have hweighted : a * p.conic4 z.1 z.2 + b * p.conic4 w.1 w.2 < 0 :=
    add_neg (mul_neg_of_pos_of_neg ha hzQ) (mul_neg_of_pos_of_neg hb hwQ)
  change p.omega4 (a * z.1 + b * w.1) (a * z.2 + b * w.2)
  apply (omega4_iff_conic4_neg hp _ _).2
  rw [conic4_convex_combo p _ _ _ _ a b hab]
  linarith

/-- Strict linear separation of two disjoint open quartic ellipses. -/
lemma separating_direction_of_disjoint
    {p q : MonicQuarticCoeff}
    (hp : p.Hurwitz) (hq : q.Hurwitz)
    (hdisjoint : ¬ ∃ x y : ℝ, p.omega4 x y ∧ q.omega4 x y) :
    ∃ A B C : ℝ,
      (A ≠ 0 ∨ B ≠ 0) ∧
      (∀ x y : ℝ, p.omega4 x y → A * x + B * y < C) ∧
      (∀ x y : ℝ, q.omega4 x y → C < A * x + B * y) := by
  have hdisj : Disjoint (ellipseSet p) (ellipseSet q) := by
    rw [Set.disjoint_left]
    intro z hzP hzQ
    exact hdisjoint ⟨z.1, z.2, hzP, hzQ⟩
  obtain ⟨f, C, hfP, hfQ⟩ :=
    geometric_hahn_banach_open_open
      (ellipseSet_convex hp) (ellipseSet_isOpen hp)
      (ellipseSet_convex hq) (ellipseSet_isOpen hq) hdisj
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
    obtain ⟨zp, hzp⟩ := ellipseSet_nonempty hp
    obtain ⟨zq, hzq⟩ := ellipseSet_nonempty hq
    have hfp := hfP zp hzp
    have hfq := hfQ zq hzq
    rw [hrepr zp.1 zp.2, hnot.1, hnot.2] at hfp
    rw [hrepr zq.1 zq.2, hnot.1, hnot.2] at hfq
    norm_num at hfp hfq
    linarith
  refine ⟨A, B, C, hnormal, ?_, ?_⟩
  · intro x y hxy
    have h := hfP (x, y) hxy
    rw [hrepr] at h
    exact h
  · intro x y hxy
    have h := hfQ (x, y) hxy
    rw [hrepr] at h
    exact h

/-- Disjointness produces a direction in which the two support intervals
    are separated. -/
lemma support_gap_of_disjoint
    {p q : MonicQuarticCoeff}
    (hp : p.Hurwitz) (hq : q.Hurwitz)
    (hdisjoint : ¬ ∃ x y : ℝ, p.omega4 x y ∧ q.omega4 x y) :
    ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧
      supportRadius p A B + supportRadius q A B ≤
        (q.c1 - p.c1) * A + (q.c2 - p.c2) * B := by
  obtain ⟨A, B, C, hnormal, hhalfP, hhalfQ⟩ :=
    separating_direction_of_disjoint hp hq hdisjoint
  have hupper := support_upper_bound_of_halfspace hp hnormal hhalfP
  have hlower := support_lower_bound_of_halfspace hq hnormal hhalfQ
  refine ⟨A, B, hnormal, ?_⟩
  linarith

/-! ## The Hurwitz determinant excludes a separated support direction -/

lemma dualQuadratic_convex_identity
    (p q : MonicQuarticCoeff) (t A B : ℝ) :
    (convex p q t).dualQuadratic B A =
      (1 - t) * p.dualQuadratic B A + t * q.dualQuadratic B A -
        t * (1 - t) *
          (((q.c1 - p.c1) * A + (q.c2 - p.c2) * B) ^ 2) := by
  unfold dualQuadratic convex
  ring

theorem no_support_gap_of_hurwitz_segment
    {p q : MonicQuarticCoeff}
    (hp : p.Hurwitz) (hq : q.Hurwitz)
    (hsegment : allConvexHurwitz p q)
    {A B : ℝ} (hnormal : A ≠ 0 ∨ B ≠ 0)
    (hgap : supportRadius p A B + supportRadius q A B ≤
      (q.c1 - p.c1) * A + (q.c2 - p.c2) * B) : False := by
  let rp := supportRadius p A B
  let rq := supportRadius q A B
  let S := rp + rq
  let D := (q.c1 - p.c1) * A + (q.c2 - p.c2) * B
  have hrp : 0 < rp := supportRadius_pos hp hnormal
  have hrq : 0 < rq := supportRadius_pos hq hnormal
  have hS : 0 < S := by dsimp [S]; linarith
  have hSD : S ≤ D := hgap
  have hDsq : S ^ 2 ≤ D ^ 2 := by nlinarith
  let t : ℝ := rp / S
  have ht0 : 0 ≤ t := le_of_lt (div_pos hrp hS)
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ hS).2
    dsimp [S]
    linarith
  have hweight : 0 ≤ t * (1 - t) :=
    mul_nonneg ht0 (sub_nonneg.mpr ht1)
  have hpP : rp ^ 2 = p.dualQuadratic B A := supportRadius_sq hp hnormal
  have hqP : rq ^ 2 = q.dualQuadratic B A := supportRadius_sq hq hnormal
  have hweighted :
      (1 - t) * p.dualQuadratic B A +
        t * q.dualQuadratic B A = rp * rq := by
    rw [← hpP, ← hqP]
    dsimp [t, S]
    field_simp [ne_of_gt hS]
    ring
  have hweighted2 : t * (1 - t) * S ^ 2 = rp * rq := by
    dsimp [t, S]
    field_simp [ne_of_gt hS]
    ring
  have hmul : t * (1 - t) * S ^ 2 ≤ t * (1 - t) * D ^ 2 :=
    mul_le_mul_of_nonneg_left hDsq hweight
  have hpt : (convex p q t).Hurwitz := hsegment t ht0 ht1
  have hpositive : 0 < (convex p q t).dualQuadratic B A :=
    dualQuadratic_pos_of_normal_ne_zero hpt hnormal
  rw [dualQuadratic_convex_identity] at hpositive
  dsimp [D] at hmul
  nlinarith

theorem stable_segment_ellipse_intersection {p q : MonicQuarticCoeff}
    (hp : p.Hurwitz) (hq : q.Hurwitz) (hsegment : allConvexHurwitz p q) :
    ∃ x y : ℝ, p.omega4 x y ∧ q.omega4 x y := by
  by_contra hnone
  obtain ⟨A, B, hnormal, hgap⟩ := support_gap_of_disjoint hp hq hnone
  exact no_support_gap_of_hurwitz_segment hp hq hsegment hnormal hgap

/-! ## 4. 一次选取 ε，同时加入常数项和四次项 -/

/-- 负扰动被线性项控制：t²*evenPart(t) ≥ -c₂³*t。 -/
lemma evenPart_linear_perturb_lower {p : MonicQuarticCoeff} (hp : p.Hurwitz)
    (t : ℝ) (ht : 0 ≤ t) : -p.c2 ^ 3 * t ≤ t ^ 2 * p.evenPart t := by
  have hbase : -p.c2 ^ 3 ≤ t * p.evenPart t := by
    by_cases hlarge : p.c2 ≤ t
    · have heven : 0 ≤ p.evenPart t := by
        have := mul_nonneg ht (sub_nonneg.mpr hlarge)
        dsimp [evenPart]
        nlinarith [hp.2.2.2.1]
      exact le_trans (neg_nonpos.mpr (pow_nonneg hp.2.1.le 3)) (mul_nonneg ht heven)
    · have hsmall : t ≤ p.c2 := (lt_of_not_ge hlarge).le
      have ht2 : t ^ 2 ≤ p.c2 ^ 2 := by gcongr
      have hmul := mul_le_mul_of_nonneg_left ht2 hp.2.1.le
      dsimp [evenPart]
      nlinarith [pow_nonneg ht 3, mul_nonneg hp.2.2.2.1.le ht]
  have hmul := mul_le_mul_of_nonneg_right hbase ht
  nlinarith

/-- 同时扰动后的频率分子仍有统一正下界 ε*c₄。r=0 时给出三阶分子。 -/
lemma quarticCross_lower_of_small_perturbations {p : MonicQuarticCoeff}
    {x y z r m : ℝ} (hp : p.Hurwitz)
    (hbase : ∀ t : ℝ, m ≤ p.baseQuadratic x y t)
    (hz : 0 ≤ z) (hr : 0 ≤ r)
    (hsmall : z * p.c2 + r * p.c2 ^ 3 ≤ m)
    (t : ℝ) (ht : 0 ≤ t) : z * p.c4 ≤ p.quarticCross r x y z t := by
  have hq := mul_le_mul_of_nonneg_right (hbase t) ht
  have heven : p.c4 - p.c2 * t ≤ p.evenPart t := by
    dsimp [evenPart]
    nlinarith [sq_nonneg t]
  have hzbound := mul_le_mul_of_nonneg_left heven hz
  have hrbound := mul_le_mul_of_nonneg_left (evenPart_linear_perturb_lower hp t ht) hr
  have hrest := mul_nonneg (sub_nonneg.mpr hsmall) ht
  dsimp [quarticCross, cubicCross]
  nlinarith

/-- 一个公共 ε>0 同时满足两个分母的扰动上界。 -/
lemma common_small_parameter {p q : MonicQuarticCoeff} {x y : ℝ}
    (hp : p.Hurwitz) (hq : q.Hurwitz) (hpxy : p.omega4 x y) (hqxy : q.omega4 x y) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ t : ℝ, 0 ≤ t → ε * p.c4 ≤ p.quarticCross ε x y ε t) ∧
      (∀ t : ℝ, 0 ≤ t → ε * q.c4 ≤ q.quarticCross ε x y ε t) ∧
      (∀ t : ℝ, 0 ≤ t → ε * p.c4 ≤ p.cubicCross x y ε t) ∧
      (∀ t : ℝ, 0 ≤ t → ε * q.c4 ≤ q.cubicCross x y ε t) := by
  obtain ⟨mp, hmp, hpb⟩ := omega4_baseQuadratic_uniform hpxy
  obtain ⟨mq, hmq, hqb⟩ := omega4_baseQuadratic_uniform hqxy
  have hLp : 0 < p.c2 + p.c2 ^ 3 := add_pos hp.2.1 (pow_pos hp.2.1 3)
  have hLq : 0 < q.c2 + q.c2 ^ 3 := add_pos hq.2.1 (pow_pos hq.2.1 3)
  let ε := min (mp / (p.c2 + p.c2 ^ 3)) (mq / (q.c2 + q.c2 ^ 3))
  have hε : 0 < ε := lt_min (div_pos hmp hLp) (div_pos hmq hLq)
  have hpSmall : ε * p.c2 + ε * p.c2 ^ 3 ≤ mp := by
    have h := (le_div_iff₀ hLp).mp (min_le_left
      (mp / (p.c2 + p.c2 ^ 3)) (mq / (q.c2 + q.c2 ^ 3)))
    dsimp [ε]
    nlinarith
  have hqSmall : ε * q.c2 + ε * q.c2 ^ 3 ≤ mq := by
    have h := (le_div_iff₀ hLq).mp (min_le_right
      (mp / (p.c2 + p.c2 ^ 3)) (mq / (q.c2 + q.c2 ^ 3)))
    dsimp [ε]
    nlinarith
  have hpSmall0 : ε * p.c2 + 0 * p.c2 ^ 3 ≤ mp := by
    nlinarith [mul_nonneg hε.le (pow_nonneg hp.2.1.le 3)]
  have hqSmall0 : ε * q.c2 + 0 * q.c2 ^ 3 ≤ mq := by
    nlinarith [mul_nonneg hε.le (pow_nonneg hq.2.1.le 3)]
  refine ⟨ε, hε, quarticCross_lower_of_small_perturbations hp hpb hε.le hε.le hpSmall,
    quarticCross_lower_of_small_perturbations hq hqb hε.le hε.le hqSmall, ?_, ?_⟩
  · simpa [quarticCross] using
      quarticCross_lower_of_small_perturbations hp hpb hε.le (le_refl 0) hpSmall0
  · simpa [quarticCross] using
      quarticCross_lower_of_small_perturbations hq hqb hε.le (le_refl 0) hqSmall0

/-- 分母保持四阶，先记录公共三阶分子 s³+x*s²+y*s+z 的存在性。 -/
theorem stable_segment_has_common_cubic {p q : MonicQuarticCoeff}
    (hp : p.Hurwitz) (hq : q.Hurwitz) (hsegment : allConvexHurwitz p q) :
    ∃ x y z : ℝ, 0 < z ∧ p.cubicRePos x y z ∧ q.cubicRePos x y z := by
  obtain ⟨x, y, hpxy, hqxy⟩ := stable_segment_ellipse_intersection hp hq hsegment
  obtain ⟨ε, hε, _, _, hpCubic, hqCubic⟩ := common_small_parameter hp hq hpxy hqxy
  refine ⟨x, y, ε, hε, ?_, ?_⟩
  · exact cubicRePos_of_cross_pos hp (fun t ht => lt_of_lt_of_le
      (mul_pos hε hp.2.2.2.1) (hpCubic t ht))
  · exact cubicRePos_of_cross_pos hq (fun t ht => lt_of_lt_of_le
      (mul_pos hε hq.2.2.2.1) (hqCubic t ht))

/-- 直接构造 c(s)=ε*s⁴+s³+x*s²+y*s+ε，常数项与最高次系数相同。 -/
theorem stable_segment_has_common_spr4 {p q : MonicQuarticCoeff}
    (hp : p.Hurwitz) (hq : q.Hurwitz) (hsegment : allConvexHurwitz p q) :
    ∃ ε x y : ℝ, 0 < ε ∧ p.SPR4For ε x y ε ∧ q.SPR4For ε x y ε := by
  obtain ⟨x, y, hpxy, hqxy⟩ := stable_segment_ellipse_intersection hp hq hsegment
  obtain ⟨ε, hε, hpQuartic, hqQuartic, _, _⟩ := common_small_parameter hp hq hpxy hqxy
  refine ⟨ε, x, y, hε, ⟨hp, hε, ?_⟩, ⟨hq, hε, ?_⟩⟩
  · intro ω
    rw [re_quartic_div_quartic]
    exact div_pos (lt_of_lt_of_le (mul_pos hε hp.2.2.2.1)
      (hpQuartic (ω ^ 2) (sq_nonneg ω))) (evalJW_normSq_pos hp ω)
  · intro ω
    rw [re_quartic_div_quartic]
    exact div_pos (lt_of_lt_of_le (mul_pos hε hq.2.2.2.1)
      (hqQuartic (ω ^ 2) (sq_nonneg ω))) (evalJW_normSq_pos hq ω)

/-! ## 5. 必要性：SPR 商的分子 Hurwitz，再使用倒数与凸组合 -/

def monicCross (n d : MonicQuarticCoeff) (t : ℝ) : ℝ :=
  n.evenPart t * d.evenPart t +
    t * (n.c3 - n.c1 * t) * (d.c3 - d.c1 * t)

lemma monicCross_identity (n d : MonicQuarticCoeff) (ω : ℝ) :
    (n.evalJW ω).re * (d.evalJW ω).re +
      (n.evalJW ω).im * (d.evalJW ω).im =
        monicCross n d (ω ^ 2) := by
  rw [n.evalJW_re, n.evalJW_im, d.evalJW_re, d.evalJW_im]
  unfold monicCross evenPart
  ring

lemma re_monic_div (n d : MonicQuarticCoeff) (ω : ℝ) :
    ((n.evalJW ω) / d.evalJW ω).re =
      monicCross n d (ω ^ 2) / Complex.normSq (d.evalJW ω) := by
  rw [complex_div_re_eq, monicCross_identity]

lemma monicCross_pos_on_nonneg
    {n d : MonicQuarticCoeff} (hd : d.Hurwitz)
    (h : ∀ ω : ℝ, 0 < ((n.evalJW ω) / d.evalJW ω).re) :
    ∀ t : ℝ, 0 ≤ t → 0 < monicCross n d t := by
  intro t ht
  let ω := Real.sqrt t
  have hω : ω ^ 2 = t := Real.sq_sqrt ht
  have hpos := h ω
  rw [re_monic_div, hω] at hpos
  exact (div_pos_iff_of_pos_right (evalJW_normSq_pos hd ω)).mp hpos

lemma evenPart_pivot_neg {d : MonicQuarticCoeff} (hd : d.Hurwitz) :
    d.evenPart (d.c3 / d.c1) < 0 := by
  have hd1 : 0 < d.c1 := hd.1
  have hdet : 0 < d.hurwitzDet := hd.det_pos
  have hscaled :
      d.c1 ^ 2 * d.evenPart (d.c3 / d.c1) = -d.hurwitzDet := by
    unfold evenPart hurwitzDet
    field_simp [ne_of_gt hd1]
    ring
  have hsq : 0 < d.c1 ^ 2 := sq_pos_of_pos hd1
  have hneg : d.c1 ^ 2 * d.evenPart (d.c3 / d.c1) < 0 := by
    rw [hscaled]
    linarith
  by_contra hnot
  have hnonneg : 0 ≤ d.evenPart (d.c3 / d.c1) := le_of_not_gt hnot
  have hprod := mul_nonneg (le_of_lt hsq) hnonneg
  linarith

/-- The two positive zeroes of the denominator's even part straddle the
    zero of its imaginary part. -/
lemma evenPart_two_roots {d : MonicQuarticCoeff} (hd : d.Hurwitz) :
    ∃ α β : ℝ,
      0 < α ∧ α < d.c3 / d.c1 ∧ d.c3 / d.c1 < β ∧ β < d.c2 ∧
      d.evenPart α = 0 ∧ d.evenPart β = 0 := by
  have hd1 : 0 < d.c1 := hd.1
  have hd2 : 0 < d.c2 := hd.2.1
  have hd3 : 0 < d.c3 := hd.2.2.1
  have hd4 : 0 < d.c4 := hd.2.2.2.1
  let t0 : ℝ := d.c3 / d.c1
  have ht0 : 0 < t0 := div_pos hd3 hd1
  have ht0lt : t0 < d.c2 := by
    dsimp [t0]
    apply (div_lt_iff₀ hd1).2
    have hfirst := hd.2.2.2.2.1
    nlinarith
  have hf0 : 0 < d.evenPart 0 := by simpa [evenPart] using hd4
  have hft0 : d.evenPart t0 < 0 := evenPart_pivot_neg hd
  have hfc2 : 0 < d.evenPart d.c2 := by
    unfold evenPart
    nlinarith
  have hcont : Continuous (fun t : ℝ => d.evenPart t) := by
    unfold evenPart
    fun_prop
  have hleft : 0 ∈ Set.Ioo (d.evenPart t0) (d.evenPart 0) := ⟨hft0, hf0⟩
  obtain ⟨α, hαmem, hαroot⟩ :=
    (intermediate_value_Ioo' (le_of_lt ht0) hcont.continuousOn) hleft
  have hright : 0 ∈ Set.Ioo (d.evenPart t0) (d.evenPart d.c2) := ⟨hft0, hfc2⟩
  obtain ⟨β, hβmem, hβroot⟩ :=
    (intermediate_value_Ioo (le_of_lt ht0lt) hcont.continuousOn) hright
  exact ⟨α, β, hαmem.1, hαmem.2, hβmem.1, hβmem.2,
    hαroot, hβroot⟩

lemma evenPart_between_roots_neg (d : MonicQuarticCoeff)
    {α β t : ℝ} (hαβ : α < β)
    (hαroot : d.evenPart α = 0) (hβroot : d.evenPart β = 0)
    (hαt : α < t) (htβ : t < β) :
    d.evenPart t < 0 := by
  have hfactor : (β - α) * (α + β - d.c2) = 0 := by
    unfold evenPart at hαroot hβroot
    nlinarith
  have hsum : α + β = d.c2 := by
    have hdiff : β - α ≠ 0 := ne_of_gt (sub_pos.mpr hαβ)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hdiff)
  have hprod : α * β = d.c4 := by
    unfold evenPart at hαroot
    rw [← hsum] at hαroot
    nlinarith
  have hformula : d.evenPart t = (t - α) * (t - β) := by
    unfold evenPart
    rw [← hsum, ← hprod]
    ring
  rw [hformula]
  exact mul_neg_of_pos_of_neg (sub_pos.mpr hαt) (sub_neg.mpr htβ)

lemma evenPart_pivot_scaled (n : MonicQuarticCoeff)
    (hn1 : n.c1 ≠ 0) :
    n.c1 ^ 2 * n.evenPart (n.c3 / n.c1) = -n.hurwitzDet := by
  unfold evenPart hurwitzDet
  field_simp [hn1]
  ring

theorem numerator_hurwitz {d n : MonicQuarticCoeff} (hd : d.Hurwitz)
    (hreal : ∀ ω : ℝ, 0 < ((n.evalJW ω) / d.evalJW ω).re) : n.Hurwitz := by
  obtain ⟨α, β, hα0, hαt0, ht0β, _, hαroot, hβroot⟩ :=
    evenPart_two_roots hd
  have hd1 : 0 < d.c1 := hd.1
  have hd3 : 0 < d.c3 := hd.2.2.1
  have hd4 : 0 < d.c4 := hd.2.2.2.1
  have hαβ : α < β := lt_trans hαt0 ht0β
  have hβ0 : 0 < β := lt_trans (div_pos hd3 hd1) ht0β
  have hcross := monicCross_pos_on_nonneg hd hreal
  have hdα : 0 < d.c3 - d.c1 * α := by
    have hmul := (lt_div_iff₀ hd1).mp hαt0
    nlinarith
  have hdβ : d.c3 - d.c1 * β < 0 := by
    have hmul := (div_lt_iff₀ hd1).mp ht0β
    nlinarith
  have hcα : 0 < α * (n.c3 - n.c1 * α) * (d.c3 - d.c1 * α) := by
    simpa [monicCross, hαroot] using hcross α (le_of_lt hα0)
  have hnα : 0 < n.c3 - n.c1 * α := by
    have hrest : 0 < (n.c3 - n.c1 * α) * (d.c3 - d.c1 * α) :=
      (mul_pos_iff_of_pos_left hα0).mp (by simpa [mul_assoc] using hcα)
    exact (mul_pos_iff_of_pos_right hdα).mp hrest
  have hcβ : 0 < β * (n.c3 - n.c1 * β) * (d.c3 - d.c1 * β) := by
    simpa [monicCross, hβroot] using hcross β (le_of_lt hβ0)
  have hnβ : n.c3 - n.c1 * β < 0 := by
    have hrest : 0 < (n.c3 - n.c1 * β) * (d.c3 - d.c1 * β) :=
      (mul_pos_iff_of_pos_left hβ0).mp (by simpa [mul_assoc] using hcβ)
    by_contra hnot
    have hnonneg : 0 ≤ n.c3 - n.c1 * β := le_of_not_gt hnot
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hnonneg (le_of_lt hdβ)
    linarith
  have hn1 : 0 < n.c1 := by
    by_contra hnot
    have hle : n.c1 ≤ 0 := le_of_not_gt hnot
    have hnonpos : n.c1 * (β - α) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt (sub_pos.mpr hαβ))
    nlinarith
  have hn3 : 0 < n.c3 := by
    nlinarith [mul_pos hn1 hα0]
  have hn4 : 0 < n.c4 := by
    have hc0 := hcross 0 (by norm_num)
    simp [monicCross, evenPart] at hc0
    exact (mul_pos_iff_of_pos_right hd4).mp hc0
  let u : ℝ := n.c3 / n.c1
  have hu : 0 < u := div_pos hn3 hn1
  have hαu : α < u := by
    dsimp [u]
    apply (lt_div_iff₀ hn1).2
    nlinarith [hnα]
  have huβ : u < β := by
    dsimp [u]
    apply (div_lt_iff₀ hn1).2
    nlinarith [hnβ]
  have hdeven : d.evenPart u < 0 :=
    evenPart_between_roots_neg d hαβ hαroot hβroot hαu huβ
  have hnimag : n.c3 - n.c1 * u = 0 := by
    dsimp [u]
    field_simp [ne_of_gt hn1]
  have hcU := hcross u (le_of_lt hu)
  have hprod : 0 < n.evenPart u * d.evenPart u := by
    simpa [monicCross, hnimag] using hcU
  have hneven : n.evenPart u < 0 := by
    by_contra hnot
    have hnonneg : 0 ≤ n.evenPart u := le_of_not_gt hnot
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hnonneg (le_of_lt hdeven)
    linarith
  have hn2 : 0 < n.c2 := by
    by_contra hnot
    have hle : n.c2 ≤ 0 := le_of_not_gt hnot
    have hprodnonpos := mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt hu)
    unfold evenPart at hneven
    nlinarith [sq_nonneg u]
  have hscaled := evenPart_pivot_scaled n (ne_of_gt hn1)
  have hneg : n.c1 ^ 2 * n.evenPart u < 0 :=
    mul_neg_of_pos_of_neg (sq_pos_of_pos hn1) hneven
  dsimp [u] at hneg
  rw [hscaled] at hneg
  have hdet : 0 < n.hurwitzDet := by linarith
  exact Hurwitz.of_pos_coeff_and_det hn1 hn2 hn3 hn4 hdet

def normalizedNumerator (r x y z : ℝ) : MonicQuarticCoeff where
  c1 := 1 / r
  c2 := x / r
  c3 := y / r
  c4 := z / r

lemma quarticNumEvalJW_eq_scaled_normalized
    {r x y z : ℝ} (hr : r ≠ 0) (ω : ℝ) :
    quarticNumEvalJW r x y z ω =
      (r : ℂ) * (normalizedNumerator r x y z).evalJW ω := by
  unfold quarticNumEvalJW normalizedNumerator evalJW cubicEvalJW
  push_cast
  field_simp [hr]
  ring

lemma existsCommonMonicSPR4_of_constructed
    {p q : MonicQuarticCoeff}
    (hcommon : ExistsCommonSPR4 p q) :
    ExistsCommonMonicSPR4 p q := by
  obtain ⟨r, x, y, z, hp, hq⟩ := hcommon
  have hr : 0 < r := hp.2.1
  let n := normalizedNumerator r x y z
  refine ⟨n, ⟨hp.1, ?_⟩, ⟨hq.1, ?_⟩⟩
  · intro ω
    have h := hp.2.2 ω
    rw [quarticNumEvalJW_eq_scaled_normalized (ne_of_gt hr), mul_div_assoc] at h
    norm_num at h
    exact (mul_pos_iff_of_pos_left hr).mp h
  · intro ω
    have h := hq.2.2 ω
    rw [quarticNumEvalJW_eq_scaled_normalized (ne_of_gt hr), mul_div_assoc] at h
    norm_num at h
    exact (mul_pos_iff_of_pos_left hr).mp h

lemma evalJW_convex (p q : MonicQuarticCoeff) (t ω : ℝ) :
    (convex p q t).evalJW ω =
      (((1 - t : ℝ) : ℂ) * p.evalJW ω) +
        (t : ℂ) * q.evalJW ω := by
  unfold convex evalJW
  push_cast
  ring

lemma re_convex_div (p q d : MonicQuarticCoeff) (t ω : ℝ) :
    (((convex p q t).evalJW ω) / d.evalJW ω).re =
      (1 - t) * ((p.evalJW ω) / d.evalJW ω).re +
        t * ((q.evalJW ω) / d.evalJW ω).re := by
  rw [evalJW_convex, add_div]
  rw [mul_div_assoc, mul_div_assoc]
  norm_num

theorem allConvexHurwitz_of_commonMonicSPR4 {p q : MonicQuarticCoeff}
    (hcommon : ExistsCommonMonicSPR4 p q) : allConvexHurwitz p q := by
  obtain ⟨n, hp, hq⟩ := hcommon
  have hn : n.Hurwitz := numerator_hurwitz hp.1 hp.2
  have hInv (d : MonicQuarticCoeff) (hd : d.MonicSPR4For n) (ω : ℝ) :
      0 < ((d.evalJW ω) / n.evalJW ω).re :=
    (complex_div_re_pos_comm (evalJW_ne_zero hn ω) (evalJW_ne_zero hd.1 ω)).1 (hd.2 ω)
  intro t ht0 ht1
  apply numerator_hurwitz hn
  intro ω
  rw [re_convex_div]
  simpa [add_comm] using convexCoeff_pos_of_pos (hInv p hp ω) (hInv q hq ω) ht0 ht1

/-! ## 6. 主定理：首一、构造形式和任意正最高次系数三个接口 -/

theorem paper_n4_main_constructive {p q : MonicQuarticCoeff}
    (hp : p.Hurwitz) (hq : q.Hurwitz) :
    ExistsCommonSPR4 p q ↔ allConvexHurwitz p q := by
  constructor
  · intro h
    exact allConvexHurwitz_of_commonMonicSPR4 (existsCommonMonicSPR4_of_constructed h)
  · intro hsegment
    obtain ⟨ε, x, y, _, hpSPR, hqSPR⟩ := stable_segment_has_common_spr4 hp hq hsegment
    exact ⟨ε, x, y, ε, hpSPR, hqSPR⟩

theorem paper_n4_main_monic {p q : MonicQuarticCoeff}
    (hp : p.Hurwitz) (hq : q.Hurwitz) :
    ExistsCommonMonicSPR4 p q ↔ allConvexHurwitz p q := by
  constructor
  · exact allConvexHurwitz_of_commonMonicSPR4
  · intro hsegment
    exact existsCommonMonicSPR4_of_constructed ((paper_n4_main_constructive hp hq).2 hsegment)

def quarticEvalGeneral
    (c0 c1 c2 c3 c4 ω : ℝ) : ℂ :=
  (c0 : ℂ) * jw ω ^ 4 + (c1 : ℂ) * jw ω ^ 3 +
    (c2 : ℂ) * jw ω ^ 2 + (c3 : ℂ) * jw ω + (c4 : ℂ)

lemma quarticEvalGeneral_normalize
    {c0 c1 c2 c3 c4 : ℝ} (hc0 : c0 ≠ 0) (ω : ℝ) :
    quarticEvalGeneral c0 c1 c2 c3 c4 ω =
      (c0 : ℂ) *
        ({ c1 := c1 / c0, c2 := c2 / c0,
           c3 := c3 / c0, c4 := c4 / c0 } : MonicQuarticCoeff).evalJW ω := by
  unfold quarticEvalGeneral evalJW
  push_cast
  field_simp [hc0]
  ring

lemma quarticEvalGeneral_one
    (n : MonicQuarticCoeff) (ω : ℝ) :
    quarticEvalGeneral 1 n.c1 n.c2 n.c3 n.c4 ω = n.evalJW ω := by
  unfold quarticEvalGeneral evalJW
  norm_num

/-- Equal-degree SPR for an arbitrary quartic numerator.  The positive
    leading coefficient is the high-frequency gain condition, as in `n3`. -/
def SPRQuarticFor (p : MonicQuarticCoeff)
    (c0 c1 c2 c3 c4 : ℝ) : Prop :=
  0 < c0 ∧ p.Hurwitz ∧
    ∀ ω : ℝ,
      0 < ((quarticEvalGeneral c0 c1 c2 c3 c4 ω) / p.evalJW ω).re

def ExistsCommonSPRQuartic (p q : MonicQuarticCoeff) : Prop :=
  ∃ c0 c1 c2 c3 c4 : ℝ,
    p.SPRQuarticFor c0 c1 c2 c3 c4 ∧
    q.SPRQuarticFor c0 c1 c2 c3 c4

lemma re_general_quartic_div_eq_scale_normalized
    {p : MonicQuarticCoeff} {c0 c1 c2 c3 c4 : ℝ}
    (hc0 : c0 ≠ 0) (ω : ℝ) :
    ((quarticEvalGeneral c0 c1 c2 c3 c4 ω) / p.evalJW ω).re =
      c0 *
        ((({ c1 := c1 / c0, c2 := c2 / c0,
             c3 := c3 / c0, c4 := c4 / c0 } : MonicQuarticCoeff).evalJW ω)
          / p.evalJW ω).re := by
  rw [quarticEvalGeneral_normalize hc0, mul_div_assoc]
  norm_num

theorem existsCommonSPRQuartic_iff_monic (p q : MonicQuarticCoeff) :
    ExistsCommonSPRQuartic p q ↔ ExistsCommonMonicSPR4 p q := by
  constructor
  · rintro ⟨c0, c1, c2, c3, c4, hp, hq⟩
    have hc0 : c0 ≠ 0 := ne_of_gt hp.1
    let n : MonicQuarticCoeff :=
      ⟨c1 / c0, c2 / c0, c3 / c0, c4 / c0⟩
    refine ⟨n, ⟨hp.2.1, ?_⟩, ⟨hq.2.1, ?_⟩⟩
    · intro ω
      have h := hp.2.2 ω
      rw [re_general_quartic_div_eq_scale_normalized hc0] at h
      exact (mul_pos_iff_of_pos_left hp.1).mp h
    · intro ω
      have h := hq.2.2 ω
      rw [re_general_quartic_div_eq_scale_normalized hc0] at h
      exact (mul_pos_iff_of_pos_left hp.1).mp h
  · rintro ⟨n, hp, hq⟩
    refine ⟨1, n.c1, n.c2, n.c3, n.c4, ?_, ?_⟩
    · refine ⟨by norm_num, hp.1, ?_⟩
      intro ω
      rw [quarticEvalGeneral_one]
      exact hp.2 ω
    · refine ⟨by norm_num, hq.1, ?_⟩
      intro ω
      rw [quarticEvalGeneral_one]
      exact hq.2 ω

/-- The full fourth-order coefficient-level paper theorem. -/
theorem paper_n4_full_spr_criterion
    {p q : MonicQuarticCoeff}
    (hp : p.Hurwitz) (hq : q.Hurwitz) :
    ExistsCommonSPRQuartic p q ↔ allConvexHurwitz p q := by
  rw [existsCommonSPRQuartic_iff_monic]
  exact paper_n4_main_monic hp hq

end

end MonicQuarticCoeff

end MKNumina.SPR.Simplified

#print axioms MKNumina.SPR.Simplified.MonicQuarticCoeff.stable_segment_has_common_cubic
#print axioms MKNumina.SPR.Simplified.MonicQuarticCoeff.stable_segment_has_common_spr4
#print axioms MKNumina.SPR.Simplified.MonicQuarticCoeff.paper_n4_main_monic
#print axioms MKNumina.SPR.Simplified.MonicQuarticCoeff.paper_n4_full_spr_criterion
