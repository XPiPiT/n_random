import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Choose

import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases

/-!
# 六阶线段多项式的精简 SPR 综合证明

主定理与 `SPR/n6.lean` 一致：两个首一六阶分母具有公共首一六阶
SPR 分子，当且仅当整条分母线段的全部根都在严格左半平面。
Hurwitz 使用根位置定义，SPR 使用分母稳定性与全频率严格正实部。

充分性采用 `SPR/n_random2.lean` 的统一接触点计数及留数反射论证，
所需辅助引理完整放在本文件的 Core 命名空间。辅助引理保留一般
次数参数 d；六阶充分性在本文件取 d=6 后直接反证，主定理保留
原文件的六个系数接口。没有导入原五阶、六阶或任意阶主定理。

主线：频率紧化与凸分离 → 临界支撑 → 弱正实性限制根的位置
→ 正负频率统一计数 → 留数反射恒等式 → 两个次数要求矛盾。
原文件针对四至七个接触点的分类，由同一个次数矛盾统一处理。

本文件聚焦完整主定理；论文审校、反例和区域几何仍见原文件。
主要接口位于 `MKNumina.SPR.Simplified.SixthOrder`。
-/

namespace MKNumina.SPR.Simplified.SixthOrder

namespace Core

noncomputable section

open Polynomial Set Filter
open scoped Topology ComplexConjugate

/-- Evaluation of a real polynomial at a complex argument. -/
def value (p : ℝ[X]) (z : ℂ) : ℂ := Polynomial.aeval z p

theorem value_eq_mapped_eval (p : ℝ[X]) (z : ℂ) :
    value p z = (p.map (algebraMap ℝ ℂ)).eval z := by
  simp [value, Polynomial.aeval_def, Polynomial.eval_map]

/-- Root exclusion on the closed right half-plane. -/
def Stable (p : ℝ[X]) : Prop :=
  ∀ z : ℂ, 0 ≤ z.re → value p z ≠ 0

/-- The affine segment between the two denominator polynomials. -/
def blend (a b : ℝ[X]) (t : ℝ) : ℝ[X] := C (1-t)*a + C t*b

/-- Strict positivity of the real part on the imaginary axis. -/
def FrequencyPositive (c p : ℝ[X]) : Prop :=
  ∀ w : ℝ, 0 < (value c (w*Complex.I) / value p (w*Complex.I)).re

/-- Frequency-domain SPR, with denominator stability recorded explicitly. -/
def SPR (c p : ℝ[X]) : Prop := Stable p ∧ FrequencyPositive c p

theorem stable_axis_ne_zero {p : ℝ[X]} (hp : Stable p) (w : ℝ) :
    value p ((w : ℂ)*Complex.I) ≠ 0 := by
  apply hp
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, le_refl]

/-- The Hurwitz class H^d, including normalization and exact degree. -/
def HurwitzClass (d : ℕ) (p : ℝ[X]) : Prop :=
  p.Monic ∧ p.natDegree = d ∧ Stable p

/-- The real Euclidean pairing of two complex numbers. -/
def pairing (u v : ℂ) : ℝ := (u * conj v).re

theorem value_blend (a b : ℝ[X]) (t : ℝ) (z : ℂ) :
    value (blend a b t) z = (1-t : ℝ)*value a z + (t : ℂ)*value b z := by
  simp [value, blend]

theorem coeff_blend (a b : ℝ[X]) (t : ℝ) (k : ℕ) :
    (blend a b t).coeff k = (1-t)*a.coeff k+t*b.coeff k := by
  simp only [blend, Polynomial.coeff_add, Polynomial.coeff_C_mul]

theorem blend_monic_and_degree {a b : ℝ[X]} {d : ℕ}
    (ha : a.Monic) (hb : b.Monic)
    (hda : a.natDegree = d) (hdb : b.natDegree = d) (t : ℝ) :
    (blend a b t).Monic ∧ (blend a b t).natDegree = d := by
  have hbound : (blend a b t).natDegree ≤ d := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [coeff_blend, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    ring
  have htop : (blend a b t).coeff d = 1 := by
    have hA : a.coeff d = 1 := by simpa [← hda] using ha.coeff_natDegree
    have hB : b.coeff d = 1 := by simpa [← hdb] using hb.coeff_natDegree
    rw [coeff_blend, hA, hB]
    ring
  exact ⟨Polynomial.monic_of_natDegree_le_of_coeff_eq_one d hbound htop,
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hbound (by rw [htop]; norm_num)⟩

theorem real_quotient (u v : ℂ) :
    (u/v).re = pairing u v / Complex.normSq v := by
  simp [Complex.div_re, pairing, Complex.mul_re]
  ring

theorem positive_quotient_iff (u v : ℂ) (hv : v ≠ 0) :
    0 < (u/v).re ↔ 0 < pairing u v := by
  rw [real_quotient]
  exact div_pos_iff_of_pos_right (Complex.normSq_pos.mpr hv)

theorem pairing_blend (u v₀ v₁ : ℂ) (t : ℝ) :
    pairing u ((1-t : ℝ)*v₀+(t : ℂ)*v₁) =
      (1-t)*pairing u v₀+t*pairing u v₁ := by
  simp [pairing, Complex.mul_re, Complex.mul_im]
  ring

private theorem convex_strict_pos {x y t : ℝ}
    (hx : 0 < x) (hy : 0 < y) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < (1-t)*x+t*y := by
  by_cases hzero : t = 0
  · simpa [hzero] using hx
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr ht.2) hx.le)
      (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm hzero)) hy)

theorem frequency_positive_denominator_ne_zero {c p : ℝ[X]}
    (h : FrequencyPositive c p) (w : ℝ) : value p (w*Complex.I) ≠ 0 := by
  intro hz
  have hp := h w
  simp [hz] at hp

/-- Endpoint positivity itself excludes all imaginary-axis zeros of the segment. -/
theorem endpoint_pairing_positive {c a b : ℝ[X]}
    (ha : FrequencyPositive c a) (hb : FrequencyPositive c b)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (w : ℝ) :
    0 < pairing (value c (w*Complex.I)) (value (blend a b t) (w*Complex.I)) := by
  rw [value_blend, pairing_blend]
  exact convex_strict_pos
    ((positive_quotient_iff _ _ (frequency_positive_denominator_ne_zero ha w)).mp (ha w))
    ((positive_quotient_iff _ _ (frequency_positive_denominator_ne_zero hb w)).mp (hb w)) ht

theorem segment_axis_nonvanishing {c a b : ℝ[X]}
    (ha : FrequencyPositive c a) (hb : FrequencyPositive c b)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (w : ℝ) :
    value (blend a b t) (w*Complex.I) ≠ 0 := by
  intro hz
  have hp := endpoint_pairing_positive ha hb t ht w
  simp [hz, pairing] at hp

/-- One fixed numerator stays frequency-positive on the whole segment. -/
theorem frequency_positive_on_segment {c a b : ℝ[X]}
    (ha : FrequencyPositive c a) (hb : FrequencyPositive c b)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : FrequencyPositive c (blend a b t) := by
  intro w
  exact (positive_quotient_iff _ _ (segment_axis_nonvanishing ha hb t ht w)).mpr
    (endpoint_pairing_positive ha hb t ht w)

/-- A monic polynomial that has no root near z cannot be small at z. -/
theorem eval_norm_lower_bound (p : ℂ[X]) (hp : p.Monic)
    (z : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hfar : ∀ u : ℂ, p.eval u = 0 → r ≤ ‖z-u‖) :
    r ^ p.natDegree ≤ ‖p.eval z‖ := by
  classical
  have hnorm (s : Multiset ℂ) :
      ‖(s.map (fun u => z-u)).prod‖ = (s.map (fun u => ‖z-u‖)).prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons u s ih => simp [ih, norm_mul]
  have hcount : p.roots.card = p.natDegree := by
    simpa using (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits p)).symm
  have hproduct : (p.roots.map (fun _ => r)).prod ≤
      (p.roots.map (fun u => ‖z-u‖)).prod := by
    apply Multiset.prod_map_le_prod_map₀
    · intro _ _
      exact hr
    · intro u hu
      exact hfar u ((Polynomial.mem_roots hp.ne_zero).mp hu)
  rw [Polynomial.eval_eq_prod_roots_sub_of_monic_of_splits_id hp
    (IsAlgClosed.splits p), hnorm]
  simpa [hcount] using hproduct

/-- Small evaluation of a monic polynomial forces a nearby root. -/
theorem root_near_of_small_eval (p : ℂ[X]) (hp : p.Monic)
    (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hsmall : ‖p.eval z‖ < r ^ p.natDegree) :
    ∃ u : ℂ, p.eval u = 0 ∧ ‖z-u‖ < r := by
  by_contra! hnone
  exact (not_le_of_gt hsmall) (eval_norm_lower_bound p hp z r hr.le hnone)

/-- A right-half-plane root persists under a continuous monic fixed-degree
family. No differentiability of the parameter or simplicity of the root is used. -/
theorem open_right_root_parameters
    {T : Type*} [TopologicalSpace T] (q : T → ℂ[X]) (d : ℕ)
    (hmonic : ∀ t, (q t).Monic) (hdegree : ∀ t, (q t).natDegree = d)
    (heval : ∀ z : ℂ, Continuous (fun t => (q t).eval z)) :
    IsOpen {t | ∃ z : ℂ, (q t).eval z = 0 ∧ 0 < z.re} := by
  rw [isOpen_iff_mem_nhds]
  rintro t ⟨z, hz, hre⟩
  have hsmall : ∀ᶠ u in 𝓝 t, ‖(q u).eval z‖ < z.re^d := by
    exact (isOpen_lt (heval z).norm continuous_const).mem_nhds
      (by simpa [hz] using pow_pos hre d)
  filter_upwards [hsmall] with u hu
  obtain ⟨v, hv, hdist⟩ := root_near_of_small_eval (q u) (hmonic u) z z.re hre
    (by simpa [hdegree u] using hu)
  refine ⟨v, hv, ?_⟩
  have hreal : z.re-v.re ≤ ‖z-v‖ := by
    simpa using Complex.re_le_norm (z-v)
  linarith

private theorem continuous_cauchy_bound
    {T : Type*} [TopologicalSpace T] (q : T → ℂ[X]) (d : ℕ)
    (hmonic : ∀ t, (q t).Monic) (hdegree : ∀ t, (q t).natDegree = d)
    (hcoeff : ∀ k : ℕ, Continuous (fun t => (q t).coeff k)) :
    Continuous (fun t => (q t).cauchyBound) := by
  have hsup : Continuous (fun t =>
      (Finset.range d).sup (fun k => ‖(q t).coeff k‖₊)) :=
    Continuous.finset_sup_apply (fun k _ => (hcoeff k).nnnorm)
  have heq : (fun t => (q t).cauchyBound) =
      (fun t => (Finset.range d).sup (fun k => ‖(q t).coeff k‖₊)+1) := by
    funext t
    simp [Polynomial.cauchyBound, hdegree t, (hmonic t).leadingCoeff]
  rw [heq]
  exact hsup.add continuous_const

private theorem closed_nonnegative_root_parameters
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [T2Space T]
    (q : T → ℂ[X]) (d : ℕ)
    (hmonic : ∀ t, (q t).Monic) (hdegree : ∀ t, (q t).natDegree = d)
    (hcoeff : ∀ k : ℕ, Continuous (fun t => (q t).coeff k))
    (heval : Continuous (fun tz : T × ℂ => (q tz.1).eval tz.2)) :
    IsClosed {t | ∃ z : ℂ, (q t).eval z = 0 ∧ 0 ≤ z.re} := by
  classical
  by_cases hT : Nonempty T
  · letI : Nonempty T := hT
    have hcont := continuous_cauchy_bound q d hmonic hdegree hcoeff
    obtain ⟨B, hB⟩ := isCompact_univ.bddAbove_image hcont.continuousOn
    let K : Set (T × ℂ) :=
      (univ ×ˢ Metric.closedBall (0 : ℂ) (B : ℝ)) ∩
        {tz | (q tz.1).eval tz.2 = 0 ∧ 0 ≤ tz.2.re}
    have hzero : IsClosed {tz : T × ℂ | (q tz.1).eval tz.2 = 0 ∧ 0 ≤ tz.2.re} :=
      (isClosed_eq heval continuous_const).inter
        (isClosed_le continuous_const (Complex.continuous_re.comp continuous_snd))
    have hcompact : IsCompact K :=
      (isCompact_univ.prod (isCompact_closedBall (0 : ℂ) (B : ℝ))).inter_right hzero
    have hproj : Prod.fst '' K = {t | ∃ z : ℂ, (q t).eval z = 0 ∧ 0 ≤ z.re} := by
      ext t
      constructor
      · rintro ⟨⟨u,z⟩, ⟨_, hz⟩, rfl⟩
        exact ⟨z,hz⟩
      · rintro ⟨z,hz,hre⟩
        refine ⟨(t,z), ⟨⟨mem_univ _, ?_⟩, hz, hre⟩, rfl⟩
        have hcauchy := Polynomial.IsRoot.norm_lt_cauchyBound
          (hmonic t).ne_zero hz
        have hupper : (q t).cauchyBound ≤ B := hB ⟨t,mem_univ _,rfl⟩
        have hnorm : ‖z‖ ≤ (B : ℝ) := by exact_mod_cast hcauchy.le.trans hupper
        simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
    rw [← hproj]
    exact (hcompact.image continuous_fst).isClosed
  · haveI : IsEmpty T := not_nonempty_iff.mp hT
    simpa only [Set.eq_empty_of_isEmpty] using (isClosed_empty : IsClosed (∅ : Set T))

/-- Stability cannot change in a compact connected monic fixed-degree family
without an imaginary-axis zero. -/
theorem zero_exclusion
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [T2Space T] [PreconnectedSpace T]
    (q : T → ℂ[X]) (d : ℕ)
    (hmonic : ∀ t, (q t).Monic) (hdegree : ∀ t, (q t).natDegree = d)
    (hcoeff : ∀ k : ℕ, Continuous (fun t => (q t).coeff k))
    (heval : Continuous (fun tz : T × ℂ => (q tz.1).eval tz.2))
    (haxis : ∀ t (w : ℝ), (q t).eval (w*Complex.I) ≠ 0)
    (t₀ : T) (hstart : ∀ z : ℂ, 0 ≤ z.re → (q t₀).eval z ≠ 0) :
    ∀ t (z : ℂ), 0 ≤ z.re → (q t).eval z ≠ 0 := by
  let U : Set T := {t | ∃ z : ℂ, (q t).eval z = 0 ∧ 0 < z.re}
  have hopen : IsOpen U := open_right_root_parameters q d hmonic hdegree
    (fun z => heval.comp (continuous_id.prodMk continuous_const))
  have hsame : U = {t | ∃ z : ℂ, (q t).eval z = 0 ∧ 0 ≤ z.re} := by
    ext t
    constructor
    · rintro ⟨z,hz,hre⟩
      exact ⟨z,hz,hre.le⟩
    · rintro ⟨z,hz,hre⟩
      refine ⟨z,hz,lt_of_le_of_ne hre ?_⟩
      intro hzre
      have heq : (z.im : ℂ)*Complex.I = z := by
        apply Complex.ext <;> simp [← hzre]
      exact haxis t z.im (heq.symm ▸ hz)
  have hclosed : IsClosed U := by
    rw [hsame]
    exact closed_nonnegative_root_parameters q d hmonic hdegree hcoeff heval
  have hnot : t₀ ∉ U := by
    rintro ⟨z,hz,hre⟩
    exact hstart z hre.le hz
  have hempty : U = ∅ := (isClopen_iff.mp ⟨hclosed,hopen⟩).resolve_right
    (fun h => hnot (by rw [h]; trivial))
  intro t z hre hz
  have ht : t ∈ U := by
    rw [hsame]
    exact ⟨z,hz,hre⟩
  simp [hempty] at ht

theorem stable_segment_of_axis_nonvanishing
    {a b : ℝ[X]} {d : ℕ} (ha : a.Monic) (hb : b.Monic)
    (hda : a.natDegree = d) (hdb : b.natDegree = d)
    (hstart : Stable a)
    (haxis : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ w : ℝ,
      value (blend a b t) (w*Complex.I) ≠ 0) :
    ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t) := by
  let T := Icc (0 : ℝ) 1
  letI : PreconnectedSpace T := Subtype.preconnectedSpace isPreconnected_Icc
  let q : T → ℂ[X] := fun t => (blend a b t.val).map (algebraMap ℝ ℂ)
  have qeval (t : T) (z : ℂ) : (q t).eval z = value (blend a b t.val) z :=
    (value_eq_mapped_eval _ z).symm
  have hmonic (t : T) : (q t).Monic :=
    (blend_monic_and_degree ha hb hda hdb t.val).1.map _
  have hdegree (t : T) : (q t).natDegree = d := by
    simpa [q] using (blend_monic_and_degree ha hb hda hdb t.val).2
  have hcoeff (k : ℕ) : Continuous (fun t : T => (q t).coeff k) := by
    simp only [q, Polynomial.coeff_map, coeff_blend]
    fun_prop
  have heval : Continuous (fun tz : T × ℂ => (q tz.1).eval tz.2) := by
    simp only [qeval]
    simp only [value_blend]
    unfold value
    fun_prop
  have hno (t : T) (w : ℝ) : (q t).eval (w*Complex.I) ≠ 0 := by
    rw [qeval]
    exact haxis t.val t.property w
  let t₀ : T := ⟨0,by constructor <;> norm_num⟩
  have hinit (z : ℂ) (hz : 0 ≤ z.re) : (q t₀).eval z ≠ 0 := by
    rw [qeval]
    simpa [t₀, blend] using hstart z hz
  have h := zero_exclusion q d hmonic hdegree hcoeff heval hno t₀ hinit
  intro t ht z hz
  simpa only [qeval] using h ⟨t,ht⟩ z hz

/-- The complete necessary direction; the numerator's degree is not needed. -/
theorem common_spr_implies_segment_hurwitz
    {a b c : ℝ[X]} {d : ℕ} (ha : a.Monic) (hb : b.Monic)
    (hda : a.natDegree = d) (hdb : b.natDegree = d)
    (hcA : SPR c a) (hcB : SPR c b) :
    ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → HurwitzClass d (blend a b t) := by
  have hstable := stable_segment_of_axis_nonvanishing ha hb hda hdb hcA.1
    (fun t ht w => segment_axis_nonvanishing hcA.2 hcB.2 t ht w)
  intro t ht
  exact ⟨(blend_monic_and_degree ha hb hda hdb t).1,
    (blend_monic_and_degree ha hb hda hdb t).2,hstable t ht⟩

/-- Any common endpoint numerator also works for every parameter on the segment. -/
theorem common_spr_extends_to_segment
    {a b c : ℝ[X]} {d : ℕ} (ha : a.Monic) (hb : b.Monic)
    (hda : a.natDegree = d) (hdb : b.natDegree = d)
    (hcA : SPR c a) (hcB : SPR c b) :
    ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → SPR c (blend a b t) := by
  intro t ht
  exact ⟨(common_spr_implies_segment_hurwitz ha hb hda hdb hcA hcB t ht).2.2,
    frequency_positive_on_segment hcA.2 hcB.2 t ht⟩

/-! ## 2. 频率紧化与有限维分离 -/

/-- Evaluation in homogeneous coordinates; y=0 represents infinite frequency. -/
def homogeneousValue (d : ℕ) (p : ℝ[X]) (x y : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (d+1), (p.coeff k : ℂ)*(x*Complex.I)^k*(y : ℂ)^(d-k)

theorem homogeneousValue_at_infinity (d : ℕ) (p : ℝ[X]) (x : ℝ) :
    homogeneousValue d p x 0 = (p.coeff d : ℂ)*(x*Complex.I)^d := by
  classical
  unfold homogeneousValue
  rw [Finset.sum_eq_single d]
  · simp
  · intro k hk hkd
    have hpos : 0 < d-k := by have := Finset.mem_range.mp hk; omega
    simp [zero_pow (Nat.ne_of_gt hpos)]
  · simp

theorem homogeneousValue_finite (d : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ d) (x y : ℝ) (hy : y ≠ 0) :
    homogeneousValue d p x y = (y : ℂ)^d * value p ((x/y : ℝ)*Complex.I) := by
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy
  rw [value, Polynomial.aeval_def,
    Polynomial.eval₂_eq_sum_range' (algebraMap ℝ ℂ) (by omega : p.natDegree < d+1)]
  unfold homogeneousValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkd : k ≤ d := by have := Finset.mem_range.mp hk; omega
  have hpow : (y : ℂ)^d * (((x : ℂ)*Complex.I)/(y : ℂ))^k =
      ((x : ℂ)*Complex.I)^k*(y : ℂ)^(d-k) := by
    rw [div_pow, show d = k+(d-k) by omega, pow_add]
    field_simp
    ring
  have harg : ((x/y : ℝ) : ℂ)*Complex.I = ((x : ℂ)*Complex.I)/(y : ℂ) := by
    push_cast
    ring
  simp only [Complex.coe_algebraMap]
  rw [harg]
  calc
    _ = (p.coeff k : ℂ)*(((x : ℂ)*Complex.I)^k*(y : ℂ)^(d-k)) := by ring
    _ = (p.coeff k : ℂ)*((y : ℂ)^d*(((x : ℂ)*Complex.I)/(y : ℂ))^k) := by rw [hpow]
    _ = _ := by ring

theorem pairing_common_factor (u v z : ℂ) :
    pairing (z*u) (z*v) = Complex.normSq z * pairing u v := by
  simp [pairing, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

/-- Frequency infinity tests the leading numerator coefficient exactly. -/
theorem homogeneous_pairing_at_infinity
    (d : ℕ) (c p : ℝ[X]) (hp : p.coeff d = 1) :
    pairing (homogeneousValue d c 1 0) (homogeneousValue d p 1 0) = c.coeff d := by
  rw [homogeneousValue_at_infinity, homogeneousValue_at_infinity, hp]
  simp only [Complex.ofReal_one, one_mul, mul_one]
  calc
    _ = pairing (Complex.I^d*(c.coeff d : ℂ)) (Complex.I^d*1) := by
      congr 1 <;> ring
    _ = Complex.normSq (Complex.I^d)*pairing (c.coeff d : ℂ) 1 :=
      pairing_common_factor _ _ _
    _ = _ := by simp [pairing]

/-- Finite homogeneous pairings have exactly the same sign as the original
real-part numerator: the scaling factor is an even power of y. -/
theorem homogeneous_pairing_finite
    (d : ℕ) (c p : ℝ[X]) (hc : c.natDegree ≤ d) (hp : p.natDegree ≤ d)
    (x y : ℝ) (hy : y ≠ 0) :
    pairing (homogeneousValue d c x y) (homogeneousValue d p x y) =
      y^(2*d)*pairing (value c ((x/y : ℝ)*Complex.I))
        (value p ((x/y : ℝ)*Complex.I)) := by
  rw [homogeneousValue_finite d c hc x y hy,
    homogeneousValue_finite d p hp x y hy, pairing_common_factor]
  congr 1
  simp [mul_pow, pow_mul, mul_comm 2 d, pow_two]

/-- A continuous compactification of every real frequency and both ends at infinity. -/
def compactPairing (d : ℕ) (c p : ℝ[X]) (u : ℝ) : ℝ :=
  pairing (homogeneousValue d c u (1-|u|)) (homogeneousValue d p u (1-|u|))

theorem compactPairing_continuous (d : ℕ) (c p : ℝ[X]) :
    Continuous (compactPairing d c p) := by
  unfold compactPairing pairing
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, sub_neg_eq_add]
  unfold homogeneousValue
  fun_prop

theorem homogeneous_pairing_any_infinity
    (d : ℕ) (c p : ℝ[X]) (x : ℝ) :
    pairing (homogeneousValue d c x 0) (homogeneousValue d p x 0) =
      x^(2*d)*(c.coeff d*p.coeff d) := by
  rw [homogeneousValue_at_infinity, homogeneousValue_at_infinity]
  have h := pairing_common_factor (c.coeff d : ℂ) (p.coeff d : ℂ) ((x*Complex.I)^d)
  rw [mul_comm ((x*Complex.I)^d) (c.coeff d : ℂ),
    mul_comm ((x*Complex.I)^d) (p.coeff d : ℂ)] at h
  rw [h]
  simp [pairing, mul_pow, pow_mul, mul_comm 2 d, pow_two]

/-- Compact positivity includes the leading coefficient condition and exactly
matches strict real-part positivity at every finite frequency. -/
theorem compact_positivity_iff
    (d : ℕ) (c p : ℝ[X]) (hc : c.natDegree ≤ d)
    (hp : p.Monic) (hdp : p.natDegree = d) (hstable : Stable p) :
    (∀ u : ℝ, u ∈ Icc (-1 : ℝ) 1 → 0 < compactPairing d c p u) ↔
      0 < c.coeff d ∧ FrequencyPositive c p := by
  have htop : p.coeff d = 1 := by simpa [← hdp] using hp.coeff_natDegree
  constructor
  · intro h
    have hlead := h 1 (by constructor <;> norm_num)
    have hlead' : 0 < c.coeff d := by
      simpa [compactPairing, homogeneous_pairing_at_infinity d c p htop] using hlead
    refine ⟨hlead', ?_⟩
    intro w
    let R : ℝ := 1+|w|
    have hR : 0 < R := by dsimp [R]; positivity
    let u : ℝ := w/R
    have habs : |u| = |w|/R := by simp [u,abs_div,abs_of_pos hR]
    have hu : |u| < 1 := by rw [habs]; exact (div_lt_one hR).mpr (by dsimp [R]; linarith)
    have hy : 1-|u| = 1/R := by rw [habs]; dsimp [R]; field_simp
    have hypos : 0 < 1-|u| := sub_pos.mpr hu
    have harg : u/(1-|u|) = w := by rw [hy]; dsimp [u]; field_simp
    have hpair := h u ⟨(abs_lt.mp hu).1.le,(abs_lt.mp hu).2.le⟩
    rw [compactPairing, homogeneous_pairing_finite d c p hc hdp.le _ _ (ne_of_gt hypos),
      harg] at hpair
    apply (positive_quotient_iff _ _ (hstable _ (by simp))).mpr
    exact (mul_pos_iff_of_pos_left (pow_pos hypos _)).mp hpair
  · rintro ⟨hlead,hfreq⟩ u hu
    have hy : 0 ≤ 1-|u| := sub_nonneg.mpr (abs_le.mpr hu)
    by_cases hzero : 1-|u| = 0
    · have habs : |u| = 1 := by linarith
      have hsq : u^2 = 1 := by
        have heq := congrArg (fun x : ℝ => x^2) habs
        simpa using heq
      rw [compactPairing, hzero, homogeneous_pairing_any_infinity, htop]
      simpa [pow_mul,hsq] using hlead
    · have hypos : 0 < 1-|u| := lt_of_le_of_ne hy (Ne.symm hzero)
      rw [compactPairing, homogeneous_pairing_finite d c p hc hdp.le _ _ hzero]
      have hnz : value p (((u/(1-|u|) : ℝ) : ℂ)*Complex.I) ≠ 0 :=
        stable_axis_ne_zero hstable _
      exact mul_pos (pow_pos hypos _)
        ((positive_quotient_iff _ _ hnz).mp (hfreq (u/(1-|u|))))

theorem homogeneousValue_add (d : ℕ) (p q : ℝ[X]) (x y : ℝ) :
    homogeneousValue d (p+q) x y = homogeneousValue d p x y+homogeneousValue d q x y := by
  simp only [homogeneousValue, Polynomial.coeff_add, Complex.ofReal_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem homogeneousValue_scale (d : ℕ) (p : ℝ[X]) (r x y : ℝ) :
    homogeneousValue d (C r*p) x y = (r : ℂ)*homogeneousValue d p x y := by
  simp only [homogeneousValue, Polynomial.coeff_C_mul, Complex.ofReal_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem compactPairing_add (d : ℕ) (c₁ c₂ p : ℝ[X]) (u : ℝ) :
    compactPairing d (c₁+c₂) p u = compactPairing d c₁ p u+compactPairing d c₂ p u := by
  simp [compactPairing, homogeneousValue_add, pairing, add_mul, Complex.add_re]

theorem compactPairing_scale (d : ℕ) (c p : ℝ[X]) (r u : ℝ) :
    compactPairing d (C r*c) p u = r*compactPairing d c p u := by
  simp only [compactPairing]
  rw [homogeneousValue_scale]
  simp [pairing, Complex.mul_re, Complex.mul_im]
  ring

theorem frequencyPositive_scale {c p : ℝ[X]} (h : FrequencyPositive c p)
    (r : ℝ) (hr : 0 < r) : FrequencyPositive (C r*c) p := by
  intro w
  have heq : value (C r*c) (w*Complex.I) = (r : ℂ)*value c (w*Complex.I) := by
    simp [value]
  rw [heq, mul_div_assoc, Complex.mul_re]
  simpa only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using mul_pos hr (h w)

/-- A degree-bounded feasible numerator automatically has the exact degree and
can be normalized without changing its endpoint SPR properties. -/
theorem normalize_common_numerator
    (d : ℕ) (c a b : ℝ[X]) (hc : c.natDegree ≤ d) (hlead : 0 < c.coeff d)
    (hA : SPR c a) (hB : SPR c b) :
    ∃ β : ℝ[X], β.Monic ∧ β.natDegree = d ∧ SPR β a ∧ SPR β b := by
  have hdeg : c.natDegree = d :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hc (ne_of_gt hlead)
  have htop : c.leadingCoeff = c.coeff d := by rw [← hdeg,Polynomial.coeff_natDegree]
  let r : ℝ := (c.coeff d)⁻¹
  have hr : 0 < r := inv_pos.mpr hlead
  refine ⟨C r*c, ?_, ?_, ?_, ?_⟩
  · apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [htop]
    exact inv_mul_cancel₀ (ne_of_gt hlead)
  · rw [Polynomial.natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr (ne_of_gt hr)),hdeg]
  · exact ⟨hA.1,frequencyPositive_scale hA.2 r hr⟩
  · exact ⟨hB.1,frequencyPositive_scale hB.2 r hr⟩

/-- An exact compact reformulation of the arbitrary-degree synthesis problem.
No synthesis assertion is assumed or hidden in the reformulation. -/
theorem common_numerator_iff_compact_feasible
    (d : ℕ) (a b : ℝ[X]) (ha : HurwitzClass d a) (hb : HurwitzClass d b) :
    (∃ c : ℝ[X], c.Monic ∧ c.natDegree = d ∧ SPR c a ∧ SPR c b) ↔
    (∃ c : ℝ[X], c.natDegree ≤ d ∧
      (∀ u : ℝ, u ∈ Icc (-1 : ℝ) 1 → 0 < compactPairing d c a u) ∧
      (∀ u : ℝ, u ∈ Icc (-1 : ℝ) 1 → 0 < compactPairing d c b u)) := by
  constructor
  · rintro ⟨c,hmonic,hdeg,hA,hB⟩
    have htop : 0 < c.coeff d := by rw [← hdeg,hmonic.coeff_natDegree]; norm_num
    exact ⟨c,hdeg.le,
      (compact_positivity_iff d c a hdeg.le ha.1 ha.2.1 ha.2.2).mpr ⟨htop,hA.2⟩,
      (compact_positivity_iff d c b hdeg.le hb.1 hb.2.1 hb.2.2).mpr ⟨htop,hB.2⟩⟩
  · rintro ⟨c,hdeg,hA,hB⟩
    have hA' := (compact_positivity_iff d c a hdeg ha.1 ha.2.1 ha.2.2).mp hA
    have hB' := (compact_positivity_iff d c b hdeg hb.1 hb.2.1 hb.2.2).mp hB
    exact normalize_common_numerator d c a b hdeg hA'.1 ⟨ha.2.2,hA'.2⟩ ⟨hb.2.2,hB'.2⟩

abbrev CoefficientSpace (d : ℕ) := Fin (d+1) → ℝ

/-- Ascending coefficients, with all d+1 coefficients free during separation. -/
def polynomialFrom (d : ℕ) (v : CoefficientSpace d) : ℝ[X] :=
  ∑ k : Fin (d+1), Polynomial.monomial k.val (v k)

theorem polynomialFrom_coefficient (d : ℕ) (v : CoefficientSpace d) (k : Fin (d+1)) :
    (polynomialFrom d v).coeff k.val = v k := by
  classical
  simp only [polynomialFrom, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  simp only [← Fin.ext_iff]
  simp

theorem polynomialFrom_degree (d : ℕ) (v : CoefficientSpace d) :
    (polynomialFrom d v).natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp only [polynomialFrom, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (by have := j.isLt; omega)]

theorem polynomialFrom_coefficients (d : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ d) :
    polynomialFrom d (fun k => p.coeff k.val) = p := by
  ext k
  by_cases hk : k ≤ d
  · exact polynomialFrom_coefficient d _ ⟨k,by omega⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (polynomialFrom_degree d _) (by omega)),
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (by omega))]

theorem compactPairing_sum {ι : Type*} (d : ℕ) (s : Finset ι)
    (c : ι → ℝ[X]) (p : ℝ[X]) (u : ℝ) :
    compactPairing d (∑ i ∈ s, c i) p u = ∑ i ∈ s, compactPairing d (c i) p u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [compactPairing, homogeneousValue, pairing]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,compactPairing_add,ih]

/-- Coefficient directions of each compact frequency constraint. -/
def feature (d : ℕ) (p : ℝ[X]) (u : ℝ) : CoefficientSpace d :=
  fun k => compactPairing d (X^k.val) p u

theorem feature_continuous (d : ℕ) (p : ℝ[X]) : Continuous (feature d p) := by
  apply continuous_pi
  intro k
  exact compactPairing_continuous d (X^k.val) p

theorem pairing_feature_identity (d : ℕ) (v : CoefficientSpace d) (p : ℝ[X]) (u : ℝ) :
    compactPairing d (polynomialFrom d v) p u = ∑ k : Fin (d+1), v k*feature d p u k := by
  unfold polynomialFrom
  rw [compactPairing_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Polynomial.C_mul_X_pow_eq_monomial,compactPairing_scale]
  rfl

def dotFunctional (d : ℕ) (v : CoefficientSpace d) : CoefficientSpace d →L[ℝ] ℝ :=
  ∑ k : Fin (d+1), v k • ContinuousLinearMap.proj k

theorem dotFunctional_apply (d : ℕ) (v x : CoefficientSpace d) :
    dotFunctional d v x = ∑ k : Fin (d+1), v k*x k := by
  simp [dotFunctional,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]

theorem functional_coordinates (d : ℕ) (f : CoefficientSpace d →L[ℝ] ℝ)
    (x : CoefficientSpace d) :
    f x = ∑ k : Fin (d+1), f (Pi.single k 1)*x k := by
  classical
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hsingle : Pi.single k (x k) = (x k) • (Pi.single k (1 : ℝ) : CoefficientSpace d) := by
    ext j
    by_cases h : j = k
    · subst j
      simp
    · simp [Pi.single_eq_of_ne h]
  rw [hsingle,map_smul]
  simp only [smul_eq_mul,mul_comm]

/-- The compact union of endpoint frequency features. -/
def featureSet (d : ℕ) (a b : ℝ[X]) : Set (CoefficientSpace d) :=
  (feature d a '' Icc (-1 : ℝ) 1) ∪ (feature d b '' Icc (-1 : ℝ) 1)

theorem featureSet_compact (d : ℕ) (a b : ℝ[X]) : IsCompact (featureSet d a b) :=
  (isCompact_Icc.image (feature_continuous d a)).union
    (isCompact_Icc.image (feature_continuous d b))

theorem featureSet_nonempty (d : ℕ) (a b : ℝ[X]) : (featureSet d a b).Nonempty := by
  refine ⟨feature d a 0,Or.inl ?_⟩
  exact ⟨0,by constructor <;> norm_num,rfl⟩

/-- Compactness makes pointwise strict separation equivalent to exclusion of
the origin from the closed convex hull, with no unproved synthesis step. -/
theorem strict_separation_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (hS : IsCompact S) (hne : S.Nonempty) :
    (∃ f : E →L[ℝ] ℝ, ∀ x ∈ S, 0 < f x) ↔ 0 ∉ closedConvexHull ℝ S := by
  constructor
  · rintro ⟨f,hf⟩ hzero
    obtain ⟨x,hx,hmin⟩ := hS.exists_isMinOn hne f.continuous.continuousOn
    have hhalf : closedConvexHull ℝ S ⊆ {y | f x ≤ f y} := by
      apply closedConvexHull_min
      · intro y hy
        exact hmin hy
      · exact (convex_Ici (f x)).linear_preimage f.toLinearMap
      · exact isClosed_le continuous_const f.continuous
    have hle := hhalf hzero
    have hpos := hf x hx
    simp only [Set.mem_setOf_eq,map_zero] at hle
    linarith
  · intro hzero
    obtain ⟨f,ε,hε,hf⟩ := geometric_hahn_banach_point_closed
      (convex_closedConvexHull (𝕜 := ℝ) (s := S)) isClosed_closedConvexHull hzero
    refine ⟨f,fun x hx => ?_⟩
    have hpos : 0 < ε := by simpa only [map_zero] using hε
    exact hpos.trans (hf x (subset_closedConvexHull hx))

/-- The full common-numerator existence question is now an exact separation
problem for an explicitly defined finite-dimensional frequency feature set. -/
theorem synthesis_iff_origin_excluded
    (d : ℕ) (a b : ℝ[X]) (ha : HurwitzClass d a) (hb : HurwitzClass d b) :
    (∃ c : ℝ[X], c.Monic ∧ c.natDegree = d ∧ SPR c a ∧ SPR c b) ↔
      0 ∉ closedConvexHull ℝ (featureSet d a b) := by
  rw [← strict_separation_iff _ (featureSet_compact d a b) (featureSet_nonempty d a b),
    common_numerator_iff_compact_feasible d a b ha hb]
  constructor
  · rintro ⟨c,hdeg,hA,hB⟩
    let v : CoefficientSpace d := fun k => c.coeff k.val
    have hc : polynomialFrom d v = c := polynomialFrom_coefficients d c hdeg
    refine ⟨dotFunctional d v, ?_⟩
    intro x hx
    rcases hx with ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩
    · simpa only [dotFunctional_apply,← pairing_feature_identity,hc] using hA u hu
    · simpa only [dotFunctional_apply,← pairing_feature_identity,hc] using hB u hu
  · rintro ⟨f,hf⟩
    let v : CoefficientSpace d := fun k => f (Pi.single k 1)
    refine ⟨polynomialFrom d v,polynomialFrom_degree d v,?_,?_⟩
    · intro u hu
      rw [pairing_feature_identity]
      exact (functional_coordinates d f _).symm ▸ hf _ (Or.inl ⟨u,hu,rfl⟩)
    · intro u hu
      rw [pairing_feature_identity]
      exact (functional_coordinates d f _).symm ▸ hf _ (Or.inr ⟨u,hu,rfl⟩)

/-! ## 3. 有限接触证书与临界支撑多项式 -/

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

/-- Failure of the full same-degree synthesis problem has an actual finite
positive barycentric witness, not just a limit of approximate witnesses. -/
theorem synthesis_failure_finite_witness
    (d : ℕ) (a b : ℝ[X]) (ha : HurwitzClass d a) (hb : HurwitzClass d b)
    (hfail : ¬ ∃ c : ℝ[X], c.Monic ∧ c.natDegree = d ∧ SPR c a ∧ SPR c b) :
    ∃ (ι : Type) (_ : Fintype ι) (z : ι → CoefficientSpace d) (w : ι → ℝ),
      (∀ i, z i ∈ featureSet d a b) ∧ (∀ i, 0 < w i) ∧
      (∑ i, w i) = 1 ∧ (∑ i, w i • z i) = 0 := by
  have hzero : (0 : CoefficientSpace d) ∈ closedConvexHull ℝ (featureSet d a b) := by
    by_contra h
    exact hfail ((synthesis_iff_origin_excluded d a b ha hb).mpr h)
  rw [closedConvexHull_eq_convexHull_of_compact _ (featureSet_compact d a b)] at hzero
  obtain ⟨ι,hι,z,w,hz,_,hw,hsum,hcombo⟩ := eq_pos_convex_span_of_mem_convexHull hzero
  exact ⟨ι,hι,z,w,(fun i => hz ⟨i,rfl⟩),hw,hsum,hcombo⟩

/-- No extra tangency assumption is needed: every positively weighted atom
must be a zero of every nonnegative supporting functional. -/
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

/-- At a transition from strict feasibility to failure, a unit vector supports
all frequency constraints nonnegatively. This uses a continuous max-min on a
compact unit sphere, so the support cannot collapse to the zero vector. -/
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

theorem compactPairing_denominator_blend (d : ℕ) (c a b : ℝ[X]) (t u : ℝ) :
    compactPairing d c (blend a b t) u =
      (1-t)*compactPairing d c a u+t*compactPairing d c b u := by
  have hh (x y : ℝ) : homogeneousValue d (blend a b t) x y =
      ((1-t : ℝ) : ℂ)*homogeneousValue d a x y+(t : ℂ)*homogeneousValue d b x y := by
    rw [blend,homogeneousValue_add,homogeneousValue_scale,homogeneousValue_scale]
  simp only [compactPairing,hh,pairing_blend]

theorem feature_blend (d : ℕ) (a b : ℝ[X]) (t u : ℝ) :
    feature d (blend a b t) u = (1-t) • feature d a u+t • feature d b u := by
  ext k
  exact compactPairing_denominator_blend d (X^k.val) a b t u

private def testDomain : Set (ℝ × ℝ) := ({0,1} : Set ℝ) ×ˢ Icc (-1 : ℝ) 1

private theorem testDomain_compact : IsCompact testDomain :=
  (isCompact_singleton.insert (0 : ℝ)).prod isCompact_Icc

private theorem testDomain_nonempty : testDomain.Nonempty := by
  exact ⟨(0,0),by simp [testDomain]⟩

def testFeature (d : ℕ) (a b : ℝ[X]) (t : ℝ) (su : ℝ × ℝ) : CoefficientSpace d :=
  (1-su.1) • feature d a su.2+
    su.1 • ((1-t) • feature d a su.2+t • feature d b su.2)

def supportTest (d : ℕ) (a b : ℝ[X]) (t : ℝ) (v : CoefficientSpace d) (su : ℝ × ℝ) : ℝ :=
  dotFunctional d v (testFeature d a b t su)

theorem testFeature_left (d : ℕ) (a b : ℝ[X]) (t u : ℝ) :
    testFeature d a b t (0,u) = feature d a u := by simp [testFeature]

theorem testFeature_right (d : ℕ) (a b : ℝ[X]) (t u : ℝ) :
    testFeature d a b t (1,u) = feature d (blend a b t) u := by
  simp [testFeature,feature_blend]

theorem supportTest_scale (d : ℕ) (a b : ℝ[X]) (t r : ℝ)
    (v : CoefficientSpace d) (su : ℝ × ℝ) :
    supportTest d a b t (r • v) su = r*supportTest d a b t v su := by
  simp only [supportTest,dotFunctional_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem supportTest_continuous (d : ℕ) (a b : ℝ[X]) :
    Continuous (fun x : (ℝ × CoefficientSpace d) × (ℝ × ℝ) =>
      supportTest d a b x.1.1 x.1.2 x.2) := by
  simp only [supportTest,dotFunctional_apply]
  apply continuous_finset_sum
  intro k _
  have hA : Continuous (fun x : (ℝ × CoefficientSpace d) × (ℝ × ℝ) => feature d a x.2.2 k) :=
    (compactPairing_continuous d (X^k.val) a).comp (continuous_snd.comp continuous_snd)
  have hB : Continuous (fun x : (ℝ × CoefficientSpace d) × (ℝ × ℝ) => feature d b x.2.2 k) :=
    (compactPairing_continuous d (X^k.val) b).comp (continuous_snd.comp continuous_snd)
  simp only [testFeature,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  fun_prop

theorem supportTest_left (d : ℕ) (a b : ℝ[X]) (t u : ℝ) (v : CoefficientSpace d) :
    supportTest d a b t v (0,u) = compactPairing d (polynomialFrom d v) a u := by
  rw [supportTest,testFeature_left,dotFunctional_apply,pairing_feature_identity]

theorem supportTest_right (d : ℕ) (a b : ℝ[X]) (t u : ℝ) (v : CoefficientSpace d) :
    supportTest d a b t v (1,u) = compactPairing d (polynomialFrom d v) (blend a b t) u := by
  rw [supportTest,testFeature_right,dotFunctional_apply,pairing_feature_identity]

theorem supportTest_positive_iff (d : ℕ) (a b : ℝ[X]) (t : ℝ) (v : CoefficientSpace d) :
    (∀ su ∈ testDomain, 0 < supportTest d a b t v su) ↔
    (∀ u ∈ Icc (-1 : ℝ) 1, 0 < compactPairing d (polynomialFrom d v) a u) ∧
    (∀ u ∈ Icc (-1 : ℝ) 1, 0 < compactPairing d (polynomialFrom d v) (blend a b t) u) := by
  constructor
  · intro h
    constructor
    · intro u hu
      simpa only [supportTest_left] using h (0,u) ⟨by simp,hu⟩
    · intro u hu
      simpa only [supportTest_right] using h (1,u) ⟨by simp,hu⟩
  · rintro ⟨hA,hB⟩ ⟨s,u⟩ ⟨hs,hu⟩
    rcases (show s = 0 ∨ s = 1 by simpa using hs) with rfl | rfl
    · simpa only [supportTest_left] using hA u hu
    · simpa only [supportTest_right] using hB u hu

theorem supportTest_feasible_iff_common (d : ℕ) (a b : ℝ[X]) (t : ℝ)
    (ha : HurwitzClass d a) (ht : HurwitzClass d (blend a b t)) :
    (∃ v : CoefficientSpace d, ∀ su ∈ testDomain, 0 < supportTest d a b t v su) ↔
    (∃ c : ℝ[X], c.Monic ∧ c.natDegree = d ∧ SPR c a ∧ SPR c (blend a b t)) := by
  rw [common_numerator_iff_compact_feasible d a (blend a b t) ha ht]
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨polynomialFrom d v,polynomialFrom_degree d v,
      (supportTest_positive_iff d a b t v).mp hv⟩
  · rintro ⟨c,hdeg,hA,hB⟩
    let v : CoefficientSpace d := fun k => c.coeff k.val
    have hc : polynomialFrom d v = c := polynomialFrom_coefficients d c hdeg
    refine ⟨v,(supportTest_positive_iff d a b t v).mpr ?_⟩
    simpa only [hc] using And.intro hA hB

/-- The exact finite contact data used in the remaining sufficiency argument. -/
structure CriticalCertificate (d : ℕ) (a b : ℝ[X]) where
  support : CoefficientSpace d
  support_norm : ‖support‖ = 1
  support_nonnegative : ∀ x ∈ featureSet d a b, 0 ≤ dotFunctional d support x
  count : ℕ
  point : Fin count → CoefficientSpace d
  weight : Fin count → ℝ
  point_mem : ∀ i, point i ∈ featureSet d a b
  weight_pos : ∀ i, 0 < weight i
  weight_sum : ∑ i, weight i = 1
  balance : ∑ i, weight i • point i = 0
  contact : ∀ i, dotFunctional d support (point i) = 0

/-- A failed stable segment produces a nonzero weak support and an actual
finite positive contact certificate at some parameter on that segment. -/
theorem critical_certificate_of_failed_segment
    (d : ℕ) (a b : ℝ[X])
    (hstable : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → HurwitzClass d (blend a b t))
    (hfail : ¬ ∃ c : ℝ[X], c.Monic ∧ c.natDegree = d ∧ SPR c a ∧ SPR c b) :
    ∃ t ∈ Icc (0 : ℝ) 1, Nonempty (CriticalCertificate d a (blend a b t)) := by
  classical
  have ha : HurwitzClass d a := by simpa [blend] using hstable 0 (by constructor <;> norm_num)
  have hb : HurwitzClass d b := by simpa [blend] using hstable 1 (by constructor <;> norm_num)
  have hself : FrequencyPositive a a := by
    intro w
    rw [div_self (stable_axis_ne_zero ha.2.2 w)]
    norm_num
  have hstart : ∃ v : CoefficientSpace d, ∀ su ∈ testDomain, 0 < supportTest d a b 0 v su := by
    apply (supportTest_feasible_iff_common d a b 0 ha (hstable 0 (by constructor <;> norm_num))).mpr
    exact ⟨a,ha.1,ha.2.1,⟨ha.2.2,hself⟩,by simpa [blend] using And.intro ha.2.2 hself⟩
  have hfinish : ¬ ∃ v : CoefficientSpace d, ∀ su ∈ testDomain, 0 < supportTest d a b 1 v su := by
    intro h
    have hcommon := (supportTest_feasible_iff_common d a b 1 ha
      (hstable 1 (by constructor <;> norm_num))).mp h
    exact hfail (by simpa [blend] using hcommon)
  obtain ⟨t,ht,v,hv,hsupport,hfailed⟩ := weak_support_at_transition testDomain testDomain_compact
    testDomain_nonempty (supportTest d a b) (supportTest_continuous d a b)
    (supportTest_scale d a b) hstart hfinish
  have hpt := hstable t ht
  have hweak : ∀ x ∈ featureSet d a (blend a b t), 0 ≤ dotFunctional d v x := by
    rintro x (⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩)
    · simpa only [supportTest,testFeature_left] using hsupport (0,u) ⟨by simp,hu⟩
    · simpa only [supportTest,testFeature_right] using hsupport (1,u) ⟨by simp,hu⟩
  have hfail' : ¬ ∃ c : ℝ[X], c.Monic ∧ c.natDegree = d ∧ SPR c a ∧ SPR c (blend a b t) := by
    intro h
    exact hfailed ((supportTest_feasible_iff_common d a b t ha hpt).mpr h)
  obtain ⟨ι,hι,z,w,hz,hw,hsum,hbalance⟩ := synthesis_failure_finite_witness d a (blend a b t) ha hpt hfail'
  letI : Fintype ι := hι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hcontacts := balance_forces_contacts z w (dotFunctional d v) hw hbalance
    (fun i => hweak (z i) (hz i))
  refine ⟨t,ht,⟨{
    support := v
    support_norm := hv
    support_nonnegative := hweak
    count := Fintype.card ι
    point := fun i => z (e.symm i)
    weight := fun i => w (e.symm i)
    point_mem := fun i => hz (e.symm i)
    weight_pos := fun i => hw (e.symm i)
    weight_sum := (e.symm.sum_comp w).trans hsum
    balance := (e.symm.sum_comp (fun i => w i • z i)).trans hbalance
    contact := fun i => hcontacts (e.symm i)
  }⟩⟩

def CriticalCertificate.numerator {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) : ℝ[X] := polynomialFrom d Crt.support

theorem CriticalCertificate.numerator_degree {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) : Crt.numerator.natDegree ≤ d :=
  polynomialFrom_degree d Crt.support

theorem CriticalCertificate.numerator_ne_zero {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) : Crt.numerator ≠ 0 := by
  intro hz
  have hv : Crt.support = 0 := by
    funext k
    have h := polynomialFrom_coefficient d Crt.support k
    rw [show polynomialFrom d Crt.support = 0 from hz,Polynomial.coeff_zero] at h
    exact h.symm
  have hn := Crt.support_norm
  simp [hv] at hn

theorem CriticalCertificate.compact_nonnegative {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) :
    (∀ u ∈ Icc (-1 : ℝ) 1, 0 ≤ compactPairing d Crt.numerator a u) ∧
    (∀ u ∈ Icc (-1 : ℝ) 1, 0 ≤ compactPairing d Crt.numerator b u) := by
  constructor
  · intro u hu
    have h := Crt.support_nonnegative _ (Or.inl ⟨u,hu,rfl⟩)
    simpa only [dotFunctional_apply,← pairing_feature_identity] using h
  · intro u hu
    have h := Crt.support_nonnegative _ (Or.inr ⟨u,hu,rfl⟩)
    simpa only [dotFunctional_apply,← pairing_feature_identity] using h

theorem finite_frequency_coordinates (w : ℝ) :
    ∃ u ∈ Icc (-1 : ℝ) 1, 0 < 1-|u| ∧ u/(1-|u|) = w := by
  let R : ℝ := 1+|w|
  have hR : 0 < R := by dsimp [R]; positivity
  let u : ℝ := w/R
  have habs : |u| = |w|/R := by simp [u,abs_div,abs_of_pos hR]
  have hu : |u| < 1 := by rw [habs]; exact (div_lt_one hR).mpr (by dsimp [R]; linarith)
  have hy : 1-|u| = 1/R := by rw [habs]; dsimp [R]; field_simp
  exact ⟨u,⟨(abs_lt.mp hu).1.le,(abs_lt.mp hu).2.le⟩,sub_pos.mpr hu,
    by rw [hy]; dsimp [u]; field_simp⟩

theorem boundary_nonnegative_of_compact
    (d : ℕ) (c p : ℝ[X]) (hc : c.natDegree ≤ d) (hp : p.natDegree ≤ d)
    (hcompact : ∀ u ∈ Icc (-1 : ℝ) 1, 0 ≤ compactPairing d c p u) :
    ∀ w : ℝ, 0 ≤ (value c (w*Complex.I)/value p (w*Complex.I)).re := by
  intro w
  obtain ⟨u,hu,hy,harg⟩ := finite_frequency_coordinates w
  have h := hcompact u hu
  rw [compactPairing,homogeneous_pairing_finite d c p hc hp _ _ (ne_of_gt hy),harg] at h
  have hpair : 0 ≤ pairing (value c (w*Complex.I)) (value p (w*Complex.I)) :=
    (mul_nonneg_iff_of_pos_left (pow_pos hy _)).mp h
  rw [real_quotient]
  exact div_nonneg hpair (Complex.normSq_nonneg _)

theorem CriticalCertificate.boundary_nonnegative {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (ha : a.natDegree = d) (hb : b.natDegree = d) :
    (∀ w : ℝ, 0 ≤ (value Crt.numerator (w*Complex.I)/value a (w*Complex.I)).re) ∧
    (∀ w : ℝ, 0 ≤ (value Crt.numerator (w*Complex.I)/value b (w*Complex.I)).re) :=
  ⟨boundary_nonnegative_of_compact d _ _ Crt.numerator_degree ha.le Crt.compact_nonnegative.1,
    boundary_nonnegative_of_compact d _ _ Crt.numerator_degree hb.le Crt.compact_nonnegative.2⟩

theorem CriticalCertificate.top_coefficient_nonnegative {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (ha : a.Monic) (hda : a.natDegree = d) :
    0 ≤ Crt.numerator.coeff d := by
  have htop : a.coeff d = 1 := by simpa [← hda] using ha.coeff_natDegree
  have h := Crt.compact_nonnegative.1 1 (by constructor <;> norm_num)
  simpa [compactPairing,homogeneous_pairing_at_infinity d Crt.numerator a htop] using h

/-! ## 4. 弱正实性与虚轴零点的一重性 -/

/-- Polynomial pullback from the right half-plane to the unit disk. -/
def diskPolynomial (d : ℕ) (p : ℝ[X]) : ℂ[X] :=
  ∑ k ∈ Finset.range (d+1), C (p.coeff k : ℂ)*(1+X)^k*(1-X)^(d-k)

theorem diskPolynomial_at_one (d : ℕ) (p : ℝ[X]) :
    (diskPolynomial d p).eval 1 = (p.coeff d : ℂ)*(2 : ℂ)^d := by
  classical
  simp only [diskPolynomial,Polynomial.eval_finset_sum,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X]
  rw [Finset.sum_eq_single d]
  · norm_num
  · intro k hk hkd
    have hpos : 0 < d-k := by have := Finset.mem_range.mp hk; omega
    simp [zero_pow (Nat.ne_of_gt hpos)]
  · simp

theorem diskPolynomial_finite (d : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ d)
    (z : ℂ) (hz : z ≠ 1) :
    (diskPolynomial d p).eval z = (1-z)^d*value p ((1+z)/(1-z)) := by
  have hden : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  simp only [diskPolynomial,Polynomial.eval_finset_sum,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X]
  rw [value,Polynomial.aeval_def,
    Polynomial.eval₂_eq_sum_range' (algebraMap ℝ ℂ) (by omega : p.natDegree < d+1)]
  simp only [Complex.coe_algebraMap]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ d := by have := Finset.mem_range.mp hk; omega
  have hpow : (1-z)^d*((1+z)/(1-z))^k = (1+z)^k*(1-z)^(d-k) := by
    rw [div_pow,show d = k+(d-k) by omega,pow_add]
    field_simp
    ring
  calc
    _ = (p.coeff k : ℂ)*((1+z)^k*(1-z)^(d-k)) := by ring
    _ = (p.coeff k : ℂ)*((1-z)^d*((1+z)/(1-z))^k) := by rw [hpow]
    _ = _ := by ring

theorem cayley_real_part (z : ℂ) :
    ((1+z)/(1-z)).re = (1-Complex.normSq z)/Complex.normSq (1-z) := by
  rw [Complex.div_re]
  simp [Complex.normSq_apply]
  ring

theorem cayley_real_part_nonnegative (z : ℂ) (hz : ‖z‖ ≤ 1) :
    0 ≤ ((1+z)/(1-z)).re := by
  rw [cayley_real_part]
  have hsq : Complex.normSq z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  exact div_nonneg (sub_nonneg.mpr hsq) (Complex.normSq_nonneg _)

theorem diskPolynomial_denominator_nonzero (d : ℕ) (p : ℝ[X])
    (hp : HurwitzClass d p) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (diskPolynomial d p).eval z ≠ 0 := by
  by_cases hzone : z = 1
  · subst z
    rw [diskPolynomial_at_one,← hp.2.1,hp.1.coeff_natDegree]
    simp
  · rw [diskPolynomial_finite d p hp.2.1.le z hzone]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hzone)))
      (hp.2.2 _ (cayley_real_part_nonnegative z hz))

theorem real_part_nonnegative_on_disk
    (f : ℂ → ℂ) (hf : DiffContOnCl ℂ f (Metric.ball 0 1))
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (f z).re) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → 0 ≤ (f z).re := by
  let g : ℂ → ℂ := fun z => Complex.exp (-f z)
  have hg : DiffContOnCl ℂ g (Metric.ball 0 1) :=
    Complex.differentiable_exp.comp_diffContOnCl hf.neg
  intro z hz
  have hnorm : ‖g z‖ ≤ 1 := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hg
    · intro w hw
      have hsphere := Metric.frontier_ball_subset_sphere hw
      have hnormw : ‖w‖ = 1 := by simpa [Metric.mem_sphere,dist_zero_right] using hsphere
      have hreal := hboundary w hnormw
      simp only [g,Complex.norm_exp,Complex.neg_re,Real.exp_le_one_iff]
      linarith
    · rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
      simpa [Metric.mem_closedBall,dist_zero_right] using hz
  have hreal : -(f z).re ≤ 0 := by
    simpa only [g,Complex.norm_exp,Complex.neg_re,Real.exp_le_one_iff] using hnorm
  linarith

theorem disk_quotient_finite (d : ℕ) (c p : ℝ[X])
    (hc : c.natDegree ≤ d) (hp : p.natDegree ≤ d) (z : ℂ) (hz : z ≠ 1) :
    (diskPolynomial d c).eval z/(diskPolynomial d p).eval z =
      value c ((1+z)/(1-z))/value p ((1+z)/(1-z)) := by
  rw [diskPolynomial_finite d c hc z hz,diskPolynomial_finite d p hp z hz]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hz)))

theorem cayley_real_part_on_circle (z : ℂ) (hz : ‖z‖ = 1) :
    ((1+z)/(1-z)).re = 0 := by
  rw [cayley_real_part,Complex.normSq_eq_norm_sq,hz]
  norm_num

theorem disk_quotient_real_nonnegative
    (d : ℕ) (c p : ℝ[X]) (hc : c.natDegree ≤ d) (hp : HurwitzClass d p)
    (hlead : 0 ≤ c.coeff d)
    (hfreq : ∀ w : ℝ, 0 ≤ (value c (w*Complex.I)/value p (w*Complex.I)).re) :
    ∀ z : ℂ, ‖z‖ ≤ 1 →
      0 ≤ ((diskPolynomial d c).eval z/(diskPolynomial d p).eval z).re := by
  let f : ℂ → ℂ := fun z => (diskPolynomial d c).eval z/(diskPolynomial d p).eval z
  have hf : DiffContOnCl ℂ f (Metric.ball 0 1) := by
    apply DiffContOnCl.mk_ball
    · intro z hz
      apply DifferentiableAt.differentiableWithinAt
      exact ((diskPolynomial d c).differentiable.differentiableAt).div
        ((diskPolynomial d p).differentiable.differentiableAt)
        (diskPolynomial_denominator_nonzero d p hp z
          (by have h := Metric.ball_subset_closedBall hz; simpa [Metric.mem_closedBall,dist_zero_right] using h))
    · apply ContinuousOn.div (diskPolynomial d c).continuous.continuousOn
        (diskPolynomial d p).continuous.continuousOn
      intro z hz
      apply diskPolynomial_denominator_nonzero d p hp z
      simpa [Metric.mem_closedBall,dist_zero_right] using hz
  apply real_part_nonnegative_on_disk f hf
  intro z hz
  by_cases hone : z = 1
  · subst z
    change 0 ≤ ((diskPolynomial d c).eval 1/(diskPolynomial d p).eval 1).re
    rw [diskPolynomial_at_one,diskPolynomial_at_one,
      show p.coeff d = 1 by simpa [← hp.2.1] using hp.1.coeff_natDegree]
    simpa using hlead
  · rw [show f z = _ from disk_quotient_finite d c p hc hp.2.1.le z hone]
    let s : ℂ := (1+z)/(1-z)
    have hs : s.re = 0 := cayley_real_part_on_circle z hz
    have heq : (s.im : ℂ)*Complex.I = s := by
      apply Complex.ext <;> simp [hs]
    simpa only [heq] using hfreq s.im

theorem inverse_cayley (s : ℂ) (hs : 0 ≤ s.re) :
    let z := (s-1)/(s+1)
    ‖z‖ ≤ 1 ∧ z ≠ 1 ∧ (1+z)/(1-z) = s := by
  have hden : s+1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at h'
    linarith
  have hnorm : ‖s-1‖ ≤ ‖s+1‖ := by
    have hsq : ‖s-1‖^2 ≤ ‖s+1‖^2 := by
      rw [Complex.sq_norm,Complex.sq_norm]
      simp [Complex.normSq_apply]
      linarith
    nlinarith [norm_nonneg (s-1),norm_nonneg (s+1)]
  dsimp only
  refine ⟨?_,?_,?_⟩
  · rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hden)).mpr hnorm
  · intro h
    have heq : s-1 = s+1 := (div_eq_one_iff_eq hden).mp h
    have hre := congrArg Complex.re heq
    simp at hre
    linarith
  · field_simp
    ring

/-- Weak positivity on the imaginary axis extends to the full closed right
half-plane through the disk maximum principle. -/
theorem right_half_plane_real_nonnegative
    (d : ℕ) (c p : ℝ[X]) (hc : c.natDegree ≤ d) (hp : HurwitzClass d p)
    (hlead : 0 ≤ c.coeff d)
    (hfreq : ∀ w : ℝ, 0 ≤ (value c (w*Complex.I)/value p (w*Complex.I)).re) :
    ∀ s : ℂ, 0 ≤ s.re → 0 ≤ (value c s/value p s).re := by
  intro s hs
  let z : ℂ := (s-1)/(s+1)
  have hz := inverse_cayley s hs
  have h := disk_quotient_real_nonnegative d c p hc hp hlead hfreq z hz.1
  rw [disk_quotient_finite d c p hc hp.2.1.le z hz.2.1,hz.2.2] at h
  exact h

private def unitRay (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ)*Complex.I)

private theorem unitRay_re (θ : ℝ) : (unitRay θ).re = Real.cos θ := by
  simp [unitRay,Complex.exp_re]

private theorem unitRay_pow (θ : ℝ) (m : ℕ) :
    unitRay θ ^ m = unitRay ((m : ℝ)*θ) := by
  unfold unitRay
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- A nonzero monomial with nonnegative real part in every right-half-plane
direction has order at most one. This is the angular obstruction to multiple
boundary zeros of a nonzero positive-real function. -/
theorem monomial_half_plane_order_bound (A : ℂ) (hA : A ≠ 0) (m : ℕ)
    (hpos : ∀ z : ℂ, 0 < z.re → 0 ≤ (A*z^m).re) : m ≤ 1 := by
  classical
  by_contra hn
  have hm : 2 ≤ m := by omega
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  let θ : ℝ := Real.pi/(2*(m : ℝ))
  have hθpos : 0 < θ := div_pos Real.pi_pos (by positivity)
  have hθlt : θ < Real.pi/2 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2*(m : ℝ))).mpr
    nlinarith [Real.pi_pos]
  have hzre : 0 < (unitRay θ).re := by
    rw [unitRay_re]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hθlt⟩
  have hmθ : (m : ℝ)*θ = Real.pi/2 := by dsimp [θ]; field_simp; ring
  have hzpow : unitRay θ^m = Complex.I := by
    rw [unitRay_pow,hmθ]
    simp [unitRay,Complex.ofReal_div]
  have hneg := hpos (unitRay θ) hzre
  rw [hzpow] at hneg
  have hposIm := hpos (conj (unitRay θ)) (by simpa using hzre)
  have hconjpow : (conj (unitRay θ))^m = -Complex.I := by
    rw [← map_pow,hzpow]
    simp
  rw [hconjpow] at hposIm
  have him : A.im = 0 := by
    simp only [mul_neg,Complex.mul_I_re,Complex.neg_re] at hneg hposIm
    linarith
  have hre : 0 ≤ A.re := by simpa using hpos 1 (by norm_num)
  have hrePos : 0 < A.re := by
    by_contra h
    have heq : A.re = 0 := le_antisymm (le_of_not_gt h) hre
    exact hA (Complex.ext heq him)
  by_cases hm2 : m = 2
  · have h := hpos (1+2*Complex.I) (by norm_num)
    rw [hm2] at h
    norm_num [pow_two,Complex.mul_re,Complex.mul_im,him] at h
    linarith
  · have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast (show 3 ≤ m by omega)
    let φ : ℝ := Real.pi/(m : ℝ)
    have hφpos : 0 < φ := div_pos Real.pi_pos hmpos
    have hφlt : φ < Real.pi/2 := by
      apply (div_lt_iff₀ hmpos).mpr
      nlinarith [Real.pi_pos]
    have hφre : 0 < (unitRay φ).re := by
      rw [unitRay_re]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hφlt⟩
    have hmφ : (m : ℝ)*φ = Real.pi := by dsimp [φ]; field_simp
    have hφpow : unitRay φ^m = -1 := by rw [unitRay_pow,hmφ]; simp [unitRay]
    have h := hpos (unitRay φ) hφre
    rw [hφpow] at h
    simp at h
    linarith

/-- With all complex directions available, a positive-real nonzero monomial
cannot have any positive order. -/
theorem monomial_full_plane_order_zero (A : ℂ) (hA : A ≠ 0) (m : ℕ)
    (hpos : ∀ z : ℂ, 0 ≤ (A*z^m).re) : m = 0 := by
  by_contra hm
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (-A⁻¹) (Nat.pos_of_ne_zero hm)
  have h := hpos z
  rw [hz,mul_neg,mul_inv_cancel₀ hA] at h
  norm_num at h

/-- Extract the leading homogeneous term along any ray that stays inside the
right half-plane. The proof takes a one-sided real limit of the regular
factor, after dividing by a positive real power of the radius. -/
theorem rational_leading_ray_nonnegative
    (P D Q : ℂ[X]) (s₀ v : ℂ) (m : ℕ)
    (hfactor : P = (X-C s₀)^m*Q) (hD : D.eval s₀ ≠ 0)
    (hweak : ∀ s : ℂ, 0 ≤ s.re → 0 ≤ (P.eval s/D.eval s).re)
    (hregion : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 ≤ (s₀+(r : ℂ)*v).re) :
    0 ≤ ((Q.eval s₀/D.eval s₀)*v^m).re := by
  have hpoint : Continuous (fun r : ℝ => s₀+(r : ℂ)*v) := by fun_prop
  have hQ := (Q.continuous.comp hpoint).continuousAt (x := (0 : ℝ))
  have hDen := (D.continuous.comp hpoint).continuousAt (x := (0 : ℝ))
  have hlim : Tendsto (fun r : ℝ => (v^m*Q.eval (s₀+(r : ℂ)*v)/D.eval (s₀+(r : ℂ)*v)).re)
      (𝓝[>] 0) (𝓝 ((v^m*Q.eval s₀/D.eval s₀).re)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    have hct : ContinuousAt (fun r : ℝ => v^m*Q.eval (s₀+(r : ℂ)*v)/D.eval (s₀+(r : ℂ)*v)) 0 :=
      (continuousAt_const.mul hQ).div hDen (by simpa using hD)
    have hre := Complex.continuous_re.continuousAt.comp hct
    simpa using hre.tendsto
  have hevent : ∀ᶠ r : ℝ in 𝓝[>] 0,
      0 ≤ (v^m*Q.eval (s₀+(r : ℂ)*v)/D.eval (s₀+(r : ℂ)*v)).re := by
    filter_upwards [hregion,self_mem_nhdsWithin] with r hreg hr
    have hrpos : 0 < r := hr
    have h := hweak (s₀+(r : ℂ)*v) hreg
    have heq : P.eval (s₀+(r : ℂ)*v)/D.eval (s₀+(r : ℂ)*v) =
        (r^m : ℝ)*(v^m*Q.eval (s₀+(r : ℂ)*v)/D.eval (s₀+(r : ℂ)*v)) := by
      rw [hfactor,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
      push_cast
      ring
    rw [heq,Complex.mul_re] at h
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at h
    exact (mul_nonneg_iff_of_pos_left (pow_pos hrpos m)).mp h
  have h := ge_of_tendsto hlim hevent
  convert h using 1
  congr 1
  ring

theorem weak_positive_real_no_open_right_root
    (P D : ℂ[X]) (hP : P ≠ 0)
    (hD : ∀ s : ℂ, 0 ≤ s.re → D.eval s ≠ 0)
    (hweak : ∀ s : ℂ, 0 ≤ s.re → 0 ≤ (P.eval s/D.eval s).re) :
    ∀ s : ℂ, P.eval s = 0 → s.re ≤ 0 := by
  intro s hs
  by_contra hn
  have hre : 0 < s.re := lt_of_not_ge hn
  obtain ⟨Q,hfactor,hnot⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hP s
  have hQ : Q.eval s ≠ 0 := by
    intro hz
    exact hnot ((Polynomial.dvd_iff_isRoot).mpr hz)
  have hA : Q.eval s/D.eval s ≠ 0 := div_ne_zero hQ (hD s hre.le)
  have hdirs (v : ℂ) : 0 ≤ ((Q.eval s/D.eval s)*v^P.rootMultiplicity s).re := by
    apply rational_leading_ray_nonnegative P D Q s v _ hfactor (hD s hre.le) hweak
    have hcont : ContinuousAt (fun r : ℝ => (s+(r : ℂ)*v).re) 0 := by fun_prop
    have hnear : ∀ᶠ r : ℝ in 𝓝 (0 : ℝ), 0 < (s+(r : ℂ)*v).re :=
      hcont (by simpa using Ioi_mem_nhds hre)
    exact (hnear.filter_mono nhdsWithin_le_nhds).mono (fun _ h => h.le)
  have hm0 := monomial_full_plane_order_zero _ hA _ hdirs
  have hmpos := (Polynomial.rootMultiplicity_pos hP).mpr hs
  omega

theorem weak_positive_real_axis_root_simple
    (P D : ℂ[X]) (hP : P ≠ 0)
    (hD : ∀ s : ℂ, 0 ≤ s.re → D.eval s ≠ 0)
    (hweak : ∀ s : ℂ, 0 ≤ s.re → 0 ≤ (P.eval s/D.eval s).re)
    (s : ℂ) (hsre : s.re = 0) (hs : P.eval s = 0) :
    P.rootMultiplicity s = 1 := by
  obtain ⟨Q,hfactor,hnot⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hP s
  have hQ : Q.eval s ≠ 0 := by
    intro hz
    exact hnot ((Polynomial.dvd_iff_isRoot).mpr hz)
  have hD0 := hD s hsre.ge
  have hA : Q.eval s/D.eval s ≠ 0 := div_ne_zero hQ hD0
  have hdirs (v : ℂ) (hv : 0 < v.re) :
      0 ≤ ((Q.eval s/D.eval s)*v^P.rootMultiplicity s).re := by
    apply rational_leading_ray_nonnegative P D Q s v _ hfactor hD0 hweak
    filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      hsre,zero_mul,sub_zero,zero_add]
    exact mul_nonneg (le_of_lt hr) hv.le
  have hmle := monomial_half_plane_order_bound _ hA _ hdirs
  have hmpos := (Polynomial.rootMultiplicity_pos hP).mpr hs
  omega

private theorem CriticalCertificate.mapped_numerator_ne_zero {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) : Crt.numerator.map (algebraMap ℝ ℂ) ≠ 0 := by
  intro hz
  apply Crt.numerator_ne_zero
  ext k
  have h := congrArg (fun q : ℂ[X] => q.coeff k) hz
  simpa using h

theorem CriticalCertificate.right_nonnegative {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (ha : HurwitzClass d a) (hb : b.natDegree = d) :
    ∀ s : ℂ, 0 ≤ s.re → 0 ≤ (value Crt.numerator s/value a s).re :=
  right_half_plane_real_nonnegative d Crt.numerator a Crt.numerator_degree ha
    (Crt.top_coefficient_nonnegative ha.1 ha.2.1) (Crt.boundary_nonnegative ha.2.1 hb).1

theorem CriticalCertificate.no_open_right_root {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (ha : HurwitzClass d a) (hb : b.natDegree = d) :
    ∀ s : ℂ, value Crt.numerator s = 0 → s.re ≤ 0 := by
  have hP := Crt.mapped_numerator_ne_zero
  have hD : ∀ s : ℂ, 0 ≤ s.re → (a.map (algebraMap ℝ ℂ)).eval s ≠ 0 := by
    intro s hs
    rw [← value_eq_mapped_eval]
    exact ha.2.2 s hs
  have hweak : ∀ s : ℂ, 0 ≤ s.re →
      ((Crt.numerator.map (algebraMap ℝ ℂ)).eval s/(a.map (algebraMap ℝ ℂ)).eval s).re ≥ 0 := by
    simpa only [← value_eq_mapped_eval] using Crt.right_nonnegative ha hb
  simpa only [← value_eq_mapped_eval] using
    weak_positive_real_no_open_right_root _ _ hP hD hweak

theorem CriticalCertificate.axis_root_simple {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (ha : HurwitzClass d a) (hb : b.natDegree = d)
    (s : ℂ) (hsre : s.re = 0) (hs : value Crt.numerator s = 0) :
    (Crt.numerator.map (algebraMap ℝ ℂ)).rootMultiplicity s = 1 := by
  apply weak_positive_real_axis_root_simple _ (a.map (algebraMap ℝ ℂ)) Crt.mapped_numerator_ne_zero
  · intro z hz
    rw [← value_eq_mapped_eval]
    exact ha.2.2 z hz
  · simpa only [← value_eq_mapped_eval] using Crt.right_nonnegative ha hb
  · exact hsre
  · simpa only [← value_eq_mapped_eval] using hs

/-! ## 5. 多项式反射、有符号频率与接触点计数 -/

/-- Reflection in the polynomial argument, s -> -s. -/
def reflection (p : ℂ[X]) : ℂ[X] := p.comp (-X)

theorem reflection_reflection (p : ℂ[X]) : reflection (reflection p) = p := by
  simp [reflection,Polynomial.comp_assoc]

theorem reflection_zero : reflection 0 = 0 := by simp [reflection]

theorem reflection_mul (p q : ℂ[X]) : reflection (p*q) = reflection p*reflection q := by
  simp [reflection,Polynomial.mul_comp]

theorem reflection_degree (p : ℂ[X]) : (reflection p).natDegree = p.natDegree := by
  simp [reflection,Polynomial.natDegree_comp]

theorem reflection_ne_zero {p : ℂ[X]} (hp : p ≠ 0) : reflection p ≠ 0 := by
  intro hz
  have h := congrArg reflection hz
  rw [reflection_reflection,reflection_zero] at h
  exact hp h

/-- A strictly left-half-plane factor is coprime to the reflection of any
polynomial whose roots are in the closed left half-plane. -/
theorem left_factor_coprime_reflection (Q P : ℂ[X])
    (hQ : ∀ z : ℂ, Q.eval z = 0 → z.re < 0)
    (hP : ∀ z : ℂ, P.eval z = 0 → z.re ≤ 0) :
    IsCoprime Q (reflection P) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ Q (reflection P)).mpr
  intro z
  by_cases hq : Q.eval z = 0
  · right
    intro hp
    have hp' : P.eval (-z) = 0 := by simpa [reflection] using hp
    have hleft := hQ z hq
    have hright := hP (-z) hp'
    simp only [Complex.neg_re] at hright
    linarith
  · left
    simpa using hq

/-- Coefficientwise real part, used only as an additive operation. -/
def realPolynomial (P : ℂ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (P.natDegree+1), monomial k (P.coeff k).re

theorem realPolynomial_coefficient (P : ℂ[X]) (k : ℕ) :
    (realPolynomial P).coeff k = (P.coeff k).re := by
  classical
  by_cases hk : k < P.natDegree+1
  · simp [realPolynomial,Polynomial.finset_sum_coeff,Polynomial.coeff_monomial,Finset.sum_ite_eq',hk]
  · have hcoeff : P.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [realPolynomial,Polynomial.finset_sum_coeff,Polynomial.coeff_monomial,Finset.sum_ite_eq',hk,hcoeff]

theorem realPolynomial_degree (P : ℂ[X]) : (realPolynomial P).natDegree ≤ P.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [realPolynomial_coefficient,Polynomial.coeff_eq_zero_of_natDegree_lt hk]
  rfl

theorem realPolynomial_eval (P : ℂ[X]) (w : ℝ) :
    (realPolynomial P).eval w = (P.eval (w : ℂ)).re := by
  rw [Polynomial.eval_eq_sum_range (p := P) (w : ℂ)]
  simp [realPolynomial,Polynomial.eval_finset_sum,Polynomial.eval_monomial,Complex.mul_re,← Complex.ofReal_pow]

def frequencyProduct (c p : ℝ[X]) : ℂ[X] :=
  ((c.map (algebraMap ℝ ℂ)).comp (C Complex.I*X))*
    ((p.map (algebraMap ℝ ℂ)).comp (C (-Complex.I)*X))

def frequencyCross (c p : ℝ[X]) : ℝ[X] := realPolynomial (frequencyProduct c p)

theorem value_conjugate (p : ℝ[X]) (z : ℂ) : value p (conj z) = conj (value p z) := by
  simp [value,Polynomial.aeval_conj]

theorem frequencyProduct_eval (c p : ℝ[X]) (w : ℝ) :
    (frequencyProduct c p).eval (w : ℂ) =
      value c ((w : ℂ)*Complex.I)*conj (value p ((w : ℂ)*Complex.I)) := by
  simp only [frequencyProduct,Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_C,Polynomial.eval_X]
  rw [← value_eq_mapped_eval,← value_eq_mapped_eval]
  have harg : (-Complex.I)*(w : ℂ) = conj ((w : ℂ)*Complex.I) := by simp; ring
  rw [harg,value_conjugate,mul_comm Complex.I (w : ℂ)]

theorem frequencyCross_eval (c p : ℝ[X]) (w : ℝ) :
    (frequencyCross c p).eval w = pairing (value c (w*Complex.I)) (value p (w*Complex.I)) := by
  rw [frequencyCross,realPolynomial_eval,frequencyProduct_eval]
  rfl

private theorem scaled_argument_degree (P : ℝ[X]) (z : ℂ) (hz : z ≠ 0) :
    ((P.map (algebraMap ℝ ℂ)).comp (C z*X)).natDegree = P.natDegree := by
  rw [Polynomial.natDegree_comp,Polynomial.natDegree_C_mul hz,Polynomial.natDegree_X,mul_one]
  simp

theorem frequencyCross_degree (c p : ℝ[X]) :
    (frequencyCross c p).natDegree ≤ c.natDegree+p.natDegree := by
  calc
    _ ≤ (frequencyProduct c p).natDegree := realPolynomial_degree _
    _ ≤ _ := by
      unfold frequencyProduct
      have hmul := (Polynomial.natDegree_mul_le
          (p := (c.map (algebraMap ℝ ℂ)).comp (C Complex.I*X))
          (q := (p.map (algebraMap ℝ ℂ)).comp (C (-Complex.I)*X)))
      rw [scaled_argument_degree c Complex.I Complex.I_ne_zero,
        scaled_argument_degree p (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero)] at hmul
      exact hmul

theorem frequencyCross_top (d : ℕ) (c p : ℝ[X])
    (hc : c.natDegree ≤ d) (hp : p.natDegree ≤ d) (hmonic : p.coeff d = 1) :
    (frequencyCross c p).coeff (2*d) = c.coeff d := by
  have hA : ((c.map (algebraMap ℝ ℂ)).comp (C Complex.I*X)).natDegree ≤ d := by
    simpa only [scaled_argument_degree c _ Complex.I_ne_zero] using hc
  have hB : ((p.map (algebraMap ℝ ℂ)).comp (C (-Complex.I)*X)).natDegree ≤ d := by
    simpa only [scaled_argument_degree p _ (neg_ne_zero.mpr Complex.I_ne_zero)] using hp
  rw [frequencyCross,realPolynomial_coefficient,frequencyProduct,show 2*d = d+d by omega,
    Polynomial.coeff_mul_add_eq_of_natDegree_le hA hB]
  simp only [Polynomial.comp_C_mul_X_coeff,Polynomial.coeff_map,Complex.coe_algebraMap,hmonic,
    Complex.ofReal_one,one_mul]
  have hi : Complex.I^d*(-Complex.I)^d = 1 := by rw [← mul_pow]; simp
  calc
    _ = ((c.coeff d : ℂ)*(Complex.I^d*(-Complex.I)^d)).re := by congr 1; ring
    _ = c.coeff d := by rw [hi]; simp

private theorem complex_pair_sum (u v : ℂ) :
    u*conj v+conj u*v = ((2*pairing u v : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [pairing,Complex.mul_re,Complex.mul_im] <;> ring

/-- The cross polynomial of a nonzero degree-bounded numerator and a stable
monic denominator cannot vanish identically. -/
theorem frequencyCross_ne_zero (d : ℕ) (c p : ℝ[X])
    (hc : c ≠ 0) (hcdeg : c.natDegree ≤ d) (hp : HurwitzClass d p) :
    frequencyCross c p ≠ 0 := by
  classical
  intro hcross
  let P : ℂ[X] := c.map (algebraMap ℝ ℂ)
  let D : ℂ[X] := p.map (algebraMap ℝ ℂ)
  let H : ℂ[X] := P*reflection D+reflection P*D
  have hP : P ≠ 0 := by
    intro hz
    apply hc
    ext k
    have h := congrArg (fun q : ℂ[X] => q.coeff k) hz
    simpa [P] using h
  have hDleft : ∀ z : ℂ, D.eval z = 0 → z.re < 0 := by
    intro z hz
    by_contra hn
    have h := hp.2.2 z (le_of_not_gt hn)
    apply h
    simpa only [value_eq_mapped_eval] using hz
  have hcoprime : IsCoprime D (reflection D) :=
    left_factor_coprime_reflection D D hDleft (fun z hz => (hDleft z hz).le)
  have hHzero (w : ℝ) : H.eval ((w : ℂ)*Complex.I) = 0 := by
    have hz : -((w : ℂ)*Complex.I) = conj ((w : ℂ)*Complex.I) := by simp
    have hval : (frequencyCross c p).eval w = 0 := by rw [hcross]; simp
    rw [frequencyCross_eval] at hval
    simp only [H,reflection,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,
      Polynomial.eval_neg,Polynomial.eval_X,hz]
    simp only [P,D,← value_eq_mapped_eval]
    rw [value_conjugate,value_conjugate,complex_pair_sum,hval]
    simp
  have hH : H = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinj : Function.Injective (fun w : ℝ => (w : ℂ)*Complex.I) := by
      intro x y hxy
      have h := congrArg Complex.im hxy
      simpa using h
    apply (Set.infinite_range_of_injective hinj).mono
    rintro z ⟨w,rfl⟩
    exact hHzero w
  have hdvd : D ∣ P*reflection D := by
    refine ⟨-reflection P,?_⟩
    have heq : P*reflection D+reflection P*D = 0 := hH
    calc
      _ = -(reflection P*D) := eq_neg_of_add_eq_zero_left heq
      _ = _ := by ring
  have hDP : D ∣ P := hcoprime.dvd_of_dvd_mul_right hdvd
  have hdegree : d ≤ c.natDegree := by
    have h := Polynomial.natDegree_le_of_dvd hDP hP
    simpa [D,P,hp.2.1] using h
  have hcdegree : c.natDegree = d := by omega
  have htop : c.coeff d = 0 := by
    rw [← frequencyCross_top d c p hcdeg hp.2.1.le
      (by simpa [← hp.2.1] using hp.1.coeff_natDegree),hcross]
    simp
  rw [← hcdegree,Polynomial.coeff_natDegree] at htop
  exact Polynomial.leadingCoeff_ne_zero.mpr hc htop

theorem twice_real_root_card_le_degree (q : ℝ[X]) (hq : q ≠ 0)
    (hpositive : ∀ x : ℝ, 0 ≤ q.eval x) :
    2*q.roots.toFinset.card ≤ q.natDegree := by
  classical
  have hcount (x : ℝ) (hx : x ∈ q.roots.toFinset) : 2 ≤ q.roots.count x := by
    have hroot : q.eval x = 0 := (Polynomial.mem_roots hq).mp (Multiset.mem_toFinset.mp hx)
    have hlocal : IsLocalMin q.eval x := by
      filter_upwards [] with y
      rw [hroot]
      exact hpositive y
    have hderivative : q.derivative.eval x = 0 := by
      rw [← q.deriv]
      exact hlocal.deriv_eq_zero
    rw [Polynomial.count_roots]
    exact (Polynomial.one_lt_rootMultiplicity_iff_isRoot hq).mpr ⟨hroot,hderivative⟩
  calc
    2*q.roots.toFinset.card = ∑ x ∈ q.roots.toFinset, (2 : ℕ) := by simp [mul_comm]
    _ ≤ ∑ x ∈ q.roots.toFinset, q.roots.count x := Finset.sum_le_sum (fun x hx => hcount x hx)
    _ = q.roots.card := Multiset.toFinset_sum_count_eq q.roots
    _ ≤ q.natDegree := Polynomial.card_roots' q

theorem CriticalCertificate.cross_nonnegative {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (ha : HurwitzClass d a) (hb : HurwitzClass d b) :
    (∀ w : ℝ, 0 ≤ (frequencyCross Crt.numerator a).eval w) ∧
    (∀ w : ℝ, 0 ≤ (frequencyCross Crt.numerator b).eval w) := by
  have hfreq := Crt.boundary_nonnegative ha.2.1 hb.2.1
  constructor
  · intro w
    rw [frequencyCross_eval]
    have h := hfreq.1 w
    rw [real_quotient] at h
    simpa using (le_div_iff₀ (Complex.normSq_pos.mpr (stable_axis_ne_zero ha.2.2 w))).mp h
  · intro w
    rw [frequencyCross_eval]
    have h := hfreq.2 w
    rw [real_quotient] at h
    simpa using (le_div_iff₀ (Complex.normSq_pos.mpr (stable_axis_ne_zero hb.2.2 w))).mp h

/-- Signed frequencies avoid all parity and origin case splits. Contacts lie
in the union of the two real root sets; imaginary zeros of the support lie
in their intersection, so their two cardinalities share one degree budget. -/
theorem signed_contact_budget {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (ha : HurwitzClass d a) (hb : HurwitzClass d b)
    (S J : Finset ℝ)
    (hS : S ⊆ (frequencyCross Crt.numerator a).roots.toFinset ∪
      (frequencyCross Crt.numerator b).roots.toFinset)
    (hJ : J ⊆ (frequencyCross Crt.numerator a).roots.toFinset ∩
      (frequencyCross Crt.numerator b).roots.toFinset) :
    S.card+J.card ≤ Crt.numerator.natDegree+d := by
  have hnonneg := Crt.cross_nonnegative ha hb
  have hA := twice_real_root_card_le_degree _
    (frequencyCross_ne_zero d _ _ Crt.numerator_ne_zero Crt.numerator_degree ha) hnonneg.1
  have hB := twice_real_root_card_le_degree _
    (frequencyCross_ne_zero d _ _ Crt.numerator_ne_zero Crt.numerator_degree hb) hnonneg.2
  have hdegA := frequencyCross_degree Crt.numerator a
  have hdegB := frequencyCross_degree Crt.numerator b
  have hcardS := Finset.card_le_card hS
  have hcardJ := Finset.card_le_card hJ
  have hsum := Finset.card_union_add_card_inter
    (frequencyCross Crt.numerator a).roots.toFinset (frequencyCross Crt.numerator b).roots.toFinset
  rw [ha.2.1] at hdegA
  rw [hb.2.1] at hdegB
  omega

def linearRootProduct (R : Multiset ℂ) : ℂ[X] := (R.map (fun z => X-C z)).prod

theorem linearRootProduct_monic_degree (R : Multiset ℂ) :
    (linearRootProduct R).Monic ∧ (linearRootProduct R).natDegree = R.card := by
  induction R using Multiset.induction_on with
  | empty => simp [linearRootProduct]
  | cons z R ih =>
    have heq : linearRootProduct (z ::ₘ R) = (X-C z)*linearRootProduct R := by simp [linearRootProduct]
    rw [heq]
    refine ⟨(Polynomial.monic_X_sub_C z).mul ih.1,?_⟩
    rw [Polynomial.natDegree_mul (Polynomial.monic_X_sub_C z).ne_zero ih.1.ne_zero,
      Polynomial.natDegree_X_sub_C,ih.2,Multiset.card_cons]
    omega

theorem linearRootProduct_eval (R : Multiset ℂ) (z : ℂ) :
    (linearRootProduct R).eval z = (R.map (fun u => z-u)).prod := by
  induction R using Multiset.induction_on with
  | empty => simp [linearRootProduct]
  | cons u R ih =>
    have heq : linearRootProduct (u ::ₘ R) = (X-C u)*linearRootProduct R := by simp [linearRootProduct]
    rw [heq,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,ih]
    simp

theorem linearRootProduct_root_iff (R : Multiset ℂ) (z : ℂ) :
    (linearRootProduct R).eval z = 0 ↔ z ∈ R := by
  classical
  rw [linearRootProduct_eval,Multiset.prod_eq_zero_iff]
  simp only [Multiset.mem_map,sub_eq_zero]
  constructor
  · rintro ⟨u,hu,huz⟩
    simpa [huz] using hu
  · intro hz
    exact ⟨z,hz,rfl⟩

/-- Distinct real frequencies of the imaginary-axis zeros. -/
def axisFrequencies (P : ℂ[X]) : Finset ℝ :=
  (P.roots.toFinset.filter (fun z => z.re = 0)).image Complex.im

theorem mem_axisFrequencies_iff (P : ℂ[X]) (hP : P ≠ 0) (w : ℝ) :
    w ∈ axisFrequencies P ↔ P.eval ((w : ℂ)*Complex.I) = 0 := by
  classical
  constructor
  · intro hw
    obtain ⟨z,hz,hzw⟩ := Finset.mem_image.mp hw
    have hdata := Finset.mem_filter.mp hz
    have hroot := (Polynomial.mem_roots hP).mp (Multiset.mem_toFinset.mp hdata.1)
    have heq : (w : ℂ)*Complex.I = z := by
      apply Complex.ext <;> simp [hdata.2,← hzw]
    simpa only [heq] using hroot
  · intro hw
    refine Finset.mem_image.mpr ⟨(w : ℂ)*Complex.I,Finset.mem_filter.mpr ⟨?_,by simp⟩,by simp⟩
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).mpr hw)

/-- Closed-left-half-plane roots with simple axis roots split into a strictly
Hurwitz factor Q and exactly one factor per distinct axis frequency. -/
theorem strict_factor_and_axis_degree
    (P : ℂ[X]) (hP : P ≠ 0)
    (hleft : ∀ z : ℂ, P.eval z = 0 → z.re ≤ 0)
    (hsimple : ∀ z : ℂ, z.re = 0 → P.eval z = 0 → P.rootMultiplicity z = 1) :
    ∃ Q : ℂ[X], Q.Monic ∧ Q ∣ P ∧
      (∀ z : ℂ, Q.eval z = 0 → z.re < 0) ∧
      Q.natDegree+(axisFrequencies P).card = P.natDegree := by
  classical
  let L := P.roots.filter (fun z => z.re < 0)
  let A := P.roots.filter (fun z => z.re = 0)
  have hpartition : L+A = P.roots := by
    have heq : A = P.roots.filter (fun z => ¬z.re < 0) := by
      apply Multiset.filter_congr
      intro z hz
      have hr := hleft z ((Polynomial.mem_roots hP).mp hz)
      constructor <;> intro h <;> linarith
    rw [heq]
    exact Multiset.filter_add_not (p := fun z : ℂ => z.re < 0) P.roots
  have hnodup : A.Nodup := by
    apply Multiset.nodup_iff_count_le_one.mpr
    intro z
    change (P.roots.filter (fun u => u.re = 0)).count z ≤ 1
    rw [Multiset.count_filter]
    by_cases hz : z.re = 0
    · rw [if_pos hz]
      by_cases hr : z ∈ P.roots
      · rw [Polynomial.count_roots,hsimple z hz ((Polynomial.mem_roots hP).mp hr)]
      · simp [Multiset.count_eq_zero_of_not_mem hr]
    · rw [if_neg hz]
      omega
  have hAset : A.toFinset = P.roots.toFinset.filter (fun z => z.re = 0) := by
    ext z
    simp [A,Multiset.mem_filter]
  have himInjective : Set.InjOn Complex.im (A.toFinset : Set ℂ) := by
    intro z hz u hu heq
    have hzre := (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hz)).2
    have hure := (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hu)).2
    exact Complex.ext (hzre.trans hure.symm) heq
  have hAcard : (axisFrequencies P).card = A.card := by
    rw [axisFrequencies,← hAset]
    rw [Finset.card_image_iff.mpr himInjective,Multiset.toFinset_card_of_nodup hnodup]
  let Q := linearRootProduct L
  have hQ := linearRootProduct_monic_degree L
  have hrootCard : P.roots.card = P.natDegree := by
    simpa using (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits P)).symm
  have hfactor : P = C P.leadingCoeff*(Q*linearRootProduct A) := by
    calc
      P = C P.leadingCoeff*linearRootProduct P.roots :=
        (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hrootCard).symm
      _ = _ := by rw [← hpartition]; simp [linearRootProduct,Q]
  refine ⟨Q,hQ.1,?_,?_,?_⟩
  · refine ⟨C P.leadingCoeff*linearRootProduct A,?_⟩
    calc
      P = C P.leadingCoeff*(Q*linearRootProduct A) := hfactor
      _ = _ := by ring
  · intro z hz
    have hmem := (linearRootProduct_root_iff L z).mp hz
    exact (Multiset.mem_filter.mp hmem).2
  · have hc := congrArg Multiset.card hpartition
    simp only [Multiset.card_add] at hc
    rw [hrootCard] at hc
    rw [hQ.2,hAcard]
    exact hc

/-! ## 6. 留数矩、接触节点与共轭对称化 -/

/-- The numerator after putting simple fractions r_i/(s-z_i) over a common
polynomial denominator. Nodes will be roots of D in the application. -/
def residueNumerator {ι : Type*} [Fintype ι]
    (D : ℂ[X]) (z r : ι → ℂ) : ℂ[X] :=
  ∑ i : ι, C (r i)*(D /ₘ (X-C (z i)))

/-- Every high numerator coefficient is a combination of low moments. -/
theorem residueNumerator_coefficient {ι : Type*} [Fintype ι]
    (D : ℂ[X]) (z r : ι → ℂ) (k : ℕ) :
    (residueNumerator D z r).coeff k =
      ∑ j ∈ Finset.Icc (k+1) D.natDegree,
        D.coeff j * ∑ i : ι, r i*(z i)^(j-(k+1)) := by
  classical
  simp only [residueNumerator, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_divByMonic_X_sub_C]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- M zero moments annihilate every coefficient k with deg D <= k+M. -/
theorem residueNumerator_high_coefficient_zero {ι : Type*} [Fintype ι]
    (D : ℂ[X]) (z r : ι → ℂ) (M k : ℕ)
    (hmoment : ∀ j : ℕ, j < M → (∑ i : ι, r i*(z i)^j) = 0)
    (hhigh : D.natDegree ≤ k+M) :
    (residueNumerator D z r).coeff k = 0 := by
  rw [residueNumerator_coefficient]
  apply Finset.sum_eq_zero
  intro j hj
  rw [hmoment _ (by have := Finset.mem_Icc.mp hj; omega),mul_zero]

/-- A nonzero residue numerator has strictly fewer than deg D-M degrees.
The formulation also handles too many moments without truncated subtraction. -/
theorem residueNumerator_degree_gap {ι : Type*} [Fintype ι]
    (D : ℂ[X]) (z r : ι → ℂ) (M : ℕ)
    (hmoment : ∀ j : ℕ, j < M → (∑ i : ι, r i*(z i)^j) = 0)
    (hne : residueNumerator D z r ≠ 0) :
    (residueNumerator D z r).natDegree+M < D.natDegree := by
  by_contra hn
  have hc := residueNumerator_high_coefficient_zero D z r M
    (residueNumerator D z r).natDegree hmoment (le_of_not_gt hn)
  rw [Polynomial.coeff_natDegree] at hc
  exact Polynomial.leadingCoeff_ne_zero.mpr hne hc

def endpoint (a b : ℝ[X]) (right : Bool) : ℝ[X] := if right then b else a

theorem endpoint_hurwitz {d : ℕ} {a b : ℝ[X]}
    (ha : HurwitzClass d a) (hb : HurwitzClass d b) (r : Bool) : HurwitzClass d (endpoint a b r) := by
  cases r <;> assumption

structure AtomCoordinates (d : ℕ) (a b : ℝ[X]) (n : ℕ) (z : Fin n → CoefficientSpace d) where
  right : Fin n → Bool
  parameter : Fin n → ℝ
  parameter_mem : ∀ i, parameter i ∈ Icc (-1 : ℝ) 1
  represents : ∀ i, z i = feature d (endpoint a b (right i)) (parameter i)

theorem CriticalCertificate.coordinates_exist {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) : Nonempty (AtomCoordinates d a b Crt.count Crt.point) := by
  classical
  have h (i : Fin Crt.count) : ∃ r : Bool, ∃ u : ℝ,
      u ∈ Icc (-1 : ℝ) 1 ∧ Crt.point i = feature d (endpoint a b r) u := by
    rcases Crt.point_mem i with ⟨u,hu,hz⟩ | ⟨u,hu,hz⟩
    · exact ⟨false,u,hu,hz.symm⟩
    · exact ⟨true,u,hu,hz.symm⟩
  choose r u hu hz using h
  exact ⟨⟨r,u,hu,hz⟩⟩

def CriticalCertificate.coordinates {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) : AtomCoordinates d a b Crt.count Crt.point :=
  Classical.choice Crt.coordinates_exist

def CriticalCertificate.denominator {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (i : Fin Crt.count) : ℝ[X] := endpoint a b (Crt.coordinates.right i)

def CriticalCertificate.parameter {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (i : Fin Crt.count) : ℝ := Crt.coordinates.parameter i

def CriticalCertificate.finiteAtoms {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) : Finset (Fin Crt.count) :=
  Finset.univ.filter (fun i => |Crt.parameter i| < 1)

def CriticalCertificate.frequency {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (i : Fin Crt.count) : ℝ :=
  Crt.parameter i/(1-|Crt.parameter i|)

def CriticalCertificate.finiteMass {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (i : Fin Crt.count) : ℝ :=
  Crt.weight i*(1-|Crt.parameter i|)^(2*d)

theorem CriticalCertificate.point_representation {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (i : Fin Crt.count) :
    Crt.point i = feature d (Crt.denominator i) (Crt.parameter i) := Crt.coordinates.represents i

theorem CriticalCertificate.finite_scale_positive {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) {i : Fin Crt.count} (hi : i ∈ Crt.finiteAtoms) :
    0 < 1-|Crt.parameter i| := sub_pos.mpr (Finset.mem_filter.mp hi).2

theorem CriticalCertificate.finiteMass_positive {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) {i : Fin Crt.count} (hi : i ∈ Crt.finiteAtoms) :
    0 < Crt.finiteMass i := mul_pos (Crt.weight_pos i) (pow_pos (Crt.finite_scale_positive hi) _)

theorem CriticalCertificate.infinite_scale_zero {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) {i : Fin Crt.count} (hi : i ∉ Crt.finiteAtoms) :
    1-|Crt.parameter i| = 0 := by
  have hrange := Crt.coordinates.parameter_mem i
  have hle : |Crt.parameter i| ≤ 1 := abs_le.mpr hrange
  have hnot : ¬|Crt.parameter i| < 1 := by simpa [CriticalCertificate.finiteAtoms] using hi
  linarith

theorem CriticalCertificate.finite_feature {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (ha : HurwitzClass d a) (hb : HurwitzClass d b)
    {i : Fin Crt.count} (hi : i ∈ Crt.finiteAtoms) (k : Fin (d+1)) :
    Crt.point i k = (1-|Crt.parameter i|)^(2*d)*
      pairing ((Crt.frequency i*Complex.I)^k.val) (value (Crt.denominator i) (Crt.frequency i*Complex.I)) := by
  have hd := endpoint_hurwitz ha hb (Crt.coordinates.right i)
  rw [Crt.point_representation]
  unfold feature compactPairing
  rw [homogeneous_pairing_finite d (X^k.val) (Crt.denominator i)
    (by simp; omega) hd.2.1.le _ _ (ne_of_gt (Crt.finite_scale_positive hi))]
  simp [CriticalCertificate.frequency,value]

theorem CriticalCertificate.infinite_feature {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (ha : HurwitzClass d a) (hb : HurwitzClass d b)
    {i : Fin Crt.count} (hi : i ∉ Crt.finiteAtoms) (k : Fin (d+1)) :
    Crt.point i k = if k.val = d then 1 else 0 := by
  have hd := endpoint_hurwitz ha hb (Crt.coordinates.right i)
  have hdenTop : (Crt.denominator i).coeff d = 1 := by
    simpa [← hd.2.1] using hd.1.coeff_natDegree
  have hscale := Crt.infinite_scale_zero hi
  have habs : |Crt.parameter i| = 1 := by linarith
  have hsq : (Crt.parameter i)^2 = 1 := by
    have h := congrArg (fun x : ℝ => x^2) habs
    simpa using h
  rw [Crt.point_representation]
  unfold feature compactPairing
  rw [hscale,homogeneous_pairing_any_infinity,hdenTop]
  simp [Polynomial.coeff_X_pow,pow_mul,hsq,eq_comm]

theorem CriticalCertificate.finiteAtoms_nonempty {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (ha : HurwitzClass d a) (hb : HurwitzClass d b) :
    Crt.finiteAtoms.Nonempty := by
  by_contra hn
  have hall (i : Fin Crt.count) : i ∉ Crt.finiteAtoms := fun hi => hn ⟨i,hi⟩
  have h := congrArg (fun x : CoefficientSpace d => x ⟨d,by omega⟩) Crt.balance
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.zero_apply,smul_eq_mul] at h
  have heq : (∑ i : Fin Crt.count, Crt.weight i*Crt.point i ⟨d,by omega⟩) = ∑ i, Crt.weight i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Crt.infinite_feature ha hb (hall i)]
    simp
  rw [heq,Crt.weight_sum] at h
  norm_num at h

theorem CriticalCertificate.finite_contact {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (ha : HurwitzClass d a) (hb : HurwitzClass d b)
    {i : Fin Crt.count} (hi : i ∈ Crt.finiteAtoms) :
    pairing (value Crt.numerator (Crt.frequency i*Complex.I))
      (value (Crt.denominator i) (Crt.frequency i*Complex.I)) = 0 := by
  have hd := endpoint_hurwitz ha hb (Crt.coordinates.right i)
  have hc := Crt.contact i
  rw [Crt.point_representation,dotFunctional_apply,← pairing_feature_identity] at hc
  change compactPairing d Crt.numerator (Crt.denominator i) (Crt.parameter i) = 0 at hc
  rw [compactPairing,homogeneous_pairing_finite d Crt.numerator (Crt.denominator i)
    Crt.numerator_degree hd.2.1.le _ _ (ne_of_gt (Crt.finite_scale_positive hi))] at hc
  exact (mul_eq_zero.mp hc).resolve_left (ne_of_gt (pow_pos (Crt.finite_scale_positive hi) _))

/-- Infinity atoms vanish in every coefficient direction k<d. Their removal
therefore preserves the first d ordinary-frequency moment equations. -/
theorem CriticalCertificate.finite_moments {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (ha : HurwitzClass d a) (hb : HurwitzClass d b)
    (k : ℕ) (hk : k < d) :
    (∑ i ∈ Crt.finiteAtoms, Crt.finiteMass i*
      pairing ((Crt.frequency i*Complex.I)^k) (value (Crt.denominator i) (Crt.frequency i*Complex.I))) = 0 := by
  let j : Fin (d+1) := ⟨k,by omega⟩
  have h := congrArg (fun x : CoefficientSpace d => x j) Crt.balance
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.zero_apply,smul_eq_mul] at h
  have hrestrict : (∑ i ∈ Crt.finiteAtoms, Crt.weight i*Crt.point i j) =
      ∑ i : Fin Crt.count, Crt.weight i*Crt.point i j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    rw [Crt.infinite_feature ha hb hi]
    simp [j,ne_of_lt hk]
  rw [← hrestrict] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Crt.finite_feature ha hb hi j]
  dsimp [CriticalCertificate.finiteMass,j]
  ring

def imaginaryNode (w : ℝ) : ℂ := (w : ℂ)*Complex.I

theorem imaginaryNode_injective : Function.Injective imaginaryNode := by
  intro x y h
  have hi := congrArg Complex.im h
  simpa [imaginaryNode] using hi

theorem imaginaryNode_neg (w : ℝ) : imaginaryNode (-w) = -imaginaryNode w := by
  simp [imaginaryNode]

def nodePolynomial (S : Finset ℝ) : ℂ[X] := ∏ w ∈ S, (X-C (imaginaryNode w))

theorem nodePolynomial_insert (S : Finset ℝ) (w : ℝ) (hw : w ∉ S) :
    nodePolynomial (insert w S) = (X-C (imaginaryNode w))*nodePolynomial S := by
  simp [nodePolynomial,hw]

theorem nodePolynomial_monic_degree (S : Finset ℝ) :
    (nodePolynomial S).Monic ∧ (nodePolynomial S).natDegree = S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [nodePolynomial]
  | @insert w S hw ih =>
    rw [nodePolynomial_insert S w hw]
    refine ⟨(Polynomial.monic_X_sub_C _).mul ih.1,?_⟩
    rw [Polynomial.natDegree_mul (Polynomial.monic_X_sub_C _).ne_zero ih.1.ne_zero,
      Polynomial.natDegree_X_sub_C,ih.2,Finset.card_insert_of_not_mem hw]
    omega

theorem nodePolynomial_factor (S : Finset ℝ) (w : ℝ) (hw : w ∈ S) :
    nodePolynomial S = (X-C (imaginaryNode w))*nodePolynomial (S.erase w) := by
  calc
    nodePolynomial S = nodePolynomial (insert w (S.erase w)) := congrArg nodePolynomial (Finset.insert_erase hw).symm
    _ = _ := nodePolynomial_insert _ _ (Finset.not_mem_erase _ _)

theorem nodePolynomial_root_iff (S : Finset ℝ) (w : ℝ) :
    (nodePolynomial S).eval (imaginaryNode w) = 0 ↔ w ∈ S := by
  classical
  rw [nodePolynomial,Polynomial.eval_prod]
  simp only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,Finset.prod_eq_zero_iff,sub_eq_zero]
  constructor
  · rintro ⟨v,hv,heq⟩
    simpa [imaginaryNode_injective heq] using hv
  · intro hw
    exact ⟨w,hw,rfl⟩

theorem nodePolynomial_quotient (S : Finset ℝ) (w : ℝ) (hw : w ∈ S) :
    nodePolynomial S /ₘ (X-C (imaginaryNode w)) = nodePolynomial (S.erase w) := by
  rw [nodePolynomial_factor S w hw,Polynomial.mul_divByMonic_cancel_left _ (Polynomial.monic_X_sub_C _)]

theorem nodePolynomial_derivative_at_node (S : Finset ℝ) (w : ℝ) (hw : w ∈ S) :
    (nodePolynomial S).derivative.eval (imaginaryNode w) =
      (nodePolynomial (S.erase w)).eval (imaginaryNode w) := by
  rw [nodePolynomial_factor S w hw,Polynomial.derivative_mul]
  simp

theorem nodePolynomial_derivative_ne_zero (S : Finset ℝ) (w : ℝ) (hw : w ∈ S) :
    (nodePolynomial S).derivative.eval (imaginaryNode w) ≠ 0 := by
  rw [nodePolynomial_derivative_at_node S w hw]
  intro hz
  exact Finset.not_mem_erase w S ((nodePolynomial_root_iff (S.erase w) w).mp hz)

def nodeResidueNumerator (S : Finset ℝ) (r : ℝ → ℂ) : ℂ[X] :=
  residueNumerator (nodePolynomial S) (fun w : S => imaginaryNode w.val) (fun w : S => r w.val)

theorem nodeResidueNumerator_eval (S : Finset ℝ) (r : ℝ → ℂ) (w : ℝ) (hw : w ∈ S) :
    (nodeResidueNumerator S r).eval (imaginaryNode w) =
      r w*(nodePolynomial S).derivative.eval (imaginaryNode w) := by
  classical
  unfold nodeResidueNumerator residueNumerator
  simp only [Polynomial.eval_finset_sum,Polynomial.eval_mul,Polynomial.eval_C]
  rw [Finset.sum_eq_single (⟨w,hw⟩ : S)]
  · rw [nodePolynomial_quotient S w hw,← nodePolynomial_derivative_at_node S w hw]
  · intro v _ hv
    have hwv : w ≠ v.val := fun h => hv (Subtype.ext h.symm)
    rw [nodePolynomial_quotient S v.val v.property]
    rw [(nodePolynomial_root_iff (S.erase v.val) w).mpr (Finset.mem_erase.mpr ⟨hwv,hw⟩)]
    simp
  · simp

theorem nodeResidueNumerator_ne_zero (S : Finset ℝ) (hS : S.Nonempty) (r : ℝ → ℂ)
    (hr : ∀ w ∈ S, r w ≠ 0) : nodeResidueNumerator S r ≠ 0 := by
  obtain ⟨w,hw⟩ := hS
  intro hz
  have h := nodeResidueNumerator_eval S r w hw
  rw [hz,Polynomial.eval_zero] at h
  exact mul_ne_zero (hr w hw) (nodePolynomial_derivative_ne_zero S w hw) h.symm

theorem nodePolynomial_reflection (S : Finset ℝ) (hneg : ∀ w ∈ S, -w ∈ S) :
    reflection (nodePolynomial S) = C ((-1 : ℂ)^S.card)*nodePolynomial S := by
  classical
  have hprod : (∏ w ∈ S, (X-C (imaginaryNode (-w)))) = ∏ w ∈ S, (X-C (imaginaryNode w)) := by
    apply Finset.prod_bij (fun w _ => -w)
    · exact fun w hw => hneg w hw
    · intro x _ y _ hxy
      exact neg_injective hxy
    · intro y hy
      exact ⟨-y,hneg y hy,by simp⟩
    · intro w _
      rfl
  have hfactor (w : ℝ) : (X-C (imaginaryNode w)).comp (-X) =
      C (-1 : ℂ)*(X-C (imaginaryNode (-w))) := by
    simp [imaginaryNode]
    ring
  rw [reflection,nodePolynomial,Polynomial.prod_comp]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib,Finset.prod_const,← Polynomial.C_pow,hprod]

theorem nodePolynomial_derivative_neg (S : Finset ℝ) (hneg : ∀ w ∈ S, -w ∈ S) (z : ℂ) :
    (nodePolynomial S).derivative.eval (-z) =
      -((-1 : ℂ)^S.card)*(nodePolynomial S).derivative.eval z := by
  have h := congrArg Polynomial.derivative (nodePolynomial_reflection S hneg)
  simp only [reflection,Polynomial.derivative_comp,Polynomial.derivative_neg,Polynomial.derivative_X,
    Polynomial.derivative_C_mul] at h
  have hv := congrArg (fun p : ℂ[X] => p.eval z) h
  simp at hv
  have hn := congrArg (fun a : ℂ => -a) hv
  simpa using hn

/-- Contact residues force reflection parity of P*N. Degree control converts
the vanishing at all nodes into a polynomial identity. -/
theorem contact_residue_reflection_identity
    (S : Finset ℝ) (P : ℂ[X]) (r : ℝ → ℂ) (M : ℕ)
    (hneg : ∀ w ∈ S, -w ∈ S)
    (hrconj : ∀ w ∈ S, r (-w) = conj (r w))
    (hPconj : ∀ w ∈ S, P.eval (imaginaryNode (-w)) = conj (P.eval (imaginaryNode w)))
    (hcontact : ∀ w ∈ S, (P.eval (imaginaryNode w)*r w).re = 0)
    (hmoment : ∀ k < M, (∑ w : S, r w.val*(imaginaryNode w.val)^k) = 0)
    (hPdegree : P.natDegree ≤ M) (hN : nodeResidueNumerator S r ≠ 0) :
    P*nodeResidueNumerator S r =
      C ((-1 : ℂ)^S.card)*reflection (P*nodeResidueNumerator S r) := by
  classical
  let N := nodeResidueNumerator S r
  let ε : ℂ := (-1)^S.card
  let H : ℂ[X] := P*N-C ε*reflection (P*N)
  have hε : ε*ε = 1 := by dsimp [ε]; rw [← mul_pow]; simp
  have hdegree : N.natDegree+M < S.card := by
    have h := residueNumerator_degree_gap (nodePolynomial S)
      (fun w : S => imaginaryNode w.val) (fun w : S => r w.val) M hmoment hN
    simpa only [(nodePolynomial_monic_degree S).2] using h
  have hPNdegree : (P*N).natDegree < S.card := by
    have h := Polynomial.natDegree_mul_le (p := P) (q := N)
    omega
  have hHdegree : H.natDegree < S.card := by
    have hright : (C ε*reflection (P*N)).natDegree ≤ (P*N).natDegree := by
      simpa only [Polynomial.natDegree_C,zero_add,reflection_degree] using
        (Polynomial.natDegree_mul_le (p := C ε) (q := reflection (P*N)))
    calc
      H.natDegree ≤ max (P*N).natDegree (C ε*reflection (P*N)).natDegree :=
        Polynomial.natDegree_sub_le (P*N) (C ε*reflection (P*N))
      _ ≤ (P*N).natDegree := max_le le_rfl hright
      _ < S.card := hPNdegree
  have hHzero (w : ℝ) (hw : w ∈ S) : H.eval (imaginaryNode w) = 0 := by
    have hDneg : (nodePolynomial S).derivative.eval (imaginaryNode (-w)) =
        -ε*(nodePolynomial S).derivative.eval (imaginaryNode w) := by
      rw [imaginaryNode_neg]
      exact nodePolynomial_derivative_neg S hneg _
    have hsum : P.eval (imaginaryNode w)*r w+
        conj (P.eval (imaginaryNode w))*conj (r w) = 0 := by
      have h := complex_pair_sum (P.eval (imaginaryNode w)*r w) 1
      simpa [pairing,hcontact w hw] using h
    simp only [H,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,reflection,
      Polynomial.eval_comp,Polynomial.eval_neg,Polynomial.eval_X,← imaginaryNode_neg,N]
    rw [nodeResidueNumerator_eval S r w hw,nodeResidueNumerator_eval S r (-w) (hneg w hw),
      hPconj w hw,hrconj w hw,hDneg]
    calc
      _ = P.eval (imaginaryNode w)*r w*(nodePolynomial S).derivative.eval (imaginaryNode w)+
          (ε*ε)*(conj (P.eval (imaginaryNode w))*conj (r w)*(nodePolynomial S).derivative.eval (imaginaryNode w)) := by ring
      _ = (P.eval (imaginaryNode w)*r w+conj (P.eval (imaginaryNode w))*conj (r w))*
          (nodePolynomial S).derivative.eval (imaginaryNode w) := by rw [hε]; ring
      _ = 0 := by rw [hsum]; ring
  have hH : H = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero H
      (f := fun w : S => imaginaryNode w.val)
      (imaginaryNode_injective.comp Subtype.val_injective)
    · exact fun w : S => hHzero w.val w.property
    · simpa using hHdegree
  exact sub_eq_zero.mp hH

def signedFrequencies {ι : Type*} (F : Finset ι) (f : ι → ℝ) : Finset ℝ :=
  F.image f ∪ F.image (fun i => -f i)

theorem signedFrequencies_neg {ι : Type*} (F : Finset ι) (f : ι → ℝ) :
    ∀ w ∈ signedFrequencies F f, -w ∈ signedFrequencies F f := by
  intro w hw
  simp only [signedFrequencies,Finset.mem_union,Finset.mem_image] at hw ⊢
  rcases hw with ⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩
  · exact Or.inr ⟨i,hi,rfl⟩
  · exact Or.inl ⟨i,hi,by simp⟩

def symmetricWeight {ι : Type*} (f m : ι → ℝ) (w : ℝ) (i : ι) : ℝ :=
  (if f i = w then m i/2 else 0)+(if -f i = w then m i/2 else 0)

theorem symmetricWeight_neg {ι : Type*} (f m : ι → ℝ) (w : ℝ) (i : ι) :
    symmetricWeight f m (-w) i = symmetricWeight f m w i := by
  have h₁ : f i = -w ↔ -f i = w := by constructor <;> intro h <;> linarith
  have h₂ : -f i = -w ↔ f i = w := neg_inj
  simp only [symmetricWeight,h₁,h₂]
  ring

theorem symmetricWeight_nonnegative {ι : Type*} (f m : ι → ℝ) (w : ℝ) (i : ι)
    (hm : 0 ≤ m i) : 0 ≤ symmetricWeight f m w i := by
  unfold symmetricWeight
  split_ifs <;> positivity

theorem symmetricWeight_total_positive {ι : Type*}
    (F : Finset ι) (f m : ι → ℝ) (hm : ∀ i ∈ F, 0 < m i)
    (w : ℝ) (hw : w ∈ signedFrequencies F f) :
    0 < ∑ i ∈ F, symmetricWeight f m w i := by
  classical
  obtain ⟨i,hi,hpos⟩ : ∃ i ∈ F, 0 < symmetricWeight f m w i := by
    simp only [signedFrequencies,Finset.mem_union,Finset.mem_image] at hw
    rcases hw with ⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩
    · refine ⟨i,hi,?_⟩
      have h := hm i hi
      simp only [symmetricWeight,if_pos rfl]
      split_ifs <;> positivity
    · refine ⟨i,hi,?_⟩
      have h := hm i hi
      simp only [symmetricWeight,if_pos rfl]
      split_ifs <;> positivity
  exact hpos.trans_le (Finset.single_le_sum
    (fun j hj => symmetricWeight_nonnegative f m w j (hm j hj).le) hi)

/-- Symmetrization is valid even at frequency zero: its two half weights then
add at the same node. -/
theorem symmetricWeight_sum {ι : Type*} (F : Finset ι) (f m : ι → ℝ)
    (i : ι) (hi : i ∈ F) (h : ℝ → ℂ) :
    (∑ w ∈ signedFrequencies F f, (symmetricWeight f m w i : ℂ)*h w) =
      ((m i/2 : ℝ) : ℂ)*(h (f i)+h (-f i)) := by
  classical
  have hfi : f i ∈ signedFrequencies F f := Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
  have hnfi : -f i ∈ signedFrequencies F f := Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
  have hterm (w : ℝ) : (symmetricWeight f m w i : ℂ)*h w =
      (if w = f i then ((m i/2 : ℝ) : ℂ)*h (f i) else 0)+
      (if w = -f i then ((m i/2 : ℝ) : ℂ)*h (-f i) else 0) := by
    by_cases hzero : f i = 0
    · by_cases hw : w = 0
      · subst w
        simp [symmetricWeight,hzero]
        ring
      · simp [symmetricWeight,hzero,hw,Ne.symm hw]
    · have hdist : f i ≠ -f i := by intro h; apply hzero; linarith
      by_cases hw : w = f i
      · subst w
        simp [symmetricWeight,hdist,Ne.symm hdist]
      · by_cases hwn : w = -f i
        · subst w
          simp [symmetricWeight,hdist,Ne.symm hdist]
        · simp [symmetricWeight,hw,hwn,Ne.symm hw,Ne.symm hwn]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq',hfi,hnfi]
  ring

theorem value_negative_frequency (p : ℝ[X]) (w : ℝ) :
    value p (imaginaryNode (-w)) = conj (value p (imaginaryNode w)) := by
  have harg : imaginaryNode (-w) = conj (imaginaryNode w) := by simp [imaginaryNode]
  rw [harg,value_conjugate]

def groupedResidue {ι : Type*} (F : Finset ι) (f m : ι → ℝ)
    (a b : ℝ[X]) (side : ι → Bool) (w : ℝ) : ℂ :=
  ∑ i ∈ F, (symmetricWeight f m w i : ℂ)*conj (value (endpoint a b (side i)) (imaginaryNode w))

theorem groupedResidue_conjugate {ι : Type*} (F : Finset ι) (f m : ι → ℝ)
    (a b : ℝ[X]) (side : ι → Bool) (w : ℝ) :
    groupedResidue F f m a b side (-w) = conj (groupedResidue F f m a b side w) := by
  simp only [groupedResidue,symmetricWeight_neg,value_negative_frequency,map_sum,map_mul]
  simp

/-- Every nontrivial nonnegative combination of endpoint values is nonzero
when the entire denominator segment is stable. -/
theorem positive_endpoint_combination_nonzero
    (a b : ℝ[X]) (hsegment : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t))
    (w α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (htotal : 0 < α+β) :
    (α : ℂ)*value a (imaginaryNode w)+(β : ℂ)*value b (imaginaryNode w) ≠ 0 := by
  let t : ℝ := β/(α+β)
  have ht : t ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hβ htotal.le,(div_le_one htotal).mpr (by linarith)⟩
  have hnz := stable_axis_ne_zero (hsegment t ht) w
  have htotC : ((α+β : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt htotal)
  have htotC' : (α : ℂ)+(β : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt htotal)
  have heq : (α : ℂ)*value a (imaginaryNode w)+(β : ℂ)*value b (imaginaryNode w) =
      ((α+β : ℝ) : ℂ)*value (blend a b t) (imaginaryNode w) := by
    rw [value_blend]
    dsimp [t]
    push_cast
    field_simp [htotC']
  rw [heq]
  exact mul_ne_zero htotC hnz

theorem groupedResidue_ne_zero {ι : Type*}
    (F : Finset ι) (f m : ι → ℝ) (hm : ∀ i ∈ F, 0 < m i)
    (a b : ℝ[X]) (side : ι → Bool)
    (hsegment : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t))
    (w : ℝ) (hw : w ∈ signedFrequencies F f) : groupedResidue F f m a b side w ≠ 0 := by
  let α : ℝ := ∑ i ∈ F, if side i then 0 else symmetricWeight f m w i
  let β : ℝ := ∑ i ∈ F, if side i then symmetricWeight f m w i else 0
  have hα : 0 ≤ α := by
    apply Finset.sum_nonneg
    intro i hi
    cases side i
    · exact symmetricWeight_nonnegative f m w i (hm i hi).le
    · simp
  have hβ : 0 ≤ β := by
    apply Finset.sum_nonneg
    intro i hi
    cases side i
    · simp
    · exact symmetricWeight_nonnegative f m w i (hm i hi).le
  have hsum : α+β = ∑ i ∈ F, symmetricWeight f m w i := by
    dsimp [α,β]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases side i <;> simp
  have htotal : 0 < α+β := by rw [hsum]; exact symmetricWeight_total_positive F f m hm w hw
  have hcomb : (α : ℂ)*value a (imaginaryNode w)+(β : ℂ)*value b (imaginaryNode w) ≠ 0 :=
    positive_endpoint_combination_nonzero a b hsegment w α β hα hβ htotal
  have heq : groupedResidue F f m a b side w =
      conj ((α : ℂ)*value a (imaginaryNode w)+(β : ℂ)*value b (imaginaryNode w)) := by
    simp only [groupedResidue,α,β,map_add,map_mul,map_sum,Complex.conj_ofReal]
    push_cast
    rw [Finset.sum_mul,Finset.sum_mul,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases side i <;> simp [endpoint]
  rw [heq]
  intro hz
  apply hcomb
  simpa using congrArg conj hz

/-! ## 7. 统一排除临界证书 -/

theorem scalar_reflection_degree_bound (P N Q : ℂ[X]) (ε : ℂ)
    (hN : N ≠ 0) (hε : ε ≠ 0) (hQP : Q ∣ P) (hcoprime : IsCoprime Q (reflection P))
    (hidentity : P*N = C ε*reflection (P*N)) : Q.natDegree ≤ N.natDegree := by
  have hdvd : Q ∣ P*N := dvd_mul_of_dvd_left hQP N
  have heq : P*N = reflection P*(C ε*reflection N) := by rw [hidentity,reflection_mul]; ring
  rw [heq] at hdvd
  have hdiv : Q ∣ C ε*reflection N := hcoprime.dvd_of_dvd_mul_left hdvd
  have hnonzero : C ε*reflection N ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hε) (reflection_ne_zero hN)
  have h := Polynomial.natDegree_le_of_dvd hdiv hnonzero
  simpa only [Polynomial.natDegree_C_mul hε,reflection_degree] using h

structure SymmetricContactData {d : ℕ} {a b : ℝ[X]} (Crt : CriticalCertificate d a b) where
  nodes : Finset ℝ
  nodes_nonempty : nodes.Nonempty
  nodes_neg : ∀ w ∈ nodes, -w ∈ nodes
  residue : ℝ → ℂ
  residue_ne_zero : ∀ w ∈ nodes, residue w ≠ 0
  residue_conjugate : ∀ w ∈ nodes, residue (-w) = conj (residue w)
  contact : ∀ w ∈ nodes, (value Crt.numerator (imaginaryNode w)*residue w).re = 0
  moments : ∀ k < d, (∑ w : nodes, residue w.val*(imaginaryNode w.val)^k) = 0
  cross_root : ∀ w ∈ nodes,
    (frequencyCross Crt.numerator a).eval w = 0 ∨ (frequencyCross Crt.numerator b).eval w = 0

/-- Signed contact data are incompatible with a nonzero weak positive-real
support: residue moments and the real-root budget give opposite degree bounds. -/
theorem no_symmetric_contact_data {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (ha : HurwitzClass d a) (hb : HurwitzClass d b)
    (Data : SymmetricContactData Crt) : False := by
  classical
  let P : ℂ[X] := Crt.numerator.map (algebraMap ℝ ℂ)
  have hP : P ≠ 0 := Crt.mapped_numerator_ne_zero
  have hleft : ∀ z : ℂ, P.eval z = 0 → z.re ≤ 0 := by
    simpa only [P,← value_eq_mapped_eval] using Crt.no_open_right_root ha hb.2.1
  have hsimple : ∀ z : ℂ, z.re = 0 → P.eval z = 0 → P.rootMultiplicity z = 1 := by
    intro z hz hr
    exact Crt.axis_root_simple ha hb.2.1 z hz (by simpa only [value_eq_mapped_eval] using hr)
  obtain ⟨Q,_,hQP,hQleft,hQdegree⟩ := strict_factor_and_axis_degree P hP hleft hsimple
  have hcoprime := left_factor_coprime_reflection Q P hQleft hleft
  let N := nodeResidueNumerator Data.nodes Data.residue
  have hN : N ≠ 0 := nodeResidueNumerator_ne_zero Data.nodes Data.nodes_nonempty Data.residue Data.residue_ne_zero
  have hPconj : ∀ w ∈ Data.nodes, P.eval (imaginaryNode (-w)) = conj (P.eval (imaginaryNode w)) := by
    intro w _
    simpa only [P,← value_eq_mapped_eval] using value_negative_frequency Crt.numerator w
  have hidentity := contact_residue_reflection_identity Data.nodes P Data.residue d
    Data.nodes_neg Data.residue_conjugate hPconj
    (by simpa only [P,← value_eq_mapped_eval] using Data.contact)
    Data.moments (by simpa [P] using Crt.numerator_degree) hN
  have hdegree := scalar_reflection_degree_bound P N Q ((-1)^Data.nodes.card)
    hN (pow_ne_zero _ (by norm_num)) hQP hcoprime hidentity
  have hgap := residueNumerator_degree_gap (nodePolynomial Data.nodes)
    (fun w : Data.nodes => imaginaryNode w.val) (fun w : Data.nodes => Data.residue w.val) d Data.moments hN
  have hA : frequencyCross Crt.numerator a ≠ 0 :=
    frequencyCross_ne_zero d _ _ Crt.numerator_ne_zero Crt.numerator_degree ha
  have hB : frequencyCross Crt.numerator b ≠ 0 :=
    frequencyCross_ne_zero d _ _ Crt.numerator_ne_zero Crt.numerator_degree hb
  have hnodes : Data.nodes ⊆ (frequencyCross Crt.numerator a).roots.toFinset ∪
      (frequencyCross Crt.numerator b).roots.toFinset := by
    intro w hw
    rcases Data.cross_root w hw with hr | hr
    · exact Finset.mem_union.mpr (Or.inl (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hA).mpr hr)))
    · exact Finset.mem_union.mpr (Or.inr (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hB).mpr hr)))
  have haxis : axisFrequencies P ⊆ (frequencyCross Crt.numerator a).roots.toFinset ∩
      (frequencyCross Crt.numerator b).roots.toFinset := by
    intro w hw
    have hz : value Crt.numerator (imaginaryNode w) = 0 := by
      simpa only [P,← value_eq_mapped_eval] using (mem_axisFrequencies_iff P hP w).mp hw
    apply Finset.mem_inter.mpr
    constructor
    · apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_roots hA).mpr
      change (frequencyCross Crt.numerator a).eval w = 0
      rw [frequencyCross_eval]
      simp only [imaginaryNode] at hz
      simp [hz,pairing]
    · apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_roots hB).mpr
      change (frequencyCross Crt.numerator b).eval w = 0
      rw [frequencyCross_eval]
      simp only [imaginaryNode] at hz
      simp [hz,pairing]
  have hbudget := signed_contact_budget Crt ha hb Data.nodes (axisFrequencies P) hnodes haxis
  have hdegP : P.natDegree = Crt.numerator.natDegree := by simp [P]
  have hdegD := (nodePolynomial_monic_degree Data.nodes).2
  change N.natDegree+d < (nodePolynomial Data.nodes).natDegree at hgap
  omega

theorem pairing_negative_frequency (c p : ℝ[X]) (w : ℝ) :
    pairing (value c (imaginaryNode (-w))) (value p (imaginaryNode (-w))) =
      pairing (value c (imaginaryNode w)) (value p (imaginaryNode w)) := by
  rw [value_negative_frequency,value_negative_frequency]
  simp [pairing,Complex.mul_re]

theorem frequencyCross_neg_eval (c p : ℝ[X]) (w : ℝ) :
    (frequencyCross c p).eval (-w) = (frequencyCross c p).eval w := by
  rw [frequencyCross_eval,frequencyCross_eval]
  exact pairing_negative_frequency c p w

private theorem real_weighted_pair (u v : ℂ) (r : ℝ) :
    (u*((r : ℂ)*conj v)).re = r*pairing u v := by
  simp [pairing,Complex.mul_re,Complex.mul_im]
  ring

theorem groupedResidue_contact {ι : Type*}
    (F : Finset ι) (f m : ι → ℝ) (c a b : ℝ[X]) (side : ι → Bool)
    (hcontact : ∀ i ∈ F, pairing (value c (imaginaryNode (f i)))
      (value (endpoint a b (side i)) (imaginaryNode (f i))) = 0) (w : ℝ) :
    (value c (imaginaryNode w)*groupedResidue F f m a b side w).re = 0 := by
  classical
  rw [groupedResidue,Finset.mul_sum]
  simp only [Complex.re_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [real_weighted_pair]
  by_cases hp : f i = w
  · have h := hcontact i hi
    rw [hp] at h
    rw [h,mul_zero]
  · by_cases hn : -f i = w
    · have h := pairing_negative_frequency c (endpoint a b (side i)) (f i)
      rw [hn,hcontact i hi] at h
      rw [h,mul_zero]
    · simp [symmetricWeight,hp,hn]

/-- The complex moments of conjugate node pairs are exactly the real
coefficient balance moments, with a factor one-half at each conjugate copy. -/
theorem groupedResidue_moment_identity {ι : Type*}
    (F : Finset ι) (f m : ι → ℝ) (a b : ℝ[X]) (side : ι → Bool) (k : ℕ) :
    (∑ w ∈ signedFrequencies F f, groupedResidue F f m a b side w*(imaginaryNode w)^k) =
      ∑ i ∈ F, (m i : ℂ)*(pairing ((imaginaryNode (f i))^k)
        (value (endpoint a b (side i)) (imaginaryNode (f i))) : ℂ) := by
  classical
  simp only [groupedResidue,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hreassoc : (∑ w ∈ signedFrequencies F f,
      ((symmetricWeight f m w i : ℂ)*conj (value (endpoint a b (side i)) (imaginaryNode w)))*
        (imaginaryNode w)^k) =
      ∑ w ∈ signedFrequencies F f, (symmetricWeight f m w i : ℂ)*
        (conj (value (endpoint a b (side i)) (imaginaryNode w))*(imaginaryNode w)^k) := by
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [hreassoc,symmetricWeight_sum F f m i hi]
  let G : ℂ := conj (value (endpoint a b (side i)) (imaginaryNode (f i)))*(imaginaryNode (f i))^k
  have hnegative : conj (value (endpoint a b (side i)) (imaginaryNode (-f i)))*
      (imaginaryNode (-f i))^k = conj G := by
    rw [value_negative_frequency]
    have harg : imaginaryNode (-f i) = conj (imaginaryNode (f i)) := by
      simp [imaginaryNode]
    rw [harg]
    simp [G]
  rw [hnegative]
  have hsum : G+conj G = ((2*G.re : ℝ) : ℂ) := by
    simpa [pairing] using complex_pair_sum G 1
  change ((m i/2 : ℝ) : ℂ)*(G+conj G) = _
  rw [hsum]
  have hpair : G.re = pairing ((imaginaryNode (f i))^k)
      (value (endpoint a b (side i)) (imaginaryNode (f i))) := by
    unfold G pairing
    congr 1
    ring
  rw [hpair]
  push_cast
  ring

theorem CriticalCertificate.symmetric_data {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (ha : HurwitzClass d a) (hb : HurwitzClass d b)
    (hsegment : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t)) :
    Nonempty (SymmetricContactData Crt) := by
  classical
  let F := Crt.finiteAtoms
  let f := Crt.frequency
  let m := Crt.finiteMass
  let side := Crt.coordinates.right
  let S := signedFrequencies F f
  let r := groupedResidue F f m a b side
  have hF : F.Nonempty := Crt.finiteAtoms_nonempty ha hb
  have hm : ∀ i ∈ F, 0 < m i := fun i hi => Crt.finiteMass_positive hi
  have hcontact : ∀ i ∈ F, pairing (value Crt.numerator (imaginaryNode (f i)))
      (value (endpoint a b (side i)) (imaginaryNode (f i))) = 0 := by
    intro i hi
    exact Crt.finite_contact ha hb hi
  refine ⟨{
    nodes := S
    nodes_nonempty := ?_
    nodes_neg := signedFrequencies_neg F f
    residue := r
    residue_ne_zero := groupedResidue_ne_zero F f m hm a b side hsegment
    residue_conjugate := fun w _ => groupedResidue_conjugate F f m a b side w
    contact := fun w _ => groupedResidue_contact F f m Crt.numerator a b side hcontact w
    moments := ?_
    cross_root := ?_
  }⟩
  · obtain ⟨i,hi⟩ := hF
    exact ⟨f i,Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i,hi,rfl⟩))⟩
  · intro k hk
    have h := groupedResidue_moment_identity F f m a b side k
    have hzero := congrArg (fun x : ℝ => (x : ℂ)) (Crt.finite_moments ha hb k hk)
    push_cast at hzero
    have hsum : (∑ w ∈ S, r w*(imaginaryNode w)^k) = 0 := by
      rw [h]
      exact hzero
    exact (Finset.sum_coe_sort (s := S)
      (f := fun w : ℝ => r w*(imaginaryNode w)^k)).trans hsum
  · intro w hw
    have hroot (i : Fin Crt.count) (hi : i ∈ F) :
        (frequencyCross Crt.numerator (Crt.denominator i)).eval (f i) = 0 := by
      rw [frequencyCross_eval]
      exact Crt.finite_contact ha hb hi
    simp only [S,signedFrequencies,Finset.mem_union,Finset.mem_image] at hw
    rcases hw with ⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩
    · have hr := hroot i hi
      cases hs : Crt.coordinates.right i
      · left
        simpa [CriticalCertificate.denominator,endpoint,hs] using hr
      · right
        simpa [CriticalCertificate.denominator,endpoint,hs] using hr
    · have hr : (frequencyCross Crt.numerator (Crt.denominator i)).eval (-f i) = 0 := by
        rw [frequencyCross_neg_eval]
        exact hroot i hi
      cases hs : Crt.coordinates.right i
      · left
        simpa [CriticalCertificate.denominator,endpoint,hs] using hr
      · right
        simpa [CriticalCertificate.denominator,endpoint,hs] using hr

theorem no_critical_certificate {d : ℕ} {a b : ℝ[X]}
    (Crt : CriticalCertificate d a b) (ha : HurwitzClass d a) (hb : HurwitzClass d b)
    (hsegment : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t)) : False := by
  obtain ⟨Data⟩ := Crt.symmetric_data ha hb hsegment
  exact no_symmetric_contact_data Crt ha hb Data

theorem blend_initial_subsegment (a b : ℝ[X]) (t u : ℝ) :
    blend a (blend a b t) u = blend a b (u*t) := by
  ext k
  simp only [coeff_blend]
  ring

end

end Core

/-! ## 六阶系数接口与多项式表示之间的对应 -/

noncomputable section

def jw (ω : ℝ) : ℂ := Complex.I * (ω : ℂ)

structure MonicSextic where
  a1 : ℝ
  a2 : ℝ
  a3 : ℝ
  a4 : ℝ
  a5 : ℝ
  a6 : ℝ

namespace MonicSextic

def eval (a : MonicSextic) (s : ℂ) : ℂ :=
  s ^ 6 + (a.a1 : ℂ) * s ^ 5 + (a.a2 : ℂ) * s ^ 4 +
    (a.a3 : ℂ) * s ^ 3 + (a.a4 : ℂ) * s ^ 2 +
    (a.a5 : ℂ) * s + (a.a6 : ℂ)

def realPolynomial (a : MonicSextic) : Polynomial ℝ :=
  Polynomial.X ^ 6 + Polynomial.C a.a1 * Polynomial.X ^ 5 +
    Polynomial.C a.a2 * Polynomial.X ^ 4 +
    Polynomial.C a.a3 * Polynomial.X ^ 3 +
    Polynomial.C a.a4 * Polynomial.X ^ 2 +
    Polynomial.C a.a5 * Polynomial.X + Polynomial.C a.a6

lemma realPolynomial_monic (a : MonicSextic) :
    a.realPolynomial.Monic := by
  have heq : a.realPolynomial = Polynomial.X ^ 6 +
      (Polynomial.C a.a1 * Polynomial.X ^ 5 +
        Polynomial.C a.a2 * Polynomial.X ^ 4 +
        Polynomial.C a.a3 * Polynomial.X ^ 3 +
        Polynomial.C a.a4 * Polynomial.X ^ 2 +
        Polynomial.C a.a5 * Polynomial.X + Polynomial.C a.a6) := by
    unfold realPolynomial
    ring
  rw [heq]
  apply Polynomial.monic_X_pow_add
  have hle :
      (Polynomial.C a.a1 * Polynomial.X ^ 5 +
        Polynomial.C a.a2 * Polynomial.X ^ 4 +
        Polynomial.C a.a3 * Polynomial.X ^ 3 +
        Polynomial.C a.a4 * Polynomial.X ^ 2 +
        Polynomial.C a.a5 * Polynomial.X + Polynomial.C a.a6).degree ≤ 5 := by
    compute_degree!
  exact lt_of_le_of_lt hle (by norm_num)

def evalJW (a : MonicSextic) (ω : ℝ) : ℂ := a.eval (jw ω)

/-- Actual root-location version of Hurwitz stability. -/
def Hurwitz (a : MonicSextic) : Prop :=
  ∀ s : ℂ, a.eval s = 0 → s.re < 0

def convex (a b : MonicSextic) (r : ℝ) : MonicSextic where
  a1 := (1 - r) * a.a1 + r * b.a1
  a2 := (1 - r) * a.a2 + r * b.a2
  a3 := (1 - r) * a.a3 + r * b.a3
  a4 := (1 - r) * a.a4 + r * b.a4
  a5 := (1 - r) * a.a5 + r * b.a5
  a6 := (1 - r) * a.a6 + r * b.a6

@[simp] lemma convex_zero (a b : MonicSextic) : a.convex b 0 = a := by
  cases a
  simp [convex]

@[simp] lemma convex_one (a b : MonicSextic) : a.convex b 1 = b := by
  cases b
  simp [convex]

lemma convex_convex_left
    (a b : MonicSextic) (u r : ℝ) :
    a.convex (a.convex b u) r = a.convex b (r * u) := by
  cases a
  cases b
  dsimp [convex]
  congr 1 <;> ring

def AllConvexHurwitz (a b : MonicSextic) : Prop :=
  ∀ r : ℝ, 0 ≤ r → r ≤ 1 → (a.convex b r).Hurwitz

lemma allConvexHurwitz_initial
    {a b : MonicSextic} (h : a.AllConvexHurwitz b)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    a.AllConvexHurwitz (a.convex b u) := by
  intro r hr0 hr1
  rw [convex_convex_left]
  have hru0 : 0 ≤ r * u := mul_nonneg hr0 hu0
  have hruu : r * u ≤ u := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr1) hu0]
  exact h (r * u) hru0 (hruu.trans hu1)

def SPRFor (a n : MonicSextic) : Prop :=
  a.Hurwitz ∧ ∀ ω : ℝ, 0 < ((n.evalJW ω) / a.evalJW ω).re

def ExistsCommonSPR (a b : MonicSextic) : Prop :=
  ∃ n : MonicSextic, a.SPRFor n ∧ b.SPRFor n

lemma realPolynomial_natDegree (a : MonicSextic) : a.realPolynomial.natDegree = 6 := by
  unfold realPolynomial
  compute_degree!

@[simp] lemma value_realPolynomial (a : MonicSextic) (z : ℂ) :
    Core.value a.realPolynomial z = a.eval z := by
  simp [Core.value, realPolynomial, eval]

lemma stable_iff_hurwitz (a : MonicSextic) : Core.Stable a.realPolynomial ↔ a.Hurwitz := by
  constructor
  · intro h z hz
    by_contra hnot
    exact h z (le_of_not_gt hnot) (by simpa only [value_realPolynomial] using hz)
  · intro h z hz heq
    exact (not_lt_of_ge hz) (h z (by simpa only [value_realPolynomial] using heq))

lemma realPolynomial_convex (a b : MonicSextic) (t : ℝ) :
    (a.convex b t).realPolynomial = Core.blend a.realPolynomial b.realPolynomial t := by
  unfold convex realPolynomial Core.blend
  simp only [map_add, map_mul, map_sub, map_one]
  ring

lemma spr_iff (a n : MonicSextic) : Core.SPR n.realPolynomial a.realPolynomial ↔ a.SPRFor n := by
  constructor
  · rintro ⟨ha, hf⟩
    refine ⟨(stable_iff_hurwitz a).mp ha, fun ω => ?_⟩
    simpa [evalJW, jw, mul_comm] using hf ω
  · rintro ⟨ha, hf⟩
    refine ⟨(stable_iff_hurwitz a).mpr ha, fun ω => ?_⟩
    simpa [evalJW, jw, mul_comm] using hf ω

def ofPolynomial (p : Polynomial ℝ) : MonicSextic :=
  ⟨p.coeff 5, p.coeff 4, p.coeff 3, p.coeff 2, p.coeff 1, p.coeff 0⟩

lemma realPolynomial_ofPolynomial (p : Polynomial ℝ) (hp : p.Monic) (hd : p.natDegree = 6) :
    (ofPolynomial p).realPolynomial = p := by
  have h6 : p.coeff 6 = 1 := by simpa [hd] using hp.coeff_natDegree
  ext k
  by_cases hk : k ≤ 6
  · interval_cases k <;> simp [realPolynomial, ofPolynomial, h6]
  · have hpk : p.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have h0 : k ≠ 0 := by omega
    have h1 : k ≠ 1 := by omega
    have h2 : k ≠ 2 := by omega
    have h3 : k ≠ 3 := by omega
    have h4 : k ≠ 4 := by omega
    have h5 : k ≠ 5 := by omega
    have h6k : k ≠ 6 := by omega
    simp [realPolynomial, ofPolynomial, Polynomial.coeff_X, Polynomial.coeff_C,
      hpk, h0, h1, h1.symm, h2, h3, h4, h5, h6k]

lemma exists_common_polynomial_iff (a b : MonicSextic) :
    (∃ c : Polynomial ℝ, c.Monic ∧ c.natDegree = 6 ∧
      Core.SPR c a.realPolynomial ∧ Core.SPR c b.realPolynomial) ↔ a.ExistsCommonSPR b := by
  constructor
  · rintro ⟨c, hc, hd, hA, hB⟩
    have hrep := realPolynomial_ofPolynomial c hc hd
    refine ⟨ofPolynomial c, (spr_iff a _).mp ?_, (spr_iff b _).mp ?_⟩
    · simpa only [hrep] using hA
    · simpa only [hrep] using hB
  · rintro ⟨n, hA, hB⟩
    exact ⟨n.realPolynomial, n.realPolynomial_monic, n.realPolynomial_natDegree,
      (spr_iff a n).mpr hA, (spr_iff b n).mpr hB⟩

lemma segment_stable_iff (a b : MonicSextic) :
    (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Core.Stable (Core.blend a.realPolynomial b.realPolynomial t)) ↔ a.AllConvexHurwitz b := by
  constructor
  · intro h t ht0 ht1
    apply (stable_iff_hurwitz _).mp
    rw [realPolynomial_convex]
    exact h t ⟨ht0, ht1⟩
  · intro h t ht
    rw [← realPolynomial_convex]
    exact (stable_iff_hurwitz _).mpr (h t ht.1 ht.2)

end MonicSextic

/-! ## 六阶充分性：直接排除临界证书，不调用任意阶综合主定理 -/

theorem stable_segment_commonSPR {a b : MonicSextic} (hsegment : a.AllConvexHurwitz b) :
    a.ExistsCommonSPR b := by
  classical
  by_contra hno
  have hfull (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      Core.HurwitzClass 6 (Core.blend a.realPolynomial b.realPolynomial t) := by
    rw [← MonicSextic.realPolynomial_convex]
    exact ⟨(a.convex b t).realPolynomial_monic, (a.convex b t).realPolynomial_natDegree,
      (MonicSextic.stable_iff_hurwitz _).mpr (hsegment t ht.1 ht.2)⟩
  have hfail : ¬∃ c : Polynomial ℝ, c.Monic ∧ c.natDegree = 6 ∧
      Core.SPR c a.realPolynomial ∧ Core.SPR c b.realPolynomial :=
    fun hc => hno ((MonicSextic.exists_common_polynomial_iff a b).mp hc)
  obtain ⟨t, ht, ⟨Crt⟩⟩ :=
    Core.critical_certificate_of_failed_segment 6 a.realPolynomial b.realPolynomial hfull hfail
  have hA : Core.HurwitzClass 6 a.realPolynomial := by
    simpa [Core.blend] using hfull 0 (by constructor <;> norm_num)
  apply Core.no_critical_certificate Crt hA (hfull t ht)
  simpa only [MonicSextic.realPolynomial_convex] using
    (MonicSextic.segment_stable_iff a (a.convex b t)).mpr
      (MonicSextic.allConvexHurwitz_initial hsegment ht.1 ht.2)

/-- 必要性独立保留：公共 SPR 分子保证整条分母线段 Hurwitz。 -/
theorem allConvexHurwitz_of_commonSPR {a b : MonicSextic} (hcommon : a.ExistsCommonSPR b) :
    a.AllConvexHurwitz b := by
  obtain ⟨n, hA, hB⟩ := hcommon
  apply (MonicSextic.segment_stable_iff a b).mp
  intro t ht
  exact (Core.common_spr_implies_segment_hurwitz a.realPolynomial_monic b.realPolynomial_monic
    a.realPolynomial_natDegree b.realPolynomial_natDegree
    ((MonicSextic.spr_iff a n).mpr hA) ((MonicSextic.spr_iff b n).mpr hB) t ht).2.2

/-- 与原文件同一形式的完整六阶主定理。 -/
theorem sixth_order_main (a b : MonicSextic) : a.ExistsCommonSPR b ↔ a.AllConvexHurwitz b :=
  ⟨allConvexHurwitz_of_commonSPR, stable_segment_commonSPR⟩

/-- 任一公共端点分子，对整条分母线段仍然满足 SPR。 -/
theorem commonSPR_on_whole_segment {a b : MonicSextic} (hcommon : a.ExistsCommonSPR b) :
    ∃ n : MonicSextic, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (a.convex b t).SPRFor n := by
  obtain ⟨n, hA, hB⟩ := hcommon
  refine ⟨n, fun t ht0 ht1 => (MonicSextic.spr_iff _ n).mp ?_⟩
  rw [MonicSextic.realPolynomial_convex]
  exact Core.common_spr_extends_to_segment a.realPolynomial_monic b.realPolynomial_monic
    a.realPolynomial_natDegree b.realPolynomial_natDegree
    ((MonicSextic.spr_iff a n).mpr hA) ((MonicSextic.spr_iff b n).mpr hB) t ⟨ht0, ht1⟩

/-- 稳定六阶线段具有同一个适用于全部参数、全部实频率的首一六阶分子。 -/
theorem stable_segment_commonSPR_on_whole_segment {a b : MonicSextic}
    (hsegment : a.AllConvexHurwitz b) :
    ∃ n : MonicSextic, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (a.convex b t).SPRFor n :=
  commonSPR_on_whole_segment (stable_segment_commonSPR hsegment)

end

end MKNumina.SPR.Simplified.SixthOrder

#print axioms MKNumina.SPR.Simplified.SixthOrder.sixth_order_main
#print axioms MKNumina.SPR.Simplified.SixthOrder.stable_segment_commonSPR_on_whole_segment
