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
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Polynomial.Basic

/-!
# 线段多项式公共正实分子：自包含的统一证明

本文件只导入 Mathlib，已内嵌并合并 n_random2.lean 的所需基础代码。
基础引理置于 SPR.TeacherCore，低一阶综合置于 SPR.LowerNumeratorTeacher，
因此可与原 n_random2.lean 同时导入。

对首一 n 阶分母 a、b，充分性只保留一条主线：
稳定线段 → 首一 n−1 阶公共分子 → 小扰动与首一化 → 首一 n 阶公共分子。
低一阶存在性使用 2(n−1) 次频率紧化、凸分离、临界支撑和留数反射。
有限频率与无穷远接触共用根位置引理及同一个计数矛盾。
同阶结论另覆盖 n=0，不再重复整套凸几何与接触证书构造。

主要入口：
* SPR.LowerNumeratorTeacher.lower_synthesis_statement：n>0 的低一阶存在性。
* SPR.LowerNumeratorTeacher.lower_common_spr_iff_stable_segment：低一阶的完整等价。
* SPR.LowerNumeratorTeacher.lower_common_numerator_on_whole_segment：低一阶分子适用整段。
* SPR.TeacherCore.common_spr_iff_stable_segment：同阶的完整等价，含 n=0。
* SPR.TeacherCore.common_spr_on_whole_segment：同阶分子适用整段。

SPR 定义只记录分母稳定性和所有有限实频率的严格正性。
分子的首一性质和精确次数均在最终定理中单独列出。
-/

set_option maxHeartbeats 800000

namespace SPR.TeacherCore

noncomputable section

open Polynomial Set Filter
open scoped Topology ComplexConjugate

/-! ## 基本定义与稳定线段的零点排除 -/

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

/-! ## 正比例缩放、系数空间与凸分离 -/

theorem frequencyPositive_scale {c p : ℝ[X]} (h : FrequencyPositive c p)
    (r : ℝ) (hr : 0 < r) : FrequencyPositive (C r*c) p := by
  intro w
  have heq : value (C r*c) (w*Complex.I) = (r : ℂ)*value c (w*Complex.I) := by
    simp [value]
  rw [heq, mul_div_assoc, Complex.mul_re]
  simpa only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using mul_pos hr (h w)

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

/-! ## 从虚轴非负性到右半平面非负性 -/

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

/-! ## 多项式反射与频率交叉多项式 -/

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

/-! ## 根因子分解与虚轴零点计数 -/

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

/-! ## 留数矩与节点多项式 -/

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

/-! ## 正负频率对称化与留数分组 -/

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

theorem blend_initial_subsegment (a b : ℝ[X]) (t u : ℝ) :
    blend a (blend a b t) u = blend a b (u*t) := by
  ext k
  simp only [coeff_blend]
  ring

end
end SPR.TeacherCore

namespace SPR.LowerNumeratorTeacher

noncomputable section

open Polynomial Set Filter
open scoped Topology ComplexConjugate
open SPR.TeacherCore

set_option maxHeartbeats 800000

/-- 论文低一阶步骤的目标：分母次数由外部假设固定为 n。 -/
def LowerCommonNumerator (n : ℕ) (a b c : ℝ[X]) : Prop :=
  c.Monic ∧ c.natDegree = n-1 ∧ FrequencyPositive c a ∧ FrequencyPositive c b

/-- 正确的一般存在性命题；证明见文末 lower_synthesis_statement。 -/
def LowerSynthesisStatement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ a b : ℝ[X],
    a.Monic → b.Monic → a.natDegree = n → b.natDegree = n →
    (∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t)) →
    ∃ c : ℝ[X], LowerCommonNumerator n a b c

/-! ## 已有一个分子时 必要性与端点扩展 -/

theorem lower_numerator_necessity
    (n : ℕ) (a b c : ℝ[X])
    (ha : a.Monic) (hb : b.Monic)
    (hda : a.natDegree = n) (hdb : b.natDegree = n)
    (hstableA : Stable a) (hc : LowerCommonNumerator n a b c) :
    ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t) := by
  exact stable_segment_of_axis_nonvanishing ha hb hda hdb hstableA
    (fun t ht w => segment_axis_nonvanishing hc.2.2.1 hc.2.2.2 t ht w)

/-- 同一个低阶分子在两个端点的频率正性与在整条线段的频率正性等价。 -/
theorem endpoint_frequency_iff_whole_segment (a b c : ℝ[X]) :
    (FrequencyPositive c a ∧ FrequencyPositive c b) ↔
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → FrequencyPositive c (blend a b t) := by
  constructor
  · rintro ⟨hA,hB⟩ t ht
    exact frequency_positive_on_segment hA hB t ht
  · intro h
    constructor
    · simpa [blend] using h 0 (by constructor <;> norm_num)
    · simpa [blend] using h 1 (by constructor <;> norm_num)

theorem lower_numerator_on_whole_segment
    {n : ℕ} {a b c : ℝ[X]} (hc : LowerCommonNumerator n a b c)
    (hstable : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t)) :
    c.Monic ∧ c.natDegree = n-1 ∧
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → SPR.TeacherCore.SPR c (blend a b t) := by
  refine ⟨hc.1,hc.2.1,fun t ht => ⟨hstable t ht,?_⟩⟩
  exact frequency_positive_on_segment hc.2.2.1 hc.2.2.2 t ht

/-- n>0 时，低于 n 阶的分子最高坐标为零。 -/
theorem lower_top_coefficient_zero
    {n : ℕ} (hn : 0 < n) {c : ℝ[X]} (hc : c.natDegree ≤ n-1) :
    c.coeff n = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-! ## 一次分母 零阶分子 -/

theorem stable_linear_iff (α : ℝ) : Stable (X+C α) ↔ 0 < α := by
  constructor
  · intro h
    by_contra hn
    have hre : 0 ≤ (-α : ℂ).re := by simp; linarith [le_of_not_gt hn]
    have hz := h (-α) hre
    simp [value] at hz
  · intro h z hz hzero
    have heq : z+(α : ℂ) = 0 := by simpa [value] using hzero
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re,Complex.ofReal_re,Complex.zero_re] at hre
    linarith

theorem constant_one_frequency_positive (α : ℝ) (hα : 0 < α) :
    FrequencyPositive (1 : ℝ[X]) (X+C α) := by
  intro w
  apply (positive_quotient_iff _ _ (stable_axis_ne_zero ((stable_linear_iff α).mpr hα) w)).mpr
  simpa [value,pairing,Complex.mul_re,Complex.mul_im] using hα

/-- n=1：a、b 为一次，公共分子为常数 1，次数恰为 0。 -/
theorem first_order_lower_numerator
    (a b : ℝ[X]) (ha : a.Monic) (hb : b.Monic)
    (hda : a.natDegree = 1) (hdb : b.natDegree = 1)
    (hA : Stable a) (hB : Stable b) :
    LowerCommonNumerator 1 a b 1 := by
  have hα : 0 < a.coeff 0 := (stable_linear_iff _).mp (by rwa [← ha.eq_X_add_C hda])
  have hβ : 0 < b.coeff 0 := (stable_linear_iff _).mp (by rwa [← hb.eq_X_add_C hdb])
  refine ⟨Polynomial.monic_one,by norm_num,?_,?_⟩
  · rw [ha.eq_X_add_C hda]
    exact constant_one_frequency_positive _ hα
  · rw [hb.eq_X_add_C hdb]
    exact constant_one_frequency_positive _ hβ

/-- 一次情形的完整存在性和必要性，分母始终保持一次。 -/
theorem first_order_lower_iff
    (a b : ℝ[X]) (ha : a.Monic) (hb : b.Monic)
    (hda : a.natDegree = 1) (hdb : b.natDegree = 1)
    (hA : Stable a) (hB : Stable b) :
    (∃ c, LowerCommonNumerator 1 a b c) ↔
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t) := by
  constructor
  · rintro ⟨c,hc⟩
    exact lower_numerator_necessity 1 a b c ha hb hda hdb hA hc
  · intro _
    exact ⟨1,first_order_lower_numerator a b ha hb hda hdb hA hB⟩

/-! ## 稳定分母的两个系数性质 -/

/-- 首一稳定多项式在非负实轴上的值严格为正。 -/
theorem stable_monic_eval_pos
    {p : ℝ[X]} (hp : p.Monic) (hs : Stable p)
    (hdeg : 0 < p.natDegree) (x : ℝ) (hx : 0 ≤ x) :
    0 < p.eval x := by
  have htop : Tendsto (fun t : ℝ => p.eval t) atTop atTop :=
    p.tendsto_atTop_of_leadingCoeff_nonneg
      (Polynomial.natDegree_pos_iff_degree_pos.mp hdeg) (by rw [hp.leadingCoeff]; norm_num)
  obtain ⟨R,hxR,hR⟩ :=
    ((eventually_ge_atTop x).and (htop.eventually (eventually_gt_atTop 0))).exists
  by_contra hnot
  obtain ⟨r,hr,heq⟩ := intermediate_value_Icc hxR p.continuous.continuousOn
    (show 0 ∈ Icc (p.eval x) (p.eval R) from ⟨le_of_not_gt hnot,hR.le⟩)
  have hne := hs (r : ℂ) (by simpa using hx.trans hr.1)
  apply hne
  change Polynomial.eval₂ (algebraMap ℝ ℂ) (algebraMap ℝ ℂ r) p = 0
  change p.eval r = 0 at heq
  rw [Polynomial.eval₂_at_apply,heq,map_zero]

theorem stable_monic_constant_pos
    {p : ℝ[X]} (hp : p.Monic) (hs : Stable p) (hdeg : 0 < p.natDegree) :
    0 < p.coeff 0 := by
  have h := stable_monic_eval_pos hp hs hdeg 0 le_rfl
  rwa [← Polynomial.coeff_zero_eq_eval_zero] at h

private theorem real_sum_neg
    (s : Multiset ℂ) (hs : ∀ z ∈ s, z.re < 0) (hne : s ≠ 0) :
    s.sum.re < 0 := by
  induction s using Multiset.induction_on with
  | empty => exact (hne rfl).elim
  | @cons z s ih =>
    have hz : z.re < 0 := hs z (by simp)
    by_cases hsz : s = 0
    · simpa [hsz] using hz
    · have ht := ih (fun w hw => hs w (by simp [hw])) hsz
      simpa only [Multiset.sum_cons,Complex.add_re] using add_neg hz ht

/-- 严格左侧根的实部之和为负，因此首一多项式的次首项系数为正。 -/
theorem stable_monic_next_coefficient_pos
    {n : ℕ} {p : ℝ[X]} (hn : 0 < n)
    (hp : p.Monic) (hdeg : p.natDegree = n) (hs : Stable p) :
    0 < p.coeff (n-1) := by
  let P : ℂ[X] := p.map (algebraMap ℝ ℂ)
  have hP : P.Monic := hp.map _
  have hndeg : P.natDegree = n := by simp [P,hdeg]
  have hsplit : P.Splits (RingHom.id ℂ) := IsAlgClosed.splits_codomain _
  have hne : P.roots ≠ 0 := by
    intro hz
    have hc := Polynomial.splits_iff_card_roots.mp hsplit
    rw [hz,Multiset.card_zero,hndeg] at hc
    omega
  have hleft (z : ℂ) (hz : z ∈ P.roots) : z.re < 0 := by
    have hroot : P.eval z = 0 := (Polynomial.mem_roots hP.ne_zero).mp hz
    by_contra hnot
    apply hs z (le_of_not_gt hnot)
    simpa only [P,← value_eq_mapped_eval] using hroot
  have hsum := real_sum_neg P.roots hleft hne
  have hnext : P.nextCoeff = (p.coeff (n-1) : ℂ) := by
    rw [Polynomial.nextCoeff_of_natDegree_pos (by omega),hndeg]
    simp [P]
  have heq := congrArg Complex.re
    (Polynomial.sum_roots_eq_nextCoeff_of_monic_of_split hP hsplit)
  rw [hnext] at heq
  simp only [Complex.ofReal_re,Complex.neg_re] at heq
  linarith

/-! ## 二次分母 一次分子 -/

/-- 对 p=s²+αs+β，c=s+r 的交叉实部为 (α-r)ω²+rβ。 -/
theorem quadratic_pairing
    {p : ℝ[X]} (hp : p.Monic) (hdeg : p.natDegree = 2) (r w : ℝ) :
    pairing (value (X+C r) (w*Complex.I)) (value p (w*Complex.I)) =
      (p.coeff 1-r)*w^2+r*p.coeff 0 := by
  have htop : p.coeff 2 = 1 := by simpa [← hdeg] using hp.coeff_natDegree
  have heval (z : ℂ) :
      value p z = z^2+(p.coeff 1 : ℂ)*z+(p.coeff 0 : ℂ) := by
    rw [value,Polynomial.aeval_eq_sum_range,hdeg]
    norm_num [Finset.sum_range_succ,htop]
    ring
  rw [heval]
  simp [value,pairing,pow_two,Complex.mul_re,Complex.mul_im]
  ring

theorem quadratic_lower_frequency_positive
    {p : ℝ[X]} (hp : p.Monic) (hdeg : p.natDegree = 2) (hs : Stable p)
    {r : ℝ} (hr : 0 < r) (hrp : r < p.coeff 1) :
    FrequencyPositive (X+C r) p := by
  have hp0 : 0 < p.coeff 0 := stable_monic_constant_pos hp hs (by omega)
  intro w
  apply (positive_quotient_iff _ _ (stable_axis_ne_zero hs w)).mpr
  rw [quadratic_pairing hp hdeg]
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_pos.mpr hrp).le (sq_nonneg w)) (mul_pos hr hp0)

/-- n=2：取 r=min(a₁,b₁)/2，c=s+r 对两个稳定二次分母同时适用。 -/
theorem second_order_lower_numerator
    (a b : ℝ[X]) (ha : a.Monic) (hb : b.Monic)
    (hda : a.natDegree = 2) (hdb : b.natDegree = 2)
    (hA : Stable a) (hB : Stable b) :
    ∃ c : ℝ[X], LowerCommonNumerator 2 a b c := by
  have ha1 : 0 < a.coeff 1 :=
    stable_monic_next_coefficient_pos (by norm_num : 0 < (2 : ℕ)) ha hda hA
  have hb1 : 0 < b.coeff 1 :=
    stable_monic_next_coefficient_pos (by norm_num : 0 < (2 : ℕ)) hb hdb hB
  let r := min (a.coeff 1) (b.coeff 1)/2
  have hr : 0 < r := div_pos (lt_min ha1 hb1) (by norm_num)
  have hra : r < a.coeff 1 := by dsimp [r]; nlinarith [min_le_left (a.coeff 1) (b.coeff 1)]
  have hrb : r < b.coeff 1 := by dsimp [r]; nlinarith [min_le_right (a.coeff 1) (b.coeff 1)]
  refine ⟨X+C r,Polynomial.monic_X_add_C _,?_,?_,?_⟩
  · simp
  · exact quadratic_lower_frequency_positive ha hda hA hr hra
  · exact quadratic_lower_frequency_positive hb hdb hB hr hrb

/-! ## 为什么至多 n−1 阶自动成为恰好 n−1 阶 -/

private theorem reflect_eval_inverse (n : ℕ) (P : ℂ[X]) (hP : P.natDegree ≤ n)
    (z : ℂ) (hz : z ≠ 0) :
    (Polynomial.reflect n P).eval z = z^n*P.eval z⁻¹ := by
  letI : Invertible (z⁻¹) := invertibleOfNonzero (inv_ne_zero hz)
  have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) z⁻¹ n P hP
  simp only [invOf_eq_inv,inv_inv] at h
  change (Polynomial.reflect n P).eval z*(z⁻¹)^n = P.eval z⁻¹ at h
  have hinv : (z⁻¹)^n*z^n = 1 := by rw [← mul_pow,inv_mul_cancel₀ hz,one_pow]
  calc
    _ = (Polynomial.reflect n P).eval z*((z⁻¹)^n*z^n) := by rw [hinv,mul_one]
    _ = ((Polynomial.reflect n P).eval z*(z⁻¹)^n)*z^n := by ring
    _ = P.eval z⁻¹*z^n := by rw [h]
    _ = _ := mul_comm _ _

/-- 反转把过大的次数差变成原点的多重零点，与弱正实性的一重性矛盾。 -/
theorem weak_positive_real_degree_gap
    (n : ℕ) (P D : ℂ[X]) (hP : P ≠ 0)
    (hPdegree : P.natDegree ≤ n) (hDdegree : D.natDegree ≤ n)
    (hDtop : D.coeff n ≠ 0)
    (hD : ∀ z : ℂ, 0 ≤ z.re → D.eval z ≠ 0)
    (hweak : ∀ z : ℂ, 0 ≤ z.re → 0 ≤ (P.eval z/D.eval z).re) :
    n ≤ P.natDegree+1 := by
  by_contra hnot
  have hn : 2 ≤ n := by omega
  have hPn : P.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hPn1 : P.coeff (n-1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  let RP := Polynomial.reflect n P
  let RD := Polynomial.reflect n D
  have hRP : RP ≠ 0 := by
    intro hz
    exact hP (Polynomial.reflect_eq_zero_iff.mp hz)
  have hRPzero : RP.eval 0 = 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    simpa only [RP,Polynomial.coeff_reflect,Polynomial.revAt_zero] using hPn
  have hRDzero : RD.eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    simpa only [RD,Polynomial.coeff_reflect,Polynomial.revAt_zero] using hDtop
  have hinvre (z : ℂ) (hz : 0 ≤ z.re) : 0 ≤ (z⁻¹).re := by
    rw [Complex.inv_re]
    exact div_nonneg hz (Complex.normSq_nonneg z)
  have hRD : ∀ z : ℂ, 0 ≤ z.re → RD.eval z ≠ 0 := by
    intro z hz
    by_cases hz0 : z = 0
    · simpa only [hz0] using hRDzero
    · rw [show RD = Polynomial.reflect n D from rfl,reflect_eval_inverse n D hDdegree z hz0]
      exact mul_ne_zero (pow_ne_zero _ hz0) (hD z⁻¹ (hinvre z hz))
  have hRPweak : ∀ z : ℂ, 0 ≤ z.re → 0 ≤ (RP.eval z/RD.eval z).re := by
    intro z hz
    by_cases hz0 : z = 0
    · simp only [hz0,hRPzero,zero_div,Complex.zero_re,le_refl]
    · rw [show RP = Polynomial.reflect n P from rfl,show RD = Polynomial.reflect n D from rfl,
        reflect_eval_inverse n P hPdegree z hz0,reflect_eval_inverse n D hDdegree z hz0,
        mul_div_mul_left _ _ (pow_ne_zero n hz0)]
      exact hweak z⁻¹ (hinvre z hz)
  have hmult := weak_positive_real_axis_root_simple RP RD hRP hRD hRPweak 0 (by simp) hRPzero
  have hderiv : RP.derivative.eval 0 = 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_derivative]
    simpa only [RP,zero_add,Polynomial.coeff_reflect,
      Polynomial.revAt_le (show 1 ≤ n by omega),Nat.cast_zero,Nat.cast_one,mul_one] using hPn1
  have hlarge : 1 < RP.rootMultiplicity 0 :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hRP).mpr ⟨hRPzero,hderiv⟩
  omega

/-- 非零弱正实的低阶分子也必须恰为 n−1 阶。 -/
theorem weak_lower_numerator_degree_exact
    {n : ℕ} (hn : 0 < n) {c p : ℝ[X]}
    (hc : c ≠ 0) (hcdeg : c.natDegree ≤ n-1)
    (hp : HurwitzClass n p)
    (hfreq : ∀ w : ℝ, 0 ≤ (value c (w*Complex.I)/value p (w*Complex.I)).re) :
    c.natDegree = n-1 := by
  have hweak := right_half_plane_real_nonnegative n c p (by omega) hp
    (by rw [lower_top_coefficient_zero hn hcdeg]) hfreq
  let P := c.map (algebraMap ℝ ℂ)
  let D := p.map (algebraMap ℝ ℂ)
  have hP : P ≠ 0 := Polynomial.map_ne_zero hc
  have hDtop : D.coeff n ≠ 0 := by
    have htop : p.coeff n = 1 := by simpa [← hp.2.1] using hp.1.coeff_natDegree
    simp [D,htop]
  have hD : ∀ z : ℂ, 0 ≤ z.re → D.eval z ≠ 0 := by
    simpa only [D,← value_eq_mapped_eval] using hp.2.2
  have hweak' : ∀ z : ℂ, 0 ≤ z.re → 0 ≤ (P.eval z/D.eval z).re := by
    simpa only [P,D,← value_eq_mapped_eval] using hweak
  have hgap := weak_positive_real_degree_gap n P D hP
    (by simpa [P] using (show c.natDegree ≤ n by omega))
    (by simp [D,hp.2.1]) hDtop hD hweak'
  have hPdeg : P.natDegree = c.natDegree := by simp [P]
  omega

/-- 若已找到至多 n−1 阶的频率正分子，它不可能再低两阶。 -/
theorem lower_frequency_positive_degree_exact
    {n : ℕ} (hn : 0 < n) {p c : ℝ[X]}
    (hp : HurwitzClass n p) (hc : c.natDegree ≤ n-1)
    (hfreq : FrequencyPositive c p) :
    c.natDegree = n-1 := by
  have hcne : c ≠ 0 := by
    intro hz
    have h := hfreq 0
    simp [hz,value] at h
  exact weak_lower_numerator_degree_exact hn hcne hc hp (fun w => (hfreq w).le)

/-! ## 论文引理 10 低阶分子存在后的任意首一方向升阶 -/

private theorem positive_perturbation
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfpos : ∀ t : ℝ, 0 ≤ t → 0 < f t)
    (hgtop : ∀ᶠ t : ℝ in atTop, 0 < g t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 ≤ t → 0 < f t+δ*g t := by
  obtain ⟨R,hR⟩ := eventually_atTop.1 hgtop
  let T : ℝ := max 1 R
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hRT : R ≤ T := le_max_right _ _
  let K : Set ℝ := Icc 0 T
  have hK : IsCompact K := isCompact_Icc
  have hne : K.Nonempty := ⟨0,⟨le_rfl,hTpos.le⟩⟩
  obtain ⟨t₀,ht₀,hminf⟩ := hK.exists_isMinOn hne hf.continuousOn
  obtain ⟨t₁,ht₁,hming⟩ := hK.exists_isMinOn hne hg.continuousOn
  have hf0 : 0 < f t₀ := hfpos t₀ ht₀.1
  let M : ℝ := max 1 (1-g t₁)
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hMbound : 1-g t₁ ≤ M := le_max_right _ _
  let δ : ℝ := f t₀/(2*M)
  have hδ : 0 < δ := div_pos hf0 (mul_pos (by norm_num) hMpos)
  have hδM : δ*M = f t₀/2 := by
    dsimp [δ]
    field_simp [ne_of_gt hMpos]
    ring
  refine ⟨δ,hδ,fun t ht => ?_⟩
  by_cases htT : t ≤ T
  · have htK : t ∈ K := ⟨ht,htT⟩
    have hft : f t₀ ≤ f t := hminf htK
    have hgt : g t₁ ≤ g t := hming htK
    have hδgt := mul_le_mul_of_nonneg_left hgt hδ.le
    have hδMbound := mul_le_mul_of_nonneg_left hMbound hδ.le
    nlinarith
  · have hgt := hR t (hRT.trans (le_of_lt (lt_of_not_ge htT)))
    exact add_pos (hfpos t ht) (mul_pos hδ hgt)

private theorem positive_perturbation_smaller
    {f g : ℝ → ℝ} {δ δ₀ : ℝ}
    (hf : ∀ t : ℝ, 0 ≤ t → 0 < f t)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 < f t+δ₀*g t)
    (hδ : 0 < δ) (hle : δ ≤ δ₀) :
    ∀ t : ℝ, 0 ≤ t → 0 < f t+δ*g t := by
  intro t ht
  by_cases hg : 0 ≤ g t
  · exact add_pos_of_pos_of_nonneg (hf t ht) (mul_nonneg hδ.le hg)
  · have hm := mul_le_mul_of_nonpos_right hle (le_of_lt (lt_of_not_ge hg))
    linarith [hpos t ht]

theorem monic_direction_cross
    {n : ℕ} {h p : ℝ[X]} (hh : h.Monic) (hp : p.Monic)
    (hdh : h.natDegree = n) (hdp : p.natDegree = n) :
    (frequencyCross h p).Monic ∧ (frequencyCross h p).natDegree = 2*n := by
  have hbound : (frequencyCross h p).natDegree ≤ 2*n := by
    have hdeg := frequencyCross_degree h p
    omega
  have htop : (frequencyCross h p).coeff (2*n) = 1 := by
    rw [frequencyCross_top n h p hdh.le hdp.le
      (by simpa [← hdp] using hp.coeff_natDegree)]
    simpa [← hdh] using hh.coeff_natDegree
  exact ⟨Polynomial.monic_of_natDegree_le_of_coeff_eq_one (2*n) hbound htop,
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hbound (by rw [htop]; norm_num)⟩

theorem frequencyCross_add_scaled_eval (c h p : ℝ[X]) (δ w : ℝ) :
    (frequencyCross (c+C δ*h) p).eval w =
      (frequencyCross c p).eval w+δ*(frequencyCross h p).eval w := by
  simp only [frequencyCross_eval]
  simp [value,pairing,Complex.mul_re,Complex.mul_im]
  ring

private theorem common_perturbation_size
    (fA fB gA gB : ℝ[X])
    (hfA : ∀ t : ℝ, 0 ≤ t → 0 < fA.eval t)
    (hfB : ∀ t : ℝ, 0 ≤ t → 0 < fB.eval t)
    (hgA : 0 < gA.natDegree) (hgB : 0 < gB.natDegree)
    (hmonoA : gA.Monic) (hmonoB : gB.Monic) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      (∀ t : ℝ, 0 ≤ t → 0 < fA.eval t+δ*gA.eval t) ∧
      (∀ t : ℝ, 0 ≤ t → 0 < fB.eval t+δ*gB.eval t) := by
  have htopA := gA.tendsto_atTop_of_leadingCoeff_nonneg
    (Polynomial.natDegree_pos_iff_degree_pos.mp hgA) (by rw [hmonoA.leadingCoeff]; norm_num)
  have htopB := gB.tendsto_atTop_of_leadingCoeff_nonneg
    (Polynomial.natDegree_pos_iff_degree_pos.mp hgB) (by rw [hmonoB.leadingCoeff]; norm_num)
  obtain ⟨δA,hδA,hA⟩ := positive_perturbation _ _ fA.continuous gA.continuous
    hfA (htopA.eventually (eventually_gt_atTop 0))
  obtain ⟨δB,hδB,hB⟩ := positive_perturbation _ _ fB.continuous gB.continuous
    hfB (htopB.eventually (eventually_gt_atTop 0))
  refine ⟨min δA δB,lt_min hδA hδB,fun δ hδ hle => ⟨?_,?_⟩⟩
  · exact positive_perturbation_smaller hfA hA hδ (hle.trans (min_le_left _ _))
  · exact positive_perturbation_smaller hfB hB hδ (hle.trans (min_le_right _ _))

/-- 同一个 δ₀ 同时控制两个端点；任意更小的正 δ 均可，并推广到所有线段参数。 -/
theorem lower_to_same_degree_perturbation
    {n : ℕ} (hn : 0 < n) (a b c h : ℝ[X])
    (ha : a.Monic) (hb : b.Monic) (hh : h.Monic)
    (hda : a.natDegree = n) (hdb : b.natDegree = n) (hdh : h.natDegree = n)
    (hc : LowerCommonNumerator n a b c)
    (hsegment : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t)) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      (c+C δ*h).natDegree = n ∧ (c+C δ*h).coeff n = δ ∧
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → SPR.TeacherCore.SPR (c+C δ*h) (blend a b t) := by
  have hA : Stable a := by simpa [blend] using hsegment 0 (by constructor <;> norm_num)
  have hB : Stable b := by simpa [blend] using hsegment 1 (by constructor <;> norm_num)
  have hfA (w : ℝ) (_ : 0 ≤ w) : 0 < (frequencyCross c a).eval w := by
    rw [frequencyCross_eval]
    exact (positive_quotient_iff _ _ (stable_axis_ne_zero hA w)).mp (hc.2.2.1 w)
  have hfB (w : ℝ) (_ : 0 ≤ w) : 0 < (frequencyCross c b).eval w := by
    rw [frequencyCross_eval]
    exact (positive_quotient_iff _ _ (stable_axis_ne_zero hB w)).mp (hc.2.2.2 w)
  have hgA := monic_direction_cross hh ha hdh hda
  have hgB := monic_direction_cross hh hb hdh hdb
  obtain ⟨δ₀,hδ₀,hpos⟩ := common_perturbation_size _ _ _ _ hfA hfB
    (by rw [hgA.2]; omega) (by rw [hgB.2]; omega) hgA.1 hgB.1
  refine ⟨δ₀,hδ₀,fun δ hδ hδle => ?_⟩
  obtain ⟨hposA,hposB⟩ := hpos δ hδ hδle
  have hdeg : (c+C δ*h).natDegree = n := by
    rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt,Polynomial.natDegree_C_mul (ne_of_gt hδ),hdh]
    rw [Polynomial.natDegree_C_mul (ne_of_gt hδ),hdh,hc.2.1]
    omega
  have hcoeff : (c+C δ*h).coeff n = δ := by
    simp only [Polynomial.coeff_add,Polynomial.coeff_C_mul,
      lower_top_coefficient_zero hn hc.2.1.le]
    have htop : h.coeff n = 1 := by simpa [← hdh] using hh.coeff_natDegree
    rw [htop]
    ring
  have hfreq {p : ℝ[X]} (hs : Stable p)
      (hpositive : ∀ w : ℝ, 0 ≤ w →
        0 < (frequencyCross c p).eval w+δ*(frequencyCross h p).eval w) :
      FrequencyPositive (c+C δ*h) p := by
    intro w
    apply (positive_quotient_iff _ _ (stable_axis_ne_zero hs w)).mpr
    rw [← frequencyCross_eval,frequencyCross_add_scaled_eval]
    have hv := hpositive |w| (abs_nonneg w)
    by_cases hw : 0 ≤ w
    · simpa [abs_of_nonneg hw] using hv
    · simpa [abs_of_neg (lt_of_not_ge hw),frequencyCross_neg_eval] using hv
  refine ⟨hdeg,hcoeff,fun t ht => ⟨hsegment t ht,?_⟩⟩
  exact frequency_positive_on_segment (hfreq hA hposA) (hfreq hB hposB) t ht

/-- 升阶后除以同一个正的最高次系数，得到精确 n 阶的首一公共分子。 -/
theorem raise_then_normalize
    {n : ℕ} (hn : 0 < n) (a b c h : ℝ[X])
    (ha : a.Monic) (hb : b.Monic) (hh : h.Monic)
    (hda : a.natDegree = n) (hdb : b.natDegree = n) (hdh : h.natDegree = n)
    (hc : LowerCommonNumerator n a b c)
    (hsegment : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ β : ℝ[X],
      β = C δ⁻¹*(c+C δ*h) ∧ β.Monic ∧ β.natDegree = n ∧
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → SPR.TeacherCore.SPR β (blend a b t) := by
  obtain ⟨δ,hδ,hall⟩ := lower_to_same_degree_perturbation hn a b c h ha hb hh hda hdb hdh hc hsegment
  obtain ⟨hdeg,hcoeff,hwhole⟩ := hall δ hδ le_rfl
  have hlead : (c+C δ*h).leadingCoeff = δ := by
    rw [Polynomial.leadingCoeff,hdeg,hcoeff]
  refine ⟨δ,hδ,C δ⁻¹*(c+C δ*h),rfl,?_,?_,?_⟩
  · apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [hlead,inv_mul_cancel₀ (ne_of_gt hδ)]
  · rw [Polynomial.natDegree_C_mul (inv_ne_zero (ne_of_gt hδ)),hdeg]
  · intro t ht
    exact ⟨(hwhole t ht).1,frequencyPositive_scale (hwhole t ht).2 δ⁻¹ (inv_pos.mpr hδ)⟩

/-! ## 任意阶单个分母的显式低阶分子

临界参数论证需要一个已知可行的起点 a=b。
任意阶的这个起点可直接取 c=a'/n，利用每个稳定根产生的正实部。
-/

private theorem root_product_log_derivative (R : Multiset ℂ) (z : ℂ)
    (hz : ∀ r ∈ R, z-r ≠ 0) :
    (linearRootProduct R).derivative.eval z/(linearRootProduct R).eval z =
      (R.map (fun r => (z-r)⁻¹)).sum := by
  induction R using Multiset.induction_on with
  | empty => simp [linearRootProduct]
  | cons r R ih =>
    have hzr := hz r (by simp)
    have htail : ∀ u ∈ R, z-u ≠ 0 := fun u hu => hz u (by simp [hu])
    have hR : (linearRootProduct R).eval z ≠ 0 := by
      intro hzero
      have hmem := (linearRootProduct_root_iff R z).mp hzero
      exact htail z hmem (sub_self z)
    have heq : linearRootProduct (r ::ₘ R) = (X-C r)*linearRootProduct R := by
      simp [linearRootProduct]
    rw [heq,Polynomial.derivative_mul]
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.derivative_sub,
      Polynomial.derivative_X,Polynomial.derivative_C,sub_zero,Polynomial.eval_one,
      Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,one_mul,
      Multiset.map_cons,Multiset.sum_cons,← ih htail]
    field_simp
    ring

private theorem complex_sum_real_pos
    (s : Multiset ℂ) (hs : ∀ z ∈ s, 0 < z.re) (hne : s ≠ 0) :
    0 < s.sum.re := by
  induction s using Multiset.induction_on with
  | empty => exact (hne rfl).elim
  | @cons z s ih =>
    have hz : 0 < z.re := hs z (by simp)
    by_cases hsz : s = 0
    · simpa [hsz] using hz
    · have ht := ih (fun w hw => hs w (by simp [hw])) hsz
      simpa only [Multiset.sum_cons,Complex.add_re] using add_pos hz ht

/-- 稳定多项式的对数导数在整个闭右半平面有严格正实部。 -/
theorem stable_log_derivative_positive
    {n : ℕ} (hn : 0 < n) {p : ℝ[X]} (hp : HurwitzClass n p)
    (z : ℂ) (hz : 0 ≤ z.re) :
    0 < (value p.derivative z/value p z).re := by
  let P := p.map (algebraMap ℝ ℂ)
  have hP : P.Monic := hp.1.map _
  have hsplit : P.Splits (RingHom.id ℂ) := IsAlgClosed.splits_codomain _
  have hndeg : P.natDegree = n := by simp [P,hp.2.1]
  have hroots : P.roots ≠ 0 := by
    intro hzero
    have hcard := Polynomial.splits_iff_card_roots.mp hsplit
    rw [hzero,Multiset.card_zero,hndeg] at hcard
    omega
  have hleft (r : ℂ) (hr : r ∈ P.roots) : r.re < 0 := by
    have hroot : P.eval r = 0 := (Polynomial.mem_roots hP.ne_zero).mp hr
    by_contra hnot
    apply hp.2.2 r (le_of_not_gt hnot)
    simpa only [P,← value_eq_mapped_eval] using hroot
  have hzr (r : ℂ) (hr : r ∈ P.roots) : 0 < (z-r).re := by
    simp only [Complex.sub_re]
    linarith [hleft r hr]
  have hzrNe (r : ℂ) (hr : r ∈ P.roots) : z-r ≠ 0 := by
    intro hzero
    have h := hzr r hr
    simp [hzero] at h
  have hlog := root_product_log_derivative P.roots z hzrNe
  have hfactor : P = linearRootProduct P.roots :=
    Polynomial.eq_prod_roots_of_monic_of_splits_id hP hsplit
  rw [← hfactor] at hlog
  have hsum : 0 < (P.roots.map (fun r => (z-r)⁻¹)).sum.re := by
    apply complex_sum_real_pos
    · intro u hu
      obtain ⟨r,hr,rfl⟩ := Multiset.mem_map.mp hu
      rw [Complex.inv_re]
      exact div_pos (hzr r hr)
        (Complex.normSq_pos.mpr (hzrNe r hr))
    · simpa using hroots
  rw [← hlog] at hsum
  simpa only [P,Polynomial.derivative_map,← value_eq_mapped_eval] using hsum

/-- 任意 n>0 的单个首一稳定分母，显式取首一分子 p'/n，次数恰为 n−1。 -/
theorem normalized_derivative_lower_numerator
    {n : ℕ} (hn : 0 < n) {p : ℝ[X]} (hp : HurwitzClass n p) :
    LowerCommonNumerator n p p (C (n : ℝ)⁻¹*p.derivative) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdeg : (C (n : ℝ)⁻¹*p.derivative).natDegree ≤ n-1 := by
    rw [Polynomial.natDegree_C_mul (inv_ne_zero (ne_of_gt hnR))]
    simpa [hp.2.1] using Polynomial.natDegree_derivative_le p
  have hcoeff : (C (n : ℝ)⁻¹*p.derivative).coeff (n-1) = 1 := by
    have htop : p.coeff n = 1 := by simpa [← hp.2.1] using hp.1.coeff_natDegree
    rw [Polynomial.coeff_C_mul,Polynomial.coeff_derivative,
      show n-1+1 = n by omega,htop,one_mul,
      show ((n-1 : ℕ) : ℝ)+1 = (n : ℝ) by exact_mod_cast (show n-1+1 = n by omega),
      inv_mul_cancel₀ (ne_of_gt hnR)]
  have hfreq : FrequencyPositive (C (n : ℝ)⁻¹*p.derivative) p := by
    intro w
    have hpos := stable_log_derivative_positive hn hp (w*Complex.I) (by simp)
    have hscale : value (C (n : ℝ)⁻¹*p.derivative) (w*Complex.I)/value p (w*Complex.I) =
        ((n : ℝ)⁻¹ : ℂ)*(value p.derivative (w*Complex.I)/value p (w*Complex.I)) := by
      simp [value,mul_div_assoc]
    rw [hscale]
    simpa using mul_pos (inv_pos.mpr hnR) hpos
  exact ⟨Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hdeg hcoeff,
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [hcoeff]; norm_num),hfreq,hfreq⟩

/-! ## 任意阶充分性的接触计数核心

低一阶分子的交叉实部是偶多项式，次数至多 2n−2。
这比粗略的乘积次数界 2n−1 少一阶，正好补偿少掉的一个矩条件。
下面先把这一点及有限频率证书的矛盾独立证明。
-/

/-- 交叉实部关于频率是偶多项式，因此其非零项的最高次数为偶数。 -/
theorem frequencyCross_natDegree_even (c p : ℝ[X]) :
    Even (frequencyCross c p).natDegree := by
  by_cases hz : frequencyCross c p = 0
  · simp [hz]
  have heq : (frequencyCross c p).comp (-X) = frequencyCross c p := by
    apply Polynomial.funext
    intro w
    simpa using frequencyCross_neg_eval c p w
  have hl := congrArg Polynomial.leadingCoeff heq
  rw [Polynomial.comp_neg_X_leadingCoeff_eq] at hl
  have hpow : (-1 : ℝ)^(frequencyCross c p).natDegree = 1 := by
    apply mul_right_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hz)
    simpa using hl
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hpow

/-- 分母 n 阶、分子至多 n−1 阶时，偶性把交叉实部的次数界降至 2n−2。 -/
theorem lower_frequencyCross_degree
    {n : ℕ} (hn : 0 < n) (c p : ℝ[X])
    (hc : c.natDegree ≤ n-1) (hp : p.natDegree ≤ n) :
    (frequencyCross c p).natDegree ≤ 2*(n-1) := by
  have hd := frequencyCross_degree c p
  obtain ⟨k,hk⟩ := frequencyCross_natDegree_even c p
  omega

/-! ### 适用于低一阶分子的频率紧化

把交叉实部按 2(n−1) 次齐次化，而不是原同阶证明的 2n 次。
有限频率的正负号不变，无穷远则检测交叉多项式的 2n−2 次系数。
-/

def realHomogeneousValue (d : ℕ) (q : ℝ[X]) (x y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (d+1), q.coeff k*x^k*y^(d-k)

theorem realHomogeneousValue_at_infinity (d : ℕ) (q : ℝ[X]) (x : ℝ) :
    realHomogeneousValue d q x 0 = q.coeff d*x^d := by
  classical
  unfold realHomogeneousValue
  rw [Finset.sum_eq_single d]
  · simp
  · intro k hk hkd
    have hpos : 0 < d-k := by have := Finset.mem_range.mp hk; omega
    simp [zero_pow (Nat.ne_of_gt hpos)]
  · simp

theorem realHomogeneousValue_finite (d : ℕ) (q : ℝ[X])
    (hq : q.natDegree ≤ d) (x y : ℝ) (hy : y ≠ 0) :
    realHomogeneousValue d q x y = y^d*q.eval (x/y) := by
  rw [Polynomial.eval_eq_sum_range' (by omega : q.natDegree < d+1)]
  unfold realHomogeneousValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkd : k ≤ d := by have := Finset.mem_range.mp hk; omega
  have hpow : y^d*(x/y)^k = x^k*y^(d-k) := by
    rw [div_pow,show d = k+(d-k) by omega,pow_add]
    field_simp [hy]
    ring
  calc
    _ = q.coeff k*(x^k*y^(d-k)) := by ring
    _ = q.coeff k*(y^d*(x/y)^k) := by rw [hpow]
    _ = _ := by ring

def lowerCompactPairing (n : ℕ) (c p : ℝ[X]) (u : ℝ) : ℝ :=
  realHomogeneousValue (2*(n-1)) (frequencyCross c p) u (1-|u|)

theorem lowerCompactPairing_continuous (n : ℕ) (c p : ℝ[X]) :
    Continuous (lowerCompactPairing n c p) := by
  unfold lowerCompactPairing realHomogeneousValue
  fun_prop

theorem lowerCompactPairing_at_infinity (n : ℕ) (c p : ℝ[X]) :
    lowerCompactPairing n c p 1 = (frequencyCross c p).coeff (2*(n-1)) := by
  simp [lowerCompactPairing,realHomogeneousValue_at_infinity]

theorem lowerCompactPairing_finite
    {n : ℕ} (hn : 0 < n) (c p : ℝ[X])
    (hc : c.natDegree ≤ n-1) (hp : p.natDegree ≤ n)
    (u : ℝ) (hu : 1-|u| ≠ 0) :
    lowerCompactPairing n c p u =
      (1-|u|)^(2*(n-1))*
        pairing (value c (((u/(1-|u|) : ℝ) : ℂ)*Complex.I))
          (value p (((u/(1-|u|) : ℝ) : ℂ)*Complex.I)) := by
  rw [lowerCompactPairing,realHomogeneousValue_finite _ _
    (lower_frequencyCross_degree hn c p hc hp) _ _ hu,frequencyCross_eval]

/-- 新紧化的严格正性等价于全部有限频率正性和无穷远首项正性。 -/
theorem lower_compact_positivity_iff
    {n : ℕ} (hn : 0 < n) (c p : ℝ[X])
    (hc : c.natDegree ≤ n-1) (hp : HurwitzClass n p) :
    (∀ u ∈ Icc (-1 : ℝ) 1, 0 < lowerCompactPairing n c p u) ↔
      0 < (frequencyCross c p).coeff (2*(n-1)) ∧ FrequencyPositive c p := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · simpa only [lowerCompactPairing_at_infinity] using
        h 1 (by constructor <;> norm_num)
    · intro w
      let R : ℝ := 1+|w|
      have hR : 0 < R := by dsimp [R]; positivity
      let u : ℝ := w/R
      have habs : |u| = |w|/R := by simp [u,abs_div,abs_of_pos hR]
      have hu : |u| < 1 := by rw [habs]; exact (div_lt_one hR).mpr (by dsimp [R]; linarith)
      have hy : 1-|u| = 1/R := by rw [habs]; dsimp [R]; field_simp
      have hypos : 0 < 1-|u| := sub_pos.mpr hu
      have harg : u/(1-|u|) = w := by rw [hy]; dsimp [u]; field_simp
      have hpair := h u ⟨(abs_lt.mp hu).1.le,(abs_lt.mp hu).2.le⟩
      rw [lowerCompactPairing_finite hn c p hc hp.2.1.le _ (ne_of_gt hypos),harg] at hpair
      apply (positive_quotient_iff _ _ (stable_axis_ne_zero hp.2.2 w)).mpr
      exact (mul_pos_iff_of_pos_left (pow_pos hypos _)).mp hpair
  · rintro ⟨hlead,hfreq⟩ u hu
    have hy : 0 ≤ 1-|u| := sub_nonneg.mpr (abs_le.mpr hu)
    by_cases hzero : 1-|u| = 0
    · have habs : |u| = 1 := by linarith
      have hsq : u^2 = 1 := by
        have heq := congrArg (fun x : ℝ => x^2) habs
        simpa using heq
      rw [lowerCompactPairing,hzero,realHomogeneousValue_at_infinity]
      simpa [pow_mul,hsq] using hlead
    · have hypos : 0 < 1-|u| := lt_of_le_of_ne hy (Ne.symm hzero)
      rw [lowerCompactPairing_finite hn c p hc hp.2.1.le _ hzero]
      exact mul_pos (pow_pos hypos _)
        ((positive_quotient_iff _ _ (stable_axis_ne_zero hp.2.2 _)).mp (hfreq _))

/-- 交叉多项式对分子相加保持线性。 -/
theorem frequencyCross_add (c d p : ℝ[X]) :
    frequencyCross (c+d) p = frequencyCross c p+frequencyCross d p := by
  apply Polynomial.funext
  intro w
  simp [frequencyCross_eval,value,pairing,add_mul]

theorem frequencyCross_scale (c p : ℝ[X]) (r : ℝ) :
    frequencyCross (C r*c) p = C r*frequencyCross c p := by
  apply Polynomial.funext
  intro w
  simp [frequencyCross_eval,value,pairing,Complex.mul_re,Complex.mul_im]
  ring

theorem frequencyCross_denominator_blend (c a b : ℝ[X]) (t : ℝ) :
    frequencyCross c (blend a b t) =
      C (1-t)*frequencyCross c a+C t*frequencyCross c b := by
  apply Polynomial.funext
  intro w
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    frequencyCross_eval,value_blend]
  exact pairing_blend _ _ _ t

theorem realHomogeneousValue_add (d : ℕ) (p q : ℝ[X]) (x y : ℝ) :
    realHomogeneousValue d (p+q) x y =
      realHomogeneousValue d p x y+realHomogeneousValue d q x y := by
  simp [realHomogeneousValue,Polynomial.coeff_add,add_mul,Finset.sum_add_distrib]

theorem realHomogeneousValue_scale (d : ℕ) (p : ℝ[X]) (r x y : ℝ) :
    realHomogeneousValue d (C r*p) x y = r*realHomogeneousValue d p x y := by
  simp only [realHomogeneousValue,Polynomial.coeff_C_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem lowerCompactPairing_add (n : ℕ) (c d p : ℝ[X]) (u : ℝ) :
    lowerCompactPairing n (c+d) p u =
      lowerCompactPairing n c p u+lowerCompactPairing n d p u := by
  simp only [lowerCompactPairing,frequencyCross_add,realHomogeneousValue_add]

theorem lowerCompactPairing_scale (n : ℕ) (c p : ℝ[X]) (r u : ℝ) :
    lowerCompactPairing n (C r*c) p u = r*lowerCompactPairing n c p u := by
  simp only [lowerCompactPairing,frequencyCross_scale,realHomogeneousValue_scale]

theorem lowerCompactPairing_denominator_blend (n : ℕ) (c a b : ℝ[X]) (t u : ℝ) :
    lowerCompactPairing n c (blend a b t) u =
      (1-t)*lowerCompactPairing n c a u+t*lowerCompactPairing n c b u := by
  simp only [lowerCompactPairing,frequencyCross_denominator_blend,
    realHomogeneousValue_add,realHomogeneousValue_scale]

theorem lowerCompactPairing_sum {ι : Type*} (n : ℕ) (s : Finset ι)
    (c : ι → ℝ[X]) (p : ℝ[X]) (u : ℝ) :
    lowerCompactPairing n (∑ i ∈ s, c i) p u = ∑ i ∈ s, lowerCompactPairing n (c i) p u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lowerCompactPairing,realHomogeneousValue,frequencyCross,frequencyProduct,realPolynomial]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,lowerCompactPairing_add,ih]

def lowerFeature (n : ℕ) (p : ℝ[X]) (u : ℝ) : CoefficientSpace (n-1) :=
  fun k => lowerCompactPairing n (X^k.val) p u

theorem lowerFeature_continuous (n : ℕ) (p : ℝ[X]) : Continuous (lowerFeature n p) := by
  apply continuous_pi
  intro k
  exact lowerCompactPairing_continuous n (X^k.val) p

theorem lower_pairing_feature_identity (n : ℕ) (v : CoefficientSpace (n-1)) (p : ℝ[X]) (u : ℝ) :
    lowerCompactPairing n (polynomialFrom (n-1) v) p u =
      dotFunctional (n-1) v (lowerFeature n p u) := by
  unfold polynomialFrom
  rw [lowerCompactPairing_sum,dotFunctional_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Polynomial.C_mul_X_pow_eq_monomial,lowerCompactPairing_scale]
  rfl

def lowerFeatureSet (n : ℕ) (a b : ℝ[X]) : Set (CoefficientSpace (n-1)) :=
  (lowerFeature n a '' Icc (-1 : ℝ) 1) ∪ (lowerFeature n b '' Icc (-1 : ℝ) 1)

theorem lowerFeatureSet_compact (n : ℕ) (a b : ℝ[X]) : IsCompact (lowerFeatureSet n a b) :=
  (isCompact_Icc.image (lowerFeature_continuous n a)).union
    (isCompact_Icc.image (lowerFeature_continuous n b))

theorem lowerFeatureSet_nonempty (n : ℕ) (a b : ℝ[X]) : (lowerFeatureSet n a b).Nonempty := by
  exact ⟨lowerFeature n a 0,Or.inl ⟨0,by constructor <;> norm_num,rfl⟩⟩

/-- 强的低阶综合问题：无穷远的归一化频率约束也严格为正。 -/
def LowerCompactFeasible (n : ℕ) (a b : ℝ[X]) : Prop :=
  ∃ c : ℝ[X], c.natDegree ≤ n-1 ∧
    (∀ u ∈ Icc (-1 : ℝ) 1, 0 < lowerCompactPairing n c a u) ∧
    (∀ u ∈ Icc (-1 : ℝ) 1, 0 < lowerCompactPairing n c b u)

/-- 低阶综合的凸几何改写，系数空间维数为 n。 -/
theorem lower_synthesis_iff_origin_excluded (n : ℕ) (a b : ℝ[X]) :
    LowerCompactFeasible n a b ↔
      0 ∉ closedConvexHull ℝ (lowerFeatureSet n a b) := by
  rw [← strict_separation_iff _ (lowerFeatureSet_compact n a b) (lowerFeatureSet_nonempty n a b)]
  constructor
  · rintro ⟨c,hdeg,hA,hB⟩
    let v : CoefficientSpace (n-1) := fun k => c.coeff k.val
    have hc : polynomialFrom (n-1) v = c := polynomialFrom_coefficients (n-1) c hdeg
    refine ⟨dotFunctional (n-1) v,?_⟩
    rintro x (⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩)
    · simpa only [← lower_pairing_feature_identity,hc] using hA u hu
    · simpa only [← lower_pairing_feature_identity,hc] using hB u hu
  · rintro ⟨f,hf⟩
    let v : CoefficientSpace (n-1) := fun k => f (Pi.single k 1)
    refine ⟨polynomialFrom (n-1) v,polynomialFrom_degree (n-1) v,?_,?_⟩
    · intro u hu
      rw [lower_pairing_feature_identity,dotFunctional_apply]
      exact (functional_coordinates (n-1) f _).symm ▸ hf _ (Or.inl ⟨u,hu,rfl⟩)
    · intro u hu
      rw [lower_pairing_feature_identity,dotFunctional_apply]
      exact (functional_coordinates (n-1) f _).symm ▸ hf _ (Or.inr ⟨u,hu,rfl⟩)

/-- 无穷远约束只涉及分子的最高两个系数。 -/
theorem lower_frequencyCross_top
    {n : ℕ} (hn : 2 ≤ n) (c p : ℝ[X])
    (hc : c.natDegree ≤ n-1) (hp : p.natDegree ≤ n) :
    (frequencyCross c p).coeff (2*(n-1)) =
      c.coeff (n-1)*p.coeff (n-1)-c.coeff (n-2)*p.coeff n := by
  let A := (c.map (algebraMap ℝ ℂ)).comp (C Complex.I*X)
  let B := (p.map (algebraMap ℝ ℂ)).comp (C (-Complex.I)*X)
  have hA (k : ℕ) : A.coeff k = (c.coeff k : ℂ)*Complex.I^k := by
    simp only [A,Polynomial.comp_C_mul_X_coeff,Polynomial.coeff_map,Complex.coe_algebraMap]
  have hB (k : ℕ) : B.coeff k = (p.coeff k : ℂ)*(-Complex.I)^k := by
    simp only [B,Polynomial.comp_C_mul_X_coeff,Polynomial.coeff_map,Complex.coe_algebraMap]
  have hsum : (A*B).coeff (2*(n-1)) =
      A.coeff (n-1)*B.coeff (n-1)+A.coeff (n-2)*B.coeff n := by
    rw [Polynomial.coeff_mul]
    apply Finset.sum_eq_add (n-1,n-1) (n-2,n)
    · intro heq
      have h := congrArg Prod.fst heq
      dsimp at h
      omega
    · rintro ⟨i,j⟩ hij hne
      have htotal := Finset.mem_antidiagonal.mp hij
      dsimp at htotal hne ⊢
      by_cases hi : n-1 < i
      · rw [hA,Polynomial.coeff_eq_zero_of_natDegree_lt (p := c) (by omega)]
        simp
      · by_cases hj : n < j
        · rw [hB,Polynomial.coeff_eq_zero_of_natDegree_lt (p := p) (by omega)]
          simp
        · have hfirst : i ≠ n-1 := by
            intro heq
            apply hne.1
            exact Prod.ext heq (by omega)
          apply (hne.2 ?_).elim
          exact Prod.ext (by omega) (by omega)
    · intro hnot
      exact (hnot (Finset.mem_antidiagonal.mpr (by omega))).elim
    · intro hnot
      exact (hnot (Finset.mem_antidiagonal.mpr (by omega))).elim
  have hi : Complex.I^(n-1)*(-Complex.I)^(n-1) = 1 := by
    rw [← mul_pow]
    simp
  have hj : Complex.I^(n-2)*(-Complex.I)^n = -1 := by
    calc
      _ = Complex.I^(n-2)*((-Complex.I)^(n-2)*(-Complex.I)^2) := by
        rw [← pow_add,show n-2+2 = n by omega]
      _ = (Complex.I*(-Complex.I))^(n-2)*(-Complex.I)^2 := by rw [mul_pow]; ring
      _ = -1 := by simp
  rw [frequencyCross,realPolynomial_coefficient]
  change ((A*B).coeff (2*(n-1))).re = _
  rw [hsum,hA,hA,hB,hB]
  have hrearrange :
      ((c.coeff (n-1) : ℂ)*Complex.I^(n-1))*((p.coeff (n-1) : ℂ)*(-Complex.I)^(n-1))+
        ((c.coeff (n-2) : ℂ)*Complex.I^(n-2))*((p.coeff n : ℂ)*(-Complex.I)^n) =
      (c.coeff (n-1) : ℂ)*(p.coeff (n-1) : ℂ)*
          (Complex.I^(n-1)*(-Complex.I)^(n-1))+
        (c.coeff (n-2) : ℂ)*(p.coeff n : ℂ)*(Complex.I^(n-2)*(-Complex.I)^n) := by ring
  rw [hrearrange,hi,hj]
  simp [sub_eq_add_neg]

/-- 新紧化也保留了任意阶的显式可行起点。 -/
theorem lower_compact_self_feasible
    {n : ℕ} (hn : 0 < n) {p : ℝ[X]} (hp : HurwitzClass n p) :
    LowerCompactFeasible n p p := by
  let c := C (n : ℝ)⁻¹*p.derivative
  have hc := normalized_derivative_lower_numerator hn hp
  change LowerCommonNumerator n p p c at hc
  have htop : 0 < (frequencyCross c p).coeff (2*(n-1)) := by
    by_cases hn1 : n = 1
    · subst n
      have hpform := hp.1.eq_X_add_C hp.2.1
      have hconst := stable_monic_constant_pos hp.1 hp.2.2 (by rw [hp.2.1]; norm_num)
      have hcform : c = 1 := by dsimp only [c]; rw [hpform]; simp
      rw [hcform]
      change 0 < (frequencyCross (1 : ℝ[X]) p).coeff 0
      rw [Polynomial.coeff_zero_eq_eval_zero,frequencyCross_eval]
      simp only [Complex.ofReal_zero,zero_mul]
      have hpzero : value p 0 = (p.coeff 0 : ℂ) := by
        rw [value_eq_mapped_eval,← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_map]
        rfl
      rw [show value (1 : ℝ[X]) 0 = 1 by simp [value],hpzero]
      simpa [pairing] using hconst
    · have hn2 : 2 ≤ n := by omega
      rw [lower_frequencyCross_top hn2 c p hc.2.1.le hp.2.1.le]
      have hc1 : c.coeff (n-1) = 1 := by rw [← hc.2.1]; exact hc.1.coeff_natDegree
      have hp1 : p.coeff n = 1 := by simpa [← hp.2.1] using hp.1.coeff_natDegree
      have hc2 : c.coeff (n-2) = (n : ℝ)⁻¹*(p.coeff (n-1)*((n-1 : ℕ) : ℝ)) := by
        simp only [c,Polynomial.coeff_C_mul,Polynomial.coeff_derivative]
        rw [show n-2+1 = n-1 by omega]
        congr 2
        exact_mod_cast (show n-2+1 = n-1 by omega)
      rw [hc1,hp1,hc2,one_mul,mul_one]
      have hpos := stable_monic_next_coefficient_pos hn hp.1 hp.2.1 hp.2.2
      have hcast : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
      have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      rw [hcast]
      have heq : p.coeff (n-1)-(n : ℝ)⁻¹*(p.coeff (n-1)*((n : ℝ)-1)) =
          p.coeff (n-1)/(n : ℝ) := by field_simp; ring
      rw [heq]
      exact div_pos hpos hnR
  have hcompact := (lower_compact_positivity_iff hn c p hc.2.1.le hp).mpr ⟨htop,hc.2.2.1⟩
  exact ⟨c,hc.2.1.le,hcompact,hcompact⟩

/-- 新紧化的非负支撑蕴含所有有限频率上的弱正实性。 -/
theorem lower_boundary_nonnegative_of_compact
    {n : ℕ} (hn : 0 < n) (c p : ℝ[X])
    (hc : c.natDegree ≤ n-1) (hp : p.natDegree ≤ n)
    (hcompact : ∀ u ∈ Icc (-1 : ℝ) 1, 0 ≤ lowerCompactPairing n c p u) :
    ∀ w : ℝ, 0 ≤ (value c (w*Complex.I)/value p (w*Complex.I)).re := by
  intro w
  obtain ⟨u,hu,hy,harg⟩ := finite_frequency_coordinates w
  have h := hcompact u hu
  rw [lowerCompactPairing_finite hn c p hc hp _ (ne_of_gt hy),harg] at h
  have hpair : 0 ≤ pairing (value c (w*Complex.I)) (value p (w*Complex.I)) :=
    (mul_nonneg_iff_of_pos_left (pow_pos hy _)).mp h
  rw [real_quotient]
  exact div_nonneg hpair (Complex.normSq_nonneg _)

/-- 任意阶的有限接触数据；这里没有预设任何尚待证明的存在性。 -/
structure LowerContactData (M : ℕ) (a b c : ℝ[X]) where
  nodes : Finset ℝ
  nodes_nonempty : nodes.Nonempty
  nodes_neg : ∀ w ∈ nodes, -w ∈ nodes
  residue : ℝ → ℂ
  residue_ne_zero : ∀ w ∈ nodes, residue w ≠ 0
  residue_conjugate : ∀ w ∈ nodes, residue (-w) = conj (residue w)
  contact : ∀ w ∈ nodes, (value c (imaginaryNode w)*residue w).re = 0
  moments : ∀ k < M, (∑ w : nodes, residue w.val*(imaginaryNode w.val)^k) = 0
  cross_root : ∀ w ∈ nodes,
    (frequencyCross c a).eval w = 0 ∨ (frequencyCross c b).eval w = 0

/-- 没有无穷远质量时，低一阶系数给出 n−1 个复零矩。 -/
abbrev LowerFiniteContactData (n : ℕ) (a b c : ℝ[X]) :=
  LowerContactData (n-1) a b c

/-- 当次数恰好多一阶时，反射差的最高项仍因奇偶性相消。
这允许无穷远质量使零矩数从 n−1 减少到 n−2。 -/
theorem contact_reflection_with_one_extra_degree
    (S : Finset ℝ) (P : ℂ[X]) (r : ℝ → ℂ) (M : ℕ)
    (hneg : ∀ w ∈ S, -w ∈ S)
    (hrconj : ∀ w ∈ S, r (-w) = conj (r w))
    (hPconj : ∀ w ∈ S, P.eval (imaginaryNode (-w)) = conj (P.eval (imaginaryNode w)))
    (hcontact : ∀ w ∈ S, (P.eval (imaginaryNode w)*r w).re = 0)
    (hmoment : ∀ k < M, (∑ w : S, r w.val*(imaginaryNode w.val)^k) = 0)
    (hPdegree : P.natDegree ≤ M+1) (hN : nodeResidueNumerator S r ≠ 0) :
    P*nodeResidueNumerator S r =
      C ((-1 : ℂ)^S.card)*reflection (P*nodeResidueNumerator S r) := by
  classical
  let N := nodeResidueNumerator S r
  let ε : ℂ := (-1)^S.card
  let H : ℂ[X] := P*N-C ε*reflection (P*N)
  have hε : ε*ε = 1 := by dsimp [ε]; rw [← mul_pow]; simp
  by_cases hHzero : H = 0
  · exact sub_eq_zero.mp hHzero
  have hdegree : N.natDegree+M < S.card := by
    have h := residueNumerator_degree_gap (nodePolynomial S)
      (fun w : S => imaginaryNode w.val) (fun w : S => r w.val) M hmoment hN
    simpa only [(nodePolynomial_monic_degree S).2] using h
  have hPNdegree : (P*N).natDegree ≤ S.card := by
    have h := Polynomial.natDegree_mul_le (p := P) (q := N)
    omega
  have hHle : H.natDegree ≤ S.card := by
    have hright : (C ε*reflection (P*N)).natDegree ≤ (P*N).natDegree := by
      simpa only [Polynomial.natDegree_C,zero_add,reflection_degree] using
        (Polynomial.natDegree_mul_le (p := C ε) (q := reflection (P*N)))
    exact (Polynomial.natDegree_sub_le (P*N) (C ε*reflection (P*N))).trans
      ((max_le le_rfl hright).trans hPNdegree)
  have htop : H.coeff S.card = 0 := by
    have href : (reflection (P*N)).coeff S.card = (P*N).coeff S.card*ε := by
      simp only [SPR.TeacherCore.reflection,show (-X : ℂ[X]) = C (-1)*X by simp,
        Polynomial.comp_C_mul_X_coeff,ε]
    simp only [H,Polynomial.coeff_sub,Polynomial.coeff_C_mul,href]
    calc
      _ = (P*N).coeff S.card-(ε*ε)*(P*N).coeff S.card := by ring
      _ = 0 := by rw [hε]; ring
  have hHdegree : H.natDegree < S.card := by
    apply lt_of_le_of_ne hHle
    intro heq
    rw [← heq,Polynomial.coeff_natDegree] at htop
    exact Polynomial.leadingCoeff_ne_zero.mpr hHzero htop
  have hHz (w : ℝ) (hw : w ∈ S) : H.eval (imaginaryNode w) = 0 := by
    have hDneg : (nodePolynomial S).derivative.eval (imaginaryNode (-w)) =
        -ε*(nodePolynomial S).derivative.eval (imaginaryNode w) := by
      rw [imaginaryNode_neg]
      exact nodePolynomial_derivative_neg S hneg _
    have hsum : P.eval (imaginaryNode w)*r w+
        conj (P.eval (imaginaryNode w))*conj (r w) = 0 := by
      have h := hcontact w hw
      simp only [Complex.mul_re] at h
      apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> linarith
    simp only [H,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,SPR.TeacherCore.reflection,
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
    · exact fun w : S => hHz w.val w.property
    · simpa using hHdegree
  exact sub_eq_zero.mp hH

/-- 留数反射法的通用矛盾：接触预算不能同时容纳零矩强迫的次数差。 -/
theorem no_contact_data_of_budget
    {M : ℕ} {a b c : ℝ[X]} (Data : LowerContactData M a b c)
    (hc : c ≠ 0) (hcdeg : c.natDegree ≤ M+1)
    (hleft : ∀ z : ℂ, value c z = 0 → z.re ≤ 0)
    (hsimple : ∀ z : ℂ, z.re = 0 → value c z = 0 →
      (c.map (algebraMap ℝ ℂ)).rootMultiplicity z = 1)
    (hbudget : Data.nodes.card+(axisFrequencies (c.map (algebraMap ℝ ℂ))).card ≤
      c.natDegree+M) : False := by
  classical
  let P := c.map (algebraMap ℝ ℂ)
  have hP : P ≠ 0 := Polynomial.map_ne_zero hc
  have hleft' : ∀ z : ℂ, P.eval z = 0 → z.re ≤ 0 := by
    simpa only [P,← value_eq_mapped_eval] using hleft
  have hsimple' : ∀ z : ℂ, z.re = 0 → P.eval z = 0 → P.rootMultiplicity z = 1 := by
    simpa only [P,← value_eq_mapped_eval] using hsimple
  obtain ⟨Q,_,hQP,hQleft,hQdegree⟩ := strict_factor_and_axis_degree P hP hleft' hsimple'
  let N := nodeResidueNumerator Data.nodes Data.residue
  have hN : N ≠ 0 :=
    nodeResidueNumerator_ne_zero Data.nodes Data.nodes_nonempty Data.residue Data.residue_ne_zero
  have hPconj : ∀ w ∈ Data.nodes, P.eval (imaginaryNode (-w)) = conj (P.eval (imaginaryNode w)) := by
    intro w _
    simpa only [P,← value_eq_mapped_eval] using value_negative_frequency c w
  have hidentity := contact_reflection_with_one_extra_degree Data.nodes P Data.residue M
    Data.nodes_neg Data.residue_conjugate hPconj
    (by simpa only [P,← value_eq_mapped_eval] using Data.contact)
    Data.moments (by simpa [P] using hcdeg) hN
  have hdegree := scalar_reflection_degree_bound P N Q ((-1)^Data.nodes.card)
    hN (pow_ne_zero _ (by norm_num)) hQP
    (left_factor_coprime_reflection Q P hQleft hleft') hidentity
  have hgap := residueNumerator_degree_gap (nodePolynomial Data.nodes)
    (fun w : Data.nodes => imaginaryNode w.val) (fun w : Data.nodes => Data.residue w.val)
    M Data.moments hN
  have hdegP : P.natDegree = c.natDegree := by simp [P]
  have hdegD := (nodePolynomial_monic_degree Data.nodes).2
  change N.natDegree+M < (nodePolynomial Data.nodes).natDegree at hgap
  change Data.nodes.card+(axisFrequencies P).card ≤ c.natDegree+M at hbudget
  omega

/-- 无穷远接触会令最高偶次项消失，交叉实部因此再降低两阶。 -/
theorem lower_cross_degree_of_infinite_contact
    {n : ℕ} (hn : 2 ≤ n) (c p : ℝ[X])
    (hc : c.natDegree ≤ n-1) (hp : p.natDegree ≤ n)
    (hcontact : (frequencyCross c p).coeff (2*(n-1)) = 0) :
    (frequencyCross c p).natDegree ≤ 2*(n-2) := by
  have hdeg := lower_frequencyCross_degree (by omega) c p hc hp
  by_cases hz : frequencyCross c p = 0
  · simp [hz]
  have hne : (frequencyCross c p).natDegree ≠ 2*(n-1) := by
    intro heq
    rw [← heq,Polynomial.coeff_natDegree] at hcontact
    exact Polynomial.leadingCoeff_ne_zero.mpr hz hcontact
  obtain ⟨k,hk⟩ := frequencyCross_natDegree_even c p
  omega

/-- 一次建立弱正实分子的根位置与虚轴零点一重性，供两类接触证书共用。 -/
theorem weak_lower_root_properties
    {n : ℕ} (hn : 0 < n) {p c : ℝ[X]}
    (hp : HurwitzClass n p) (hc : c ≠ 0) (hcdeg : c.natDegree ≤ n-1)
    (hfreq : ∀ w : ℝ, 0 ≤ (value c (w*Complex.I)/value p (w*Complex.I)).re) :
    (∀ z : ℂ, value c z = 0 → z.re ≤ 0) ∧
    (∀ z : ℂ, z.re = 0 → value c z = 0 →
      (c.map (algebraMap ℝ ℂ)).rootMultiplicity z = 1) := by
  let P := c.map (algebraMap ℝ ℂ)
  let D := p.map (algebraMap ℝ ℂ)
  have hP : P ≠ 0 := Polynomial.map_ne_zero hc
  have hD : ∀ z : ℂ, 0 ≤ z.re → D.eval z ≠ 0 := by
    simpa only [D,← value_eq_mapped_eval] using hp.2.2
  have hweak : ∀ z : ℂ, 0 ≤ z.re → 0 ≤ (P.eval z/D.eval z).re := by
    simpa only [P,D,← value_eq_mapped_eval] using
      right_half_plane_real_nonnegative n c p (by omega) hp
        (by rw [lower_top_coefficient_zero hn hcdeg]) hfreq
  constructor
  · simpa only [P,← value_eq_mapped_eval] using
      weak_positive_real_no_open_right_root P D hP hD hweak
  · simpa only [P,← value_eq_mapped_eval] using
      weak_positive_real_axis_root_simple P D hP hD hweak

theorem weak_frequencyCross_nonnegative {c p : ℝ[X]} (hp : Stable p)
    (hf : ∀ w : ℝ, 0 ≤ (value c (w*Complex.I)/value p (w*Complex.I)).re) :
    ∀ w : ℝ, 0 ≤ (frequencyCross c p).eval w := by
  intro w
  rw [frequencyCross_eval]
  have h := hf w
  rw [real_quotient] at h
  simpa using (le_div_iff₀ (Complex.normSq_pos.mpr (stable_axis_ne_zero hp w))).mp h

/-- 两类证书只需分别给出计数上界；根位置与留数反射的矛盾统一调用。 -/
theorem no_weak_lower_contact_data_of_budget
    {n M : ℕ} (hn : 0 < n) {a b c : ℝ[X]}
    (ha : HurwitzClass n a) (hc : c ≠ 0) (hcdeg : c.natDegree ≤ n-1)
    (hf : ∀ w : ℝ, 0 ≤ (value c (w*Complex.I)/value a (w*Complex.I)).re)
    (Data : LowerContactData M a b c) (hdegree : c.natDegree ≤ M+1)
    (hbudget : Data.nodes.card+(axisFrequencies (c.map (algebraMap ℝ ℂ))).card ≤ c.natDegree+M) :
    False := by
  obtain ⟨hleft,hsimple⟩ := weak_lower_root_properties hn ha hc hcdeg hf
  exact no_contact_data_of_budget Data hc hdegree hleft hsimple hbudget


/-- 每个接触节点占用一个根，每个支撑分子的虚轴零点同时占用两端的根。 -/
theorem lower_contact_card_degree_budget
    {n M : ℕ} {a b c : ℝ[X]} (Data : LowerContactData M a b c)
    (ha : HurwitzClass n a) (hb : HurwitzClass n b)
    (hc : c ≠ 0) (hcdeg : c.natDegree ≤ n)
    (hA : ∀ w : ℝ, 0 ≤ (frequencyCross c a).eval w)
    (hB : ∀ w : ℝ, 0 ≤ (frequencyCross c b).eval w) :
    2*(Data.nodes.card+(axisFrequencies (c.map (algebraMap ℝ ℂ))).card) ≤
      (frequencyCross c a).natDegree+(frequencyCross c b).natDegree := by
  classical
  let P := c.map (algebraMap ℝ ℂ)
  have hP : P ≠ 0 := Polynomial.map_ne_zero hc
  have hAne := frequencyCross_ne_zero n c a hc hcdeg ha
  have hBne := frequencyCross_ne_zero n c b hc hcdeg hb
  have hnodes : Data.nodes ⊆ (frequencyCross c a).roots.toFinset ∪
      (frequencyCross c b).roots.toFinset := by
    intro w hw
    rcases Data.cross_root w hw with hr | hr
    · exact Finset.mem_union.mpr (Or.inl (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hAne).mpr hr)))
    · exact Finset.mem_union.mpr (Or.inr (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hBne).mpr hr)))
  have haxis : axisFrequencies P ⊆ (frequencyCross c a).roots.toFinset ∩
      (frequencyCross c b).roots.toFinset := by
    intro w hw
    have hz : value c (imaginaryNode w) = 0 := by
      simpa only [P,← value_eq_mapped_eval] using (mem_axisFrequencies_iff P hP w).mp hw
    apply Finset.mem_inter.mpr
    constructor
    · apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_roots hAne).mpr
      change (frequencyCross c a).eval w = 0
      rw [frequencyCross_eval]
      simp only [imaginaryNode] at hz
      simp [hz,pairing]
    · apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_roots hBne).mpr
      change (frequencyCross c b).eval w = 0
      rw [frequencyCross_eval]
      simp only [imaginaryNode] at hz
      simp [hz,pairing]
  have hcountA := twice_real_root_card_le_degree _ hAne hA
  have hcountB := twice_real_root_card_le_degree _ hBne hB
  have hcardS := Finset.card_le_card hnodes
  have hcardJ := Finset.card_le_card haxis
  have hsum := Finset.card_union_add_card_inter
    (frequencyCross c a).roots.toFinset (frequencyCross c b).roots.toFinset
  change 2*(Data.nodes.card+(axisFrequencies P).card) ≤ _
  omega

/-- 任意阶弱支撑与 n−1 个零矩组成的有限频率接触证书不可能存在。
这是低一阶充分性证明中“没有无穷远原子”分支的次数矛盾。 -/
theorem no_lower_finite_contact_data
    {n : ℕ} (hn : 0 < n) {a b c : ℝ[X]}
    (ha : HurwitzClass n a) (hb : HurwitzClass n b)
    (hc : c ≠ 0) (hcdeg : c.natDegree ≤ n-1)
    (hfreqA : ∀ w : ℝ, 0 ≤ (value c (w*Complex.I)/value a (w*Complex.I)).re)
    (hfreqB : ∀ w : ℝ, 0 ≤ (value c (w*Complex.I)/value b (w*Complex.I)).re)
    (Data : LowerFiniteContactData n a b c) : False := by
  have hcount := lower_contact_card_degree_budget Data ha hb hc (by omega)
    (weak_frequencyCross_nonnegative ha.2.2 hfreqA)
    (weak_frequencyCross_nonnegative hb.2.2 hfreqB)
  have hdegA := lower_frequencyCross_degree hn c a hcdeg ha.2.1.le
  have hdegB := lower_frequencyCross_degree hn c b hcdeg hb.2.1.le
  have hdegree := weak_lower_numerator_degree_exact hn hc hcdeg ha hfreqA
  apply no_weak_lower_contact_data_of_budget hn ha hc hcdeg hfreqA Data (by omega)
  omega

/-- 含无穷远接触的分支：少一个零矩，但接触预算也至少减少一。 -/
theorem no_lower_infinite_contact_data
    {n : ℕ} (hn : 2 ≤ n) {a b c : ℝ[X]}
    (ha : HurwitzClass n a) (hb : HurwitzClass n b)
    (hc : c ≠ 0) (hcdeg : c.natDegree ≤ n-1)
    (hfreqA : ∀ w : ℝ, 0 ≤ (value c (w*Complex.I)/value a (w*Complex.I)).re)
    (hfreqB : ∀ w : ℝ, 0 ≤ (value c (w*Complex.I)/value b (w*Complex.I)).re)
    (Data : LowerContactData (n-2) a b c)
    (hinfinite : (frequencyCross c a).coeff (2*(n-1)) = 0 ∨
      (frequencyCross c b).coeff (2*(n-1)) = 0) : False := by
  have hcount := lower_contact_card_degree_budget Data ha hb hc (by omega)
    (weak_frequencyCross_nonnegative ha.2.2 hfreqA)
    (weak_frequencyCross_nonnegative hb.2.2 hfreqB)
  have hdegA := lower_frequencyCross_degree (by omega) c a hcdeg ha.2.1.le
  have hdegB := lower_frequencyCross_degree (by omega) c b hcdeg hb.2.1.le
  have hdegree := weak_lower_numerator_degree_exact (by omega) hc hcdeg ha hfreqA
  apply no_weak_lower_contact_data_of_budget (by omega) ha hc hcdeg hfreqA Data (by omega)
  rcases hinfinite with hcontact | hcontact
  · have hdrop := lower_cross_degree_of_infinite_contact hn c a hcdeg ha.2.1.le hcontact
    omega
  · have hdrop := lower_cross_degree_of_infinite_contact hn c b hcdeg hb.2.1.le hcontact
    omega

/-! ## 由失效产生实际临界证书 -/

theorem lowerFeature_blend (n : ℕ) (a b : ℝ[X]) (t u : ℝ) :
    lowerFeature n (blend a b t) u = (1-t) • lowerFeature n a u+t • lowerFeature n b u := by
  ext k
  exact lowerCompactPairing_denominator_blend n (X^k.val) a b t u

private def lowerTestDomain : Set (ℝ × ℝ) := ({0,1} : Set ℝ) ×ˢ Icc (-1 : ℝ) 1

private theorem lowerTestDomain_compact : IsCompact lowerTestDomain :=
  (isCompact_singleton.insert (0 : ℝ)).prod isCompact_Icc

private theorem lowerTestDomain_nonempty : lowerTestDomain.Nonempty := by
  exact ⟨(0,0),by simp [lowerTestDomain]⟩

def lowerTestFeature (n : ℕ) (a b : ℝ[X]) (t : ℝ) (su : ℝ × ℝ) : CoefficientSpace (n-1) :=
  (1-su.1) • lowerFeature n a su.2+
    su.1 • ((1-t) • lowerFeature n a su.2+t • lowerFeature n b su.2)

def lowerSupportTest (n : ℕ) (a b : ℝ[X]) (t : ℝ)
    (v : CoefficientSpace (n-1)) (su : ℝ × ℝ) : ℝ :=
  dotFunctional (n-1) v (lowerTestFeature n a b t su)

theorem lowerTestFeature_left (n : ℕ) (a b : ℝ[X]) (t u : ℝ) :
    lowerTestFeature n a b t (0,u) = lowerFeature n a u := by simp [lowerTestFeature]

theorem lowerTestFeature_right (n : ℕ) (a b : ℝ[X]) (t u : ℝ) :
    lowerTestFeature n a b t (1,u) = lowerFeature n (blend a b t) u := by
  simp [lowerTestFeature,lowerFeature_blend]

theorem lowerSupportTest_scale (n : ℕ) (a b : ℝ[X]) (t r : ℝ)
    (v : CoefficientSpace (n-1)) (su : ℝ × ℝ) :
    lowerSupportTest n a b t (r • v) su = r*lowerSupportTest n a b t v su := by
  simp only [lowerSupportTest,dotFunctional_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem lowerSupportTest_continuous (n : ℕ) (a b : ℝ[X]) :
    Continuous (fun x : (ℝ × CoefficientSpace (n-1)) × (ℝ × ℝ) =>
      lowerSupportTest n a b x.1.1 x.1.2 x.2) := by
  simp only [lowerSupportTest,dotFunctional_apply]
  apply continuous_finset_sum
  intro k _
  have hA : Continuous (fun x : (ℝ × CoefficientSpace (n-1)) × (ℝ × ℝ) => lowerFeature n a x.2.2 k) :=
    (lowerCompactPairing_continuous n (X^k.val) a).comp (continuous_snd.comp continuous_snd)
  have hB : Continuous (fun x : (ℝ × CoefficientSpace (n-1)) × (ℝ × ℝ) => lowerFeature n b x.2.2 k) :=
    (lowerCompactPairing_continuous n (X^k.val) b).comp (continuous_snd.comp continuous_snd)
  simp only [lowerTestFeature,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  fun_prop

theorem lowerSupportTest_left (n : ℕ) (a b : ℝ[X]) (t u : ℝ) (v : CoefficientSpace (n-1)) :
    lowerSupportTest n a b t v (0,u) = lowerCompactPairing n (polynomialFrom (n-1) v) a u := by
  rw [lowerSupportTest,lowerTestFeature_left,← lower_pairing_feature_identity]

theorem lowerSupportTest_right (n : ℕ) (a b : ℝ[X]) (t u : ℝ) (v : CoefficientSpace (n-1)) :
    lowerSupportTest n a b t v (1,u) = lowerCompactPairing n (polynomialFrom (n-1) v) (blend a b t) u := by
  rw [lowerSupportTest,lowerTestFeature_right,← lower_pairing_feature_identity]

theorem lowerSupportTest_positive_iff (n : ℕ) (a b : ℝ[X]) (t : ℝ) (v : CoefficientSpace (n-1)) :
    (∀ su ∈ lowerTestDomain, 0 < lowerSupportTest n a b t v su) ↔
    (∀ u ∈ Icc (-1 : ℝ) 1, 0 < lowerCompactPairing n (polynomialFrom (n-1) v) a u) ∧
    (∀ u ∈ Icc (-1 : ℝ) 1, 0 < lowerCompactPairing n (polynomialFrom (n-1) v) (blend a b t) u) := by
  constructor
  · intro h
    constructor
    · intro u hu
      simpa only [lowerSupportTest_left] using h (0,u) ⟨by simp,hu⟩
    · intro u hu
      simpa only [lowerSupportTest_right] using h (1,u) ⟨by simp,hu⟩
  · rintro ⟨hA,hB⟩ ⟨s,u⟩ ⟨hs,hu⟩
    rcases (show s = 0 ∨ s = 1 by simpa using hs) with rfl | rfl
    · simpa only [lowerSupportTest_left] using hA u hu
    · simpa only [lowerSupportTest_right] using hB u hu

theorem lowerSupportTest_feasible_iff (n : ℕ) (a b : ℝ[X]) (t : ℝ) :
    (∃ v : CoefficientSpace (n-1), ∀ su ∈ lowerTestDomain, 0 < lowerSupportTest n a b t v su) ↔
      LowerCompactFeasible n a (blend a b t) := by
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨polynomialFrom (n-1) v,polynomialFrom_degree (n-1) v,
      (lowerSupportTest_positive_iff n a b t v).mp hv⟩
  · rintro ⟨c,hdeg,hA,hB⟩
    let v : CoefficientSpace (n-1) := fun k => c.coeff k.val
    have hc : polynomialFrom (n-1) v = c := polynomialFrom_coefficients (n-1) c hdeg
    refine ⟨v,(lowerSupportTest_positive_iff n a b t v).mpr ?_⟩
    simpa only [hc] using And.intro hA hB

structure LowerCriticalCertificate (n : ℕ) (a b : ℝ[X]) where
  support : CoefficientSpace (n-1)
  support_norm : ‖support‖ = 1
  support_nonnegative : ∀ x ∈ lowerFeatureSet n a b, 0 ≤ dotFunctional (n-1) support x
  count : ℕ
  point : Fin count → CoefficientSpace (n-1)
  weight : Fin count → ℝ
  point_mem : ∀ i, point i ∈ lowerFeatureSet n a b
  weight_pos : ∀ i, 0 < weight i
  weight_sum : ∑ i, weight i = 1
  balance : ∑ i, weight i • point i = 0
  contact : ∀ i, dotFunctional (n-1) support (point i) = 0

/-- 任意阶低阶综合失效会在中途产生非零支撑及有限、正权的接触证书。 -/
theorem critical_certificate_of_failed_lower_segment
    {n : ℕ} (hn : 0 < n) (a b : ℝ[X]) (ha : HurwitzClass n a)
    (hfail : ¬ LowerCompactFeasible n a b) :
    ∃ t ∈ Icc (0 : ℝ) 1, Nonempty (LowerCriticalCertificate n a (blend a b t)) := by
  classical
  have hstart : ∃ v : CoefficientSpace (n-1),
      ∀ su ∈ lowerTestDomain, 0 < lowerSupportTest n a b 0 v su := by
    apply (lowerSupportTest_feasible_iff n a b 0).mpr
    simpa [blend] using lower_compact_self_feasible hn ha
  have hfinish : ¬ ∃ v : CoefficientSpace (n-1),
      ∀ su ∈ lowerTestDomain, 0 < lowerSupportTest n a b 1 v su := by
    intro h
    exact hfail (by simpa [blend] using (lowerSupportTest_feasible_iff n a b 1).mp h)
  obtain ⟨t,ht,v,hv,hsupport,hfailed⟩ := weak_support_at_transition lowerTestDomain lowerTestDomain_compact
    lowerTestDomain_nonempty (lowerSupportTest n a b) (lowerSupportTest_continuous n a b)
    (lowerSupportTest_scale n a b) hstart hfinish
  have hweak : ∀ x ∈ lowerFeatureSet n a (blend a b t), 0 ≤ dotFunctional (n-1) v x := by
    rintro x (⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩)
    · simpa only [lowerSupportTest,lowerTestFeature_left] using hsupport (0,u) ⟨by simp,hu⟩
    · simpa only [lowerSupportTest,lowerTestFeature_right] using hsupport (1,u) ⟨by simp,hu⟩
  have hzero : (0 : CoefficientSpace (n-1)) ∈ closedConvexHull ℝ (lowerFeatureSet n a (blend a b t)) := by
    by_contra hnot
    exact hfailed ((lowerSupportTest_feasible_iff n a b t).mpr
      ((lower_synthesis_iff_origin_excluded n a (blend a b t)).mpr hnot))
  rw [closedConvexHull_eq_convexHull_of_compact _ (lowerFeatureSet_compact n a (blend a b t))] at hzero
  obtain ⟨ι,hι,z,w,hz,_,hw,hsum,hbalance⟩ := eq_pos_convex_span_of_mem_convexHull hzero
  letI : Fintype ι := hι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hcontacts := balance_forces_contacts z w (dotFunctional (n-1) v) hw hbalance
    (fun i => hweak (z i) (hz ⟨i,rfl⟩))
  refine ⟨t,ht,⟨{
    support := v
    support_norm := hv
    support_nonnegative := hweak
    count := Fintype.card ι
    point := fun i => z (e.symm i)
    weight := fun i => w (e.symm i)
    point_mem := fun i => hz ⟨e.symm i,rfl⟩
    weight_pos := fun i => hw (e.symm i)
    weight_sum := (e.symm.sum_comp w).trans hsum
    balance := (e.symm.sum_comp (fun i => w i • z i)).trans hbalance
    contact := fun i => hcontacts (e.symm i)
  }⟩⟩

def LowerCriticalCertificate.numerator {n : ℕ} {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) : ℝ[X] := polynomialFrom (n-1) Crt.support

theorem LowerCriticalCertificate.numerator_degree {n : ℕ} {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) : Crt.numerator.natDegree ≤ n-1 :=
  polynomialFrom_degree (n-1) Crt.support

theorem LowerCriticalCertificate.numerator_ne_zero {n : ℕ} {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) : Crt.numerator ≠ 0 := by
  intro hz
  have hv : Crt.support = 0 := by
    funext k
    have h := polynomialFrom_coefficient (n-1) Crt.support k
    rw [show polynomialFrom (n-1) Crt.support = 0 from hz,Polynomial.coeff_zero] at h
    exact h.symm
  have hnorm := Crt.support_norm
  simp [hv] at hnorm

theorem LowerCriticalCertificate.compact_nonnegative {n : ℕ} {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) :
    (∀ u ∈ Icc (-1 : ℝ) 1, 0 ≤ lowerCompactPairing n Crt.numerator a u) ∧
    (∀ u ∈ Icc (-1 : ℝ) 1, 0 ≤ lowerCompactPairing n Crt.numerator b u) := by
  constructor
  · intro u hu
    have h := Crt.support_nonnegative _ (Or.inl ⟨u,hu,rfl⟩)
    simpa only [← lower_pairing_feature_identity] using h
  · intro u hu
    have h := Crt.support_nonnegative _ (Or.inr ⟨u,hu,rfl⟩)
    simpa only [← lower_pairing_feature_identity] using h

theorem LowerCriticalCertificate.boundary_nonnegative {n : ℕ} (hn : 0 < n) {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) (ha : a.natDegree = n) (hb : b.natDegree = n) :
    (∀ w : ℝ, 0 ≤ (value Crt.numerator (w*Complex.I)/value a (w*Complex.I)).re) ∧
    (∀ w : ℝ, 0 ≤ (value Crt.numerator (w*Complex.I)/value b (w*Complex.I)).re) :=
  ⟨lower_boundary_nonnegative_of_compact hn _ _ Crt.numerator_degree ha.le Crt.compact_nonnegative.1,
   lower_boundary_nonnegative_of_compact hn _ _ Crt.numerator_degree hb.le Crt.compact_nonnegative.2⟩

structure LowerAtomCoordinates (n : ℕ) (a b : ℝ[X]) (N : ℕ)
    (z : Fin N → CoefficientSpace (n-1)) where
  right : Fin N → Bool
  parameter : Fin N → ℝ
  parameter_mem : ∀ i, parameter i ∈ Icc (-1 : ℝ) 1
  represents : ∀ i, z i = lowerFeature n (endpoint a b (right i)) (parameter i)

theorem LowerCriticalCertificate.coordinates_exist {n : ℕ} {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) : Nonempty (LowerAtomCoordinates n a b Crt.count Crt.point) := by
  classical
  have h (i : Fin Crt.count) : ∃ r : Bool, ∃ u : ℝ,
      u ∈ Icc (-1 : ℝ) 1 ∧ Crt.point i = lowerFeature n (endpoint a b r) u := by
    rcases Crt.point_mem i with ⟨u,hu,hz⟩ | ⟨u,hu,hz⟩
    · exact ⟨false,u,hu,hz.symm⟩
    · exact ⟨true,u,hu,hz.symm⟩
  choose r u hu hz using h
  exact ⟨⟨r,u,hu,hz⟩⟩

def LowerCriticalCertificate.coordinates {n : ℕ} {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) : LowerAtomCoordinates n a b Crt.count Crt.point :=
  Classical.choice Crt.coordinates_exist

def LowerCriticalCertificate.denominator {n : ℕ} {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) (i : Fin Crt.count) : ℝ[X] := endpoint a b (Crt.coordinates.right i)

def LowerCriticalCertificate.parameter {n : ℕ} {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) (i : Fin Crt.count) : ℝ := Crt.coordinates.parameter i

def LowerCriticalCertificate.finiteAtoms {n : ℕ} {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) : Finset (Fin Crt.count) :=
  Finset.univ.filter (fun i => |Crt.parameter i| < 1)

def LowerCriticalCertificate.frequency {n : ℕ} {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) (i : Fin Crt.count) : ℝ :=
  Crt.parameter i/(1-|Crt.parameter i|)

def LowerCriticalCertificate.finiteMass {n : ℕ} {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) (i : Fin Crt.count) : ℝ :=
  Crt.weight i*(1-|Crt.parameter i|)^(2*(n-1))

theorem LowerCriticalCertificate.point_representation {n : ℕ} {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) (i : Fin Crt.count) :
    Crt.point i = lowerFeature n (Crt.denominator i) (Crt.parameter i) := Crt.coordinates.represents i

theorem LowerCriticalCertificate.finite_scale_positive {n : ℕ} {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) {i : Fin Crt.count} (hi : i ∈ Crt.finiteAtoms) :
    0 < 1-|Crt.parameter i| := sub_pos.mpr (Finset.mem_filter.mp hi).2

theorem LowerCriticalCertificate.finiteMass_positive {n : ℕ} {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) {i : Fin Crt.count} (hi : i ∈ Crt.finiteAtoms) :
    0 < Crt.finiteMass i := mul_pos (Crt.weight_pos i) (pow_pos (Crt.finite_scale_positive hi) _)

theorem LowerCriticalCertificate.infinite_scale_zero {n : ℕ} {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) {i : Fin Crt.count} (hi : i ∉ Crt.finiteAtoms) :
    1-|Crt.parameter i| = 0 := by
  have hrange := Crt.coordinates.parameter_mem i
  have hle : |Crt.parameter i| ≤ 1 := abs_le.mpr hrange
  have hnot : ¬|Crt.parameter i| < 1 := by simpa [LowerCriticalCertificate.finiteAtoms] using hi
  linarith

theorem lowerCompactPairing_of_scale_zero (n : ℕ) (c p : ℝ[X])
    (u : ℝ) (hu : 1-|u| = 0) :
    lowerCompactPairing n c p u = (frequencyCross c p).coeff (2*(n-1)) := by
  have habs : |u| = 1 := by linarith
  have hsq : u^2 = 1 := by
    have h := congrArg (fun x : ℝ => x^2) habs
    simpa using h
  simp [lowerCompactPairing,hu,realHomogeneousValue_at_infinity,pow_mul,hsq]

theorem LowerCriticalCertificate.finite_feature {n : ℕ} (hn : 0 < n) {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) (ha : HurwitzClass n a) (hb : HurwitzClass n b)
    {i : Fin Crt.count} (hi : i ∈ Crt.finiteAtoms) (k : Fin (n-1+1)) :
    Crt.point i k = (1-|Crt.parameter i|)^(2*(n-1))*
      pairing ((Crt.frequency i*Complex.I)^k.val) (value (Crt.denominator i) (Crt.frequency i*Complex.I)) := by
  have hd := endpoint_hurwitz ha hb (Crt.coordinates.right i)
  rw [Crt.point_representation]
  unfold lowerFeature
  rw [lowerCompactPairing_finite hn (X^k.val) (Crt.denominator i)
    (by simp; omega) hd.2.1.le _ (ne_of_gt (Crt.finite_scale_positive hi))]
  simp [LowerCriticalCertificate.frequency,value]

theorem LowerCriticalCertificate.infinite_feature {n : ℕ} (hn : 2 ≤ n) {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) (ha : HurwitzClass n a) (hb : HurwitzClass n b)
    {i : Fin Crt.count} (hi : i ∉ Crt.finiteAtoms) (k : Fin (n-1+1)) :
    Crt.point i k =
      (if k.val = n-1 then 1 else 0)*(Crt.denominator i).coeff (n-1)-
        (if k.val = n-2 then 1 else 0) := by
  have hd := endpoint_hurwitz ha hb (Crt.coordinates.right i)
  have htop : (Crt.denominator i).coeff n = 1 := by
    simpa [← hd.2.1] using hd.1.coeff_natDegree
  rw [Crt.point_representation]
  unfold lowerFeature
  rw [lowerCompactPairing_of_scale_zero _ _ _ _ (Crt.infinite_scale_zero hi)]
  rw [lower_frequencyCross_top (n := n) hn (X^k.val) (Crt.denominator i)
    (by simp; omega) (by simpa only [LowerCriticalCertificate.denominator] using hd.2.1.le),htop]
  simp [Polynomial.coeff_X_pow,eq_comm]

theorem LowerCriticalCertificate.finiteAtoms_nonempty {n : ℕ} (hn : 2 ≤ n) {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) (ha : HurwitzClass n a) (hb : HurwitzClass n b) :
    Crt.finiteAtoms.Nonempty := by
  classical
  by_contra hnot
  have hall (i : Fin Crt.count) : i ∉ Crt.finiteAtoms := fun hi => hnot ⟨i,hi⟩
  let k : Fin (n-1+1) := ⟨n-2,by omega⟩
  have h := congrArg (fun x : CoefficientSpace (n-1) => x k) Crt.balance
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.zero_apply,smul_eq_mul] at h
  have heq : (∑ i : Fin Crt.count, Crt.weight i*Crt.point i k) = -∑ i, Crt.weight i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Crt.infinite_feature hn ha hb (hall i)]
    simp [k,show n-2 ≠ n-1 by omega]
  rw [heq,Crt.weight_sum] at h
  norm_num at h

theorem LowerCriticalCertificate.finite_contact {n : ℕ} (hn : 0 < n) {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) (ha : HurwitzClass n a) (hb : HurwitzClass n b)
    {i : Fin Crt.count} (hi : i ∈ Crt.finiteAtoms) :
    pairing (value Crt.numerator (Crt.frequency i*Complex.I))
      (value (Crt.denominator i) (Crt.frequency i*Complex.I)) = 0 := by
  have hd := endpoint_hurwitz ha hb (Crt.coordinates.right i)
  have hc := Crt.contact i
  rw [Crt.point_representation,← lower_pairing_feature_identity] at hc
  change lowerCompactPairing n Crt.numerator (Crt.denominator i) (Crt.parameter i) = 0 at hc
  rw [lowerCompactPairing_finite hn Crt.numerator (Crt.denominator i)
    Crt.numerator_degree hd.2.1.le _ (ne_of_gt (Crt.finite_scale_positive hi))] at hc
  exact (mul_eq_zero.mp hc).resolve_left (ne_of_gt (pow_pos (Crt.finite_scale_positive hi) _))

theorem LowerCriticalCertificate.infinite_contact {n : ℕ} {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) {i : Fin Crt.count} (hi : i ∉ Crt.finiteAtoms) :
    (frequencyCross Crt.numerator (Crt.denominator i)).coeff (2*(n-1)) = 0 := by
  have hc := Crt.contact i
  rw [Crt.point_representation,← lower_pairing_feature_identity] at hc
  change lowerCompactPairing n Crt.numerator (Crt.denominator i) (Crt.parameter i) = 0 at hc
  rwa [lowerCompactPairing_of_scale_zero _ _ _ _ (Crt.infinite_scale_zero hi)] at hc

/-- 无穷远原子只影响最高两个系数方向；其余方向仍给出零矩。 -/
theorem LowerCriticalCertificate.finite_moments {n : ℕ} (hn : 2 ≤ n) {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) (ha : HurwitzClass n a) (hb : HurwitzClass n b)
    (M : ℕ) (hM : M ≤ n-1)
    (hvanish : ∀ i ∉ Crt.finiteAtoms, ∀ k < M, k < n-2)
    (k : ℕ) (hk : k < M) :
    (∑ i ∈ Crt.finiteAtoms, Crt.finiteMass i*
      pairing ((Crt.frequency i*Complex.I)^k) (value (Crt.denominator i) (Crt.frequency i*Complex.I))) = 0 := by
  classical
  let j : Fin (n-1+1) := ⟨k,by omega⟩
  have h := congrArg (fun x : CoefficientSpace (n-1) => x j) Crt.balance
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.zero_apply,smul_eq_mul] at h
  have hrestrict : (∑ i ∈ Crt.finiteAtoms, Crt.weight i*Crt.point i j) =
      ∑ i : Fin Crt.count, Crt.weight i*Crt.point i j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hki := hvanish i hi k hk
    rw [Crt.infinite_feature hn ha hb hi]
    simp [j,ne_of_lt hki,show k ≠ n-1 by omega]
  rw [← hrestrict] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Crt.finite_feature (by omega) ha hb hi j]
  dsimp [LowerCriticalCertificate.finiteMass,j]
  ring

theorem LowerCriticalCertificate.symmetric_data {n : ℕ} (hn : 2 ≤ n) {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) (ha : HurwitzClass n a) (hb : HurwitzClass n b)
    (hsegment : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t))
    (M : ℕ) (hM : M ≤ n-1)
    (hvanish : ∀ i ∉ Crt.finiteAtoms, ∀ k < M, k < n-2) :
    Nonempty (LowerContactData M a b Crt.numerator) := by
  classical
  let F := Crt.finiteAtoms
  let f := Crt.frequency
  let m := Crt.finiteMass
  let side := Crt.coordinates.right
  let S := signedFrequencies F f
  let r := groupedResidue F f m a b side
  have hF : F.Nonempty := Crt.finiteAtoms_nonempty hn ha hb
  have hm : ∀ i ∈ F, 0 < m i := fun i hi => Crt.finiteMass_positive hi
  have hcontact : ∀ i ∈ F, pairing (value Crt.numerator (imaginaryNode (f i)))
      (value (endpoint a b (side i)) (imaginaryNode (f i))) = 0 := by
    intro i hi
    exact Crt.finite_contact (by omega) ha hb hi
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
    have hzero := congrArg (fun x : ℝ => (x : ℂ)) (Crt.finite_moments hn ha hb M hM hvanish k hk)
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
      exact Crt.finite_contact (by omega) ha hb hi
    simp only [S,signedFrequencies,Finset.mem_union,Finset.mem_image] at hw
    rcases hw with ⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩
    · have hr := hroot i hi
      cases hs : Crt.coordinates.right i
      · left
        simpa [LowerCriticalCertificate.denominator,endpoint,hs] using hr
      · right
        simpa [LowerCriticalCertificate.denominator,endpoint,hs] using hr
    · have hr : (frequencyCross Crt.numerator (Crt.denominator i)).eval (-f i) = 0 := by
        rw [frequencyCross_neg_eval]
        exact hroot i hi
      cases hs : Crt.coordinates.right i
      · left
        simpa [LowerCriticalCertificate.denominator,endpoint,hs] using hr
      · right
        simpa [LowerCriticalCertificate.denominator,endpoint,hs] using hr

/-- 两类接触计数共同排除所有低阶临界证书。 -/
theorem no_lower_critical_certificate {n : ℕ} (hn : 2 ≤ n) {a b : ℝ[X]}
    (Crt : LowerCriticalCertificate n a b) (ha : HurwitzClass n a) (hb : HurwitzClass n b)
    (hsegment : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t)) : False := by
  classical
  have hfreq := Crt.boundary_nonnegative (by omega) ha.2.1 hb.2.1
  by_cases hinfinite : ∃ i : Fin Crt.count, i ∉ Crt.finiteAtoms
  · obtain ⟨i,hi⟩ := hinfinite
    obtain ⟨Data⟩ := Crt.symmetric_data hn ha hb hsegment (n-2) (by omega) (by intros; assumption)
    apply no_lower_infinite_contact_data hn ha hb Crt.numerator_ne_zero Crt.numerator_degree
      hfreq.1 hfreq.2 Data
    have hcontact := Crt.infinite_contact hi
    cases hs : Crt.coordinates.right i
    · left
      simpa [LowerCriticalCertificate.denominator,endpoint,hs] using hcontact
    · right
      simpa [LowerCriticalCertificate.denominator,endpoint,hs] using hcontact
  · have hall : ∀ i : Fin Crt.count, i ∈ Crt.finiteAtoms := by
      simpa only [not_exists,not_not] using hinfinite
    obtain ⟨Data⟩ := Crt.symmetric_data hn ha hb hsegment (n-1) le_rfl
      (fun i hi => (hi (hall i)).elim)
    exact no_lower_finite_contact_data (by omega) ha hb Crt.numerator_ne_zero Crt.numerator_degree
      hfreq.1 hfreq.2 Data

/-- 任意 n≥2 的稳定线段存在至多 n−1 阶、在新紧化上处处严格正的公共分子。 -/
theorem stable_segment_lower_compact_feasible
    {n : ℕ} (hn : 2 ≤ n) (a b : ℝ[X])
    (ha : a.Monic) (hb : b.Monic) (hda : a.natDegree = n) (hdb : b.natDegree = n)
    (hsegment : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t)) :
    LowerCompactFeasible n a b := by
  classical
  have hA : HurwitzClass n a := ⟨ha,hda,by simpa [blend] using hsegment 0 (by constructor <;> norm_num)⟩
  by_contra hfail
  obtain ⟨t,ht,⟨Crt⟩⟩ := critical_certificate_of_failed_lower_segment (by omega) a b hA hfail
  have hB : HurwitzClass n (blend a b t) :=
    ⟨(blend_monic_and_degree ha hb hda hdb t).1,
      (blend_monic_and_degree ha hb hda hdb t).2,hsegment t ht⟩
  apply no_lower_critical_certificate hn Crt hA hB
  intro u hu
  rw [blend_initial_subsegment]
  apply hsegment (u*t)
  constructor
  · exact mul_nonneg hu.1 ht.1
  · calc
      u*t ≤ 1*t := mul_le_mul_of_nonneg_right hu.2 ht.1
      _ ≤ 1 := by simpa only [one_mul] using ht.2

/-! ## 首一化、精确次数与最终任意阶定理 -/

theorem lower_frequency_positive_numerator_stable
    {n : ℕ} (hn : 0 < n) {c p : ℝ[X]}
    (hp : HurwitzClass n p) (hcdeg : c.natDegree ≤ n-1)
    (hfreq : FrequencyPositive c p) : Stable c := by
  have hc : c ≠ 0 := by
    intro hzero
    have h := hfreq 0
    simp [hzero,value] at h
  have hleft := (weak_lower_root_properties hn hp hc hcdeg (fun w => (hfreq w).le)).1
  intro z hz hzero
  have hzre : z.re = 0 := le_antisymm (hleft z hzero) hz
  have hzaxis : (z.im : ℂ)*Complex.I = z := by
    apply Complex.ext <;> simp [hzre]
  have h := hfreq z.im
  rw [hzaxis,hzero,zero_div] at h
  norm_num at h

theorem lower_frequency_positive_leadingCoeff_pos
    {n : ℕ} (hn : 0 < n) {c p : ℝ[X]}
    (hp : HurwitzClass n p) (hcdeg : c.natDegree ≤ n-1)
    (hfreq : FrequencyPositive c p) : 0 < c.leadingCoeff := by
  have hc : c ≠ 0 := by
    intro hzero
    have h := hfreq 0
    simp [hzero,value] at h
  have hlead : c.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hc
  have hcstable := lower_frequency_positive_numerator_stable hn hp hcdeg hfreq
  have hp0 := stable_monic_constant_pos hp.1 hp.2.2 (by rw [hp.2.1]; exact hn)
  have hvzero (q : ℝ[X]) : value q 0 = (q.coeff 0 : ℂ) := by
    rw [value_eq_mapped_eval,← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_map]
    rfl
  have hc0 : 0 < c.coeff 0 := by
    have hpair := (positive_quotient_iff _ _ (stable_axis_ne_zero hp.2.2 0)).mp (hfreq 0)
    have hreal : 0 < c.coeff 0*p.coeff 0 := by
      simpa [hvzero,pairing] using hpair
    exact (mul_pos_iff_of_pos_right hp0).mp hreal
  let q := C c.leadingCoeff⁻¹*c
  have hqmonic : q.Monic := by
    exact Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlead)
  have hqvalue (z : ℂ) : value q z = (c.leadingCoeff : ℂ)⁻¹*value c z := by
    simp [q,value]
  have hqstable : Stable q := by
    intro z hz hzero
    rw [hqvalue] at hzero
    apply hcstable z hz
    exact (mul_eq_zero.mp hzero).resolve_left (inv_ne_zero (Complex.ofReal_ne_zero.mpr hlead))
  have hq0 : 0 < q.coeff 0 := by
    by_cases hqdeg : q.natDegree = 0
    · have hcoeff : q.coeff 0 = 1 := by rw [← hqdeg]; exact hqmonic.coeff_natDegree
      rw [hcoeff]
      norm_num
    · exact stable_monic_constant_pos hqmonic hqstable (Nat.pos_of_ne_zero hqdeg)
  change 0 < (C c.leadingCoeff⁻¹*c).coeff 0 at hq0
  rw [Polynomial.coeff_C_mul] at hq0
  exact inv_pos.mp ((mul_pos_iff_of_pos_right hc0).mp hq0)

/-- 对可行的低阶公共分子作正比例缩放，得到首一且次数恰为 n−1 的分子。 -/
theorem normalize_lower_common_numerator
    {n : ℕ} (hn : 0 < n) {a b c : ℝ[X]}
    (ha : HurwitzClass n a) (hcdeg : c.natDegree ≤ n-1)
    (hA : FrequencyPositive c a) (hB : FrequencyPositive c b) :
    LowerCommonNumerator n a b (C c.leadingCoeff⁻¹*c) := by
  have hlead := lower_frequency_positive_leadingCoeff_pos hn ha hcdeg hA
  have hdeg := lower_frequency_positive_degree_exact hn ha hcdeg hA
  refine ⟨Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    (inv_mul_cancel₀ (ne_of_gt hlead)),?_,?_,?_⟩
  · rw [Polynomial.natDegree_C_mul (inv_ne_zero (ne_of_gt hlead)),hdeg]
  · exact frequencyPositive_scale hA _ (inv_pos.mpr hlead)
  · exact frequencyPositive_scale hB _ (inv_pos.mpr hlead)

/-- 任意阶低一阶公共分子存在性：分母始终 n 阶，分子恰为 n−1 阶。 -/
theorem stable_segment_has_lower_common_numerator
    (n : ℕ) (hn : 0 < n) (a b : ℝ[X])
    (ha : a.Monic) (hb : b.Monic) (hda : a.natDegree = n) (hdb : b.natDegree = n)
    (hsegment : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t)) :
    ∃ c : ℝ[X], LowerCommonNumerator n a b c := by
  have hA : HurwitzClass n a := ⟨ha,hda,by simpa [blend] using hsegment 0 (by constructor <;> norm_num)⟩
  have hB : HurwitzClass n b := ⟨hb,hdb,by simpa [blend] using hsegment 1 (by constructor <;> norm_num)⟩
  by_cases hn1 : n = 1
  · refine ⟨1,?_⟩
    rw [hn1]
    exact first_order_lower_numerator a b ha hb (hda.trans hn1) (hdb.trans hn1) hA.2.2 hB.2.2
  · obtain ⟨c,hdeg,hcompactA,hcompactB⟩ := stable_segment_lower_compact_feasible (by omega)
      a b ha hb hda hdb hsegment
    have hfreqA := ((lower_compact_positivity_iff hn c a hdeg hA).mp hcompactA).2
    have hfreqB := ((lower_compact_positivity_iff hn c b hdeg hB).mp hcompactB).2
    exact ⟨C c.leadingCoeff⁻¹*c,normalize_lower_common_numerator hn hA hdeg hfreqA hfreqB⟩

/-- 文件开头陈述的完整任意阶目标现已得到证明。 -/
theorem lower_synthesis_statement : LowerSynthesisStatement := by
  intro n hn a b ha hb hda hdb hsegment
  exact stable_segment_has_lower_common_numerator n hn a b ha hb hda hdb hsegment

/-- 完整等价定理；SPR 自带分母稳定性，分子的首一与低一阶次数另外显式记录。 -/
theorem lower_common_spr_iff_stable_segment
    (n : ℕ) (hn : 0 < n) (a b : ℝ[X])
    (ha : a.Monic) (hb : b.Monic) (hda : a.natDegree = n) (hdb : b.natDegree = n) :
    (∃ c : ℝ[X], c.Monic ∧ c.natDegree = n-1 ∧
      SPR.TeacherCore.SPR c a ∧ SPR.TeacherCore.SPR c b) ↔
      (∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t)) := by
  constructor
  · rintro ⟨c,_,_,hA,hB⟩ t ht
    exact (common_spr_implies_segment_hurwitz ha hb hda hdb hA hB t ht).2.2
  · intro hsegment
    obtain ⟨c,hc⟩ := stable_segment_has_lower_common_numerator n hn a b ha hb hda hdb hsegment
    refine ⟨c,hc.1,hc.2.1,⟨?_,hc.2.2.1⟩,⟨?_,hc.2.2.2⟩⟩
    · simpa [blend] using hsegment 0 (by constructor <;> norm_num)
    · simpa [blend] using hsegment 1 (by constructor <;> norm_num)

/-- 同一个首一 n−1 阶分子对全部线段参数和全部实频率同时有效。 -/
theorem lower_common_numerator_on_whole_segment
    (n : ℕ) (hn : 0 < n) (a b : ℝ[X])
    (ha : a.Monic) (hb : b.Monic) (hda : a.natDegree = n) (hdb : b.natDegree = n)
    (hsegment : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t)) :
    ∃ c : ℝ[X], c.Monic ∧ c.natDegree = n-1 ∧
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → SPR.TeacherCore.SPR c (blend a b t) := by
  obtain ⟨c,hc⟩ := stable_segment_has_lower_common_numerator n hn a b ha hb hda hdb hsegment
  exact ⟨c,lower_numerator_on_whole_segment hc hsegment⟩

end
end SPR.LowerNumeratorTeacher

/-! ## 同阶结论：由低一阶存在性经小扰动直接推出 -/

namespace SPR.TeacherCore

noncomputable section
open Polynomial Set Filter
open scoped Topology ComplexConjugate

/-- 同阶充分性只调用低一阶主定理与升阶引理，无需另一套接触证书证明。 -/
theorem stable_segment_has_common_numerator (n : ℕ) (a b : ℝ[X])
    (ha : a.Monic) (hb : b.Monic) (hda : a.natDegree = n) (hdb : b.natDegree = n)
    (hsegment : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t)) :
    ∃ c : ℝ[X], c.Monic ∧ c.natDegree = n ∧ SPR c a ∧ SPR c b := by
  cases n with
  | zero =>
    have hca : a.coeff 0 = 1 := by rw [← hda]; exact ha.coeff_natDegree
    have hcb : b.coeff 0 = 1 := by rw [← hdb]; exact hb.coeff_natDegree
    have ha1 : a = 1 := by rw [Polynomial.eq_C_of_natDegree_eq_zero hda,hca]; rfl
    have hb1 : b = 1 := by rw [Polynomial.eq_C_of_natDegree_eq_zero hdb,hcb]; rfl
    have hspr : SPR (1 : ℝ[X]) 1 := by
      constructor
      · intro z _
        simp [value]
      · intro w
        simp [value]
    exact ⟨1,Polynomial.monic_one,by simp,ha1 ▸ hspr,hb1 ▸ hspr⟩
  | succ d =>
    obtain ⟨c,hc⟩ := SPR.LowerNumeratorTeacher.stable_segment_has_lower_common_numerator
      (d+1) (by omega) a b ha hb hda hdb hsegment
    obtain ⟨δ,hδ,β,_,hβ,hdeg,hwhole⟩ := SPR.LowerNumeratorTeacher.raise_then_normalize
      (by omega) a b c a ha hb ha hda hdb hda hc hsegment
    refine ⟨β,hβ,hdeg,?_,?_⟩
    · simpa [blend] using hwhole 0 (by constructor <;> norm_num)
    · simpa [blend] using hwhole 1 (by constructor <;> norm_num)

/-- 任意阶等价定理：公共首一同阶 SPR 分子存在，当且仅当分母线段稳定。 -/
theorem common_spr_iff_stable_segment (n : ℕ) (a b : ℝ[X])
    (ha : a.Monic) (hb : b.Monic) (hda : a.natDegree = n) (hdb : b.natDegree = n) :
    (∃ c : ℝ[X], c.Monic ∧ c.natDegree = n ∧ SPR c a ∧ SPR c b) ↔
      (∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t)) := by
  constructor
  · rintro ⟨c, _, _, hA, hB⟩ t ht
    exact (common_spr_implies_segment_hurwitz ha hb hda hdb hA hB t ht).2.2
  · exact stable_segment_has_common_numerator n a b ha hb hda hdb

/-- 同一个次数恰为 n 的首一分子，对整条分母线段都满足 SPR。 -/
theorem common_spr_on_whole_segment (n : ℕ) (a b : ℝ[X])
    (ha : a.Monic) (hb : b.Monic) (hda : a.natDegree = n) (hdb : b.natDegree = n)
    (hsegment : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t)) :
    ∃ c : ℝ[X], c.Monic ∧ c.natDegree = n ∧
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → SPR c (blend a b t) := by
  obtain ⟨c, hc, hd, hA, hB⟩ :=
    stable_segment_has_common_numerator n a b ha hb hda hdb hsegment
  exact ⟨c, hc, hd, common_spr_extends_to_segment ha hb hda hdb hA hB⟩

/-- 所有线段参数和所有实频率共享同一个精确同阶、首一的分子。 -/
theorem common_spr_all_frequencies (n : ℕ) (a b : ℝ[X])
    (ha : a.Monic) (hb : b.Monic) (hda : a.natDegree = n) (hdb : b.natDegree = n)
    (hsegment : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Stable (blend a b t)) :
    ∃ c : ℝ[X], c.Monic ∧ c.natDegree = n ∧
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ ω : ℝ,
        0 < (value c (ω*Complex.I) / value (blend a b t) (ω*Complex.I)).re := by
  obtain ⟨c, hc, hd, hall⟩ :=
    common_spr_on_whole_segment n a b ha hb hda hdb hsegment
  exact ⟨c, hc, hd, fun t ht => (hall t ht).2⟩

end
end SPR.TeacherCore

#print axioms SPR.LowerNumeratorTeacher.lower_synthesis_statement
#print axioms SPR.LowerNumeratorTeacher.lower_common_spr_iff_stable_segment
#print axioms SPR.LowerNumeratorTeacher.lower_common_numerator_on_whole_segment
#print axioms SPR.LowerNumeratorTeacher.raise_then_normalize
#print axioms SPR.TeacherCore.common_spr_iff_stable_segment
#print axioms SPR.TeacherCore.common_spr_on_whole_segment
#print axioms SPR.TeacherCore.common_spr_all_frequencies
