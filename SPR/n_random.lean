import SPR.n6

/-!
# Arbitrary-order robust SPR synthesis: Yu--Wang (2003), Section 3

This file imports `SPR.n6`, which proves the sixth-order main theorem
and audits Section 2. The definitions and proofs below formalize
Section 3, record counterexamples to the printed Lemma 9, and
prove Theorem 2 for every positive order by an alternative route.

Status of the paper's Section 3 proof steps:
* Lemmas 7--10 and Theorem 2: the printed general coefficient formula and
  its affine dependence on denominator coefficients are formalized.  The
  arbitrary-order formula is also identified with a finite polynomial
  convolution, including its zero-padding convention.  For every positive
  order, the convolution is converted to the real part of the quotient of
  the paper's descending-coefficient polynomials on the imaginary axis;
  the denominator is monic when its leading coefficient is one.  Positivity
  transfers from a common numerator at the two endpoints to the whole
  stable segment.  At degree six, all four ellipse
  orientation signs, and the repaired conditional Lemma 8 are proved.
  Lemma 9 is refuted at `n=3` and at `n=6`; its claimed common-region step
  cannot be used.  The degree-independent polynomial positivity and
  common-small-δ steps underlying Lemma 10 are proved by compactness and
  leading-coefficient asymptotics, including the case where the base
  coefficient polynomial vanishes at zero.  The paper's two-coefficient
  numerator perturbation is computed in arbitrary order.  A second small
  positive leading coefficient raises the numerator to degree `n`, yielding
  a repaired conditional Lemma 10 for a common SPR numerator over the full
  stable segment.  A new pointwise construction gives a continuous complex
  common positive phase at every frequency of a stable segment, valid for
  all denominators on the segment and independent of the false
  ellipse-overlap claim.  The necessary direction of Theorem 2 is proved
  for every order using a degree-independent zero-exclusion argument.
  A degree-independent phase-avoidance criterion characterizes stable
  monic segments and yields the continuous pointwise common positive phase.
  Its equivalent dot-product/determinant form gives an algebraic
  frequency test without the paper's ellipse regions.
  Every degree-matched common SPR numerator has a positive leading
  coefficient, and its existence is exactly equivalent to simultaneous
  positivity of two explicit real coefficient polynomials.  Scaling makes
  the numerator monic, and for degree six the resulting coefficient
  feasibility condition is proved equivalent to full segment stability.
  At every positive order, the common-numerator condition is also expressed
  as nonemptiness of an open convex feasible set in `Fin n → ℝ`, with all
  frequency constraints compactified to the closed interval `[0,1]`.
  A general-order frequency-feature construction identifies common SPR
  synthesis with exclusion of the origin from a compact closed convex hull.
  Failure has an exact positive barycentric certificate using at most
  `n+2` endpoint-frequency samples, obtained by finite-dimensional
  Carathéodory reduction.  The first failure along the denominator segment
  is attained at a boundary contact and admits a sharper certificate using
  at most `n+1` samples, for every positive order.  A nonzero supporting
  vector is nonnegative on both endpoint-frequency curves and vanishes at
  each atom; every positive finite contact is a multiple root of the
  corresponding cross polynomial.  A nonzero support vector yields nonzero
  cross polynomials at Hurwitz endpoints; each has at most half its degree
  many distinct positive contacts.  Thus the set of all distinct positive
  finite contacts has at most `2*(n/2)` members; an additional shared-root
  count sharpens this bound.  If the leading support coefficient vanishes,
  the bound is at most `n-1`.  For stable
  endpoints, absence of such a critical certificate anywhere on the segment
  is equivalent to existence of a single SPR numerator for the full segment.
  A failed synthesis problem on a stable segment necessarily has an
  interior-frequency multiple contact; endpoint frequencies alone cannot
  support its critical balance.  A real-imaginary Lagrange construction
  interpolates arbitrary complex numerator values at up to `n/2` positive
  frequencies while keeping the constant value and highest coefficient
  strictly positive.  This excludes any critical certificate with at most
  half the degree many distinct positive contacts and sharpens the
  first-failure certificate accordingly.  The degree bound then forces
  positive finite contacts on both endpoint frequency curves.  The
  arbitrary-order theorem is reduced to exclusion of these high-contact
  certificates.  A sharper overlap count shows that maximal-contact
  certificates have disjoint endpoint root sets and exactly half the
  available nodes on each endpoint curve.  At full contact count,
  the atom budget permits at most one noninterior atom.  The supporting
  numerator then has no nonzero imaginary-axis zero, and at even order it
  has no imaginary-axis zero at all and is strictly positive at zero.
  Every critical support numerator has nonnegative real quotients at both
  endpoint denominators.  Saturation of the positive-root bound forces
  the nonnegative cross polynomial to be a positive scalar times a square.
  At even maximal contact both endpoint crosses have this form with the
  same leading scalar and disjoint positive root sets.  Their strict convex
  combinations are positive on the entire nonnegative frequency axis, so
  the critical support numerator is strictly positive real against every
  strictly interior denominator of the stable segment.  A zero-exclusion
  argument proves that this support numerator is Hurwitz stable itself.
  Every atom in this maximal even-order certificate lies at a strictly
  positive finite frequency; neither frequency endpoint can be an atom.
  If the atom budget uses its optional extra atom, two atoms have identical
  frequency and endpoint side, so this representation is redundant.
  At maximal contact count, the atoms on each side cover every positive
  root of that endpoint cross polynomial.  A degree-independent
  residue-interpolation identity and root-count contradiction criterion
  lead to a new algebraic exclusion of all maximal even-order critical
  certificates.  The certificate balance is decompactified into positive
  ordinary-frequency weights, then each numerator coefficient direction
  is converted into the required even and odd moment equations.  An
  arbitrary-order even/odd frequency decomposition gives a polynomial
  identity for the raised cross; Hurwitz stability makes these components
  coprime.  An optional repeated atom is merged with its identical
  frequency and endpoint side before applying the residue contradiction.
  More generally, frequency fibers are aggregated without assuming
  distinct atoms, and the first half of the even and odd moment equations
  exclude every interior-only certificate whose positive-leading support
  numerator is Hurwitz stable. Stable segments prevent the grouped
  denominator values from canceling. Endpoint contact is also impossible
  for such a support numerator. Consequently, a critical certificate with
  positive leading support coefficient must have an imaginary-axis zero;
  at maximal contact count this zero must occur at the origin.
  Weak positive-real behavior also makes the support numerator nonnegative
  on the nonnegative real axis. At odd maximal contact, the cross polynomial
  has a simple origin root, and coefficient comparison proves that the
  supporting numerator's origin root is simple with positive linear term.
  A shifted grouped-residue obstruction handles the moment equations after
  an origin factor is removed from the odd-order parity polynomial, provided
  the resulting parity pair is coprime.
  A root-product bound applied to positive stable perturbations rules out
  open right-half-plane roots of the weak supporting numerator. Removing
  its simple origin factor therefore yields a Hurwitz polynomial and the
  required coprimality; the shifted residue obstruction excludes every
  maximal odd-order critical certificate with positive leading support.
  In the maximal odd-order zero-leading case, saturated positive roots make
  the supporting numerator strictly positive at zero and exclude origin
  atoms. A fixed-degree polynomial reflection extends the stable-perturbation
   argument across the degree drop and proves that supporting numerator
   Hurwitz stable as well. A highest-coefficient identity fixes its degree at
   `n-1`; positivity on the real axis gives a positive leading coefficient.
   Infinity atoms contribute zero to every finite-coefficient balance.
   Filtering them out and applying the grouped-residue obstruction excludes
   the maximal odd-order zero-leading certificate too.
   Hence every remaining critical certificate for `n ≥ 3` has strictly more
   than `n/2` and strictly fewer than `2*(n/2)` positive finite contacts.
   If its leading support coefficient vanishes, the endpoint degree drop
   sharpens the contact bound to `2*((n-1)/2)`; at even order this is `n-2`.
   A gcd-based grouped-residue obstruction further shows that every
   remaining even-order interior certificate with positive constant and
   leading numerator terms forces a repeated common root in the parity
   gcd. Its distinct roots are positive real roots shared by the two
   endpoint cross polynomials, while the gcd degree exceeds their count.
   The origin-zero case sharpens the endpoint root budget by two,
   removing the positive-constant assumption from this repeated-root
   obstruction. A derivative reconstruction identity proves that a
   repeated parity-gcd root yields a multiple imaginary-axis zero of
   the support numerator. Thus imaginary-axis zero simplicity would
   exclude every positive-leading even-order interior certificate.
   Cayley transformation gives a unit-disk bound on the imaginary axis.
   Reflection at infinity and compactness supply a global rational
   bound. Phragmen-Lindelof then extends weak positive-realness to
   the closed right half-plane. Analytic zero factorization and a
   right-half-plane angular argument prove simplicity of imaginary-axis
   zeros of nonzero weakly positive-real numerators. A grouped-residue
   argument allowing zero-frequency atoms excludes every positive-leading
   even-order critical certificate. The degree-drop root bound proves the
   fourth-order instance of the general theorem. Reflection at infinity now proves that
   every nonzero zero-leading weakly positive-real numerator has relative
   degree exactly one. For a critical support numerator, the surviving
   degree-(n-1) coefficient is strictly positive. The degree-drop
   count now also includes overlap of endpoint contacts, and at even
   order the odd-frequency component has degree exactly `n/2-1`. A parity-swapped
   grouped-residue argument and analytic zero-factorization now exclude
   every even-order critical certificate whose atoms all have strictly
   positive finite frequencies, including zero-leading support numerators. The
   shared-root degree bound applies independently of atom locations.
   Filtering infinity atoms from the finite moments then proves that an
   even-order certificate must carry a zero-frequency atom. One extra even
   moment strengthens the grouped-residue gap by one and excludes these
   last zero-leading even certificates too. Theorem 2 is therefore proved
   for every positive even order. The same extra-moment argument,
   with parity roles swapped, excludes every positive-leading odd-order
   certificate. In the zero-leading odd-order case, the even parity
   component has exact degree `(n-1)/2`. Grouped residue moments give
   a strict gcd/contact gap. Without an origin atom this contradicts
   the degree-drop contact budget; with an origin atom, the numerator
   vanishes at zero and the endpoint root budget drops by two, giving
   the same contradiction. Thus all odd-order critical certificates
   are excluded. The first-order base case follows from the contact
   count, and the second-order base case has an explicit common
   numerator. Theorem 2 is proved for every positive order.
-/

namespace MKNumina
namespace SPR
namespace SixthOrder

noncomputable section

open Polynomial Filter Set
open scoped Topology Classical

/-- All five free coefficients of the unperturbed monic quintic used in
Section 3 of the paper.  Unlike the Section 2 construction, `q` is free. -/
structure GeneralSixCandidate where
  x : ℝ
  y : ℝ
  z : ℝ
  p : ℝ
  q : ℝ

def GeneralSixCandidate.drop (v : GeneralSixCandidate) : QuinticCandidate :=
  ⟨v.x, v.y, v.z, v.p⟩

/-- The six coefficients `c₁,...,c₆` from Section 3 for `n=6`.
Their equality with the paper's finite-sum formula is proved below. -/
def gc1 (a : MonicSextic) (v : GeneralSixCandidate) : ℝ :=
  c0 a v.drop
def gc2 (a : MonicSextic) (v : GeneralSixCandidate) : ℝ :=
  c1 a v.drop
def gc3 (a : MonicSextic) (v : GeneralSixCandidate) : ℝ :=
  c2 a v.drop - v.q
def gc4 (a : MonicSextic) (v : GeneralSixCandidate) : ℝ :=
  c3 a v.drop + a.a2 * v.q
def gc5 (a : MonicSextic) (v : GeneralSixCandidate) : ℝ :=
  c4 a v.drop - a.a4 * v.q
def gc6 (a : MonicSextic) (v : GeneralSixCandidate) : ℝ :=
  a.a6 * v.q

/-- The coefficient formula printed after Lemma 7, with signed indices so
that negative numerator subscripts have their stated value zero. -/
def paperGeneralCoefficient (n : ℕ) (a : ℕ → ℝ) (x : ℤ → ℝ)
    (l : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n+1),
    (-1 : ℝ) ^ (l+j) * a j * x (2*(l:ℤ)-(j:ℤ)-1)

def paperGeneralA6 (a : MonicSextic) : ℕ → ℝ
  | 0 => 1
  | 1 => a.a1
  | 2 => a.a2
  | 3 => a.a3
  | 4 => a.a4
  | 5 => a.a5
  | 6 => a.a6
  | _ => 0

def paperGeneralX6 (v : GeneralSixCandidate) (i : ℤ) : ℝ :=
  if i = 0 then 1 else
  if i = 1 then v.x else
  if i = 2 then v.y else
  if i = 3 then v.z else
  if i = 4 then v.p else
  if i = 5 then v.q else 0

theorem paperGeneralCoefficient_six (a : MonicSextic)
    (v : GeneralSixCandidate) :
    paperGeneralCoefficient 6 (paperGeneralA6 a) (paperGeneralX6 v) 1 = gc1 a v ∧
    paperGeneralCoefficient 6 (paperGeneralA6 a) (paperGeneralX6 v) 2 = gc2 a v ∧
    paperGeneralCoefficient 6 (paperGeneralA6 a) (paperGeneralX6 v) 3 = gc3 a v ∧
    paperGeneralCoefficient 6 (paperGeneralA6 a) (paperGeneralX6 v) 4 = gc4 a v ∧
    paperGeneralCoefficient 6 (paperGeneralA6 a) (paperGeneralX6 v) 5 = gc5 a v ∧
    paperGeneralCoefficient 6 (paperGeneralA6 a) (paperGeneralX6 v) 6 = gc6 a v := by
  unfold paperGeneralCoefficient paperGeneralA6 paperGeneralX6
    gc1 gc2 gc3 gc4 gc5 gc6 GeneralSixCandidate.drop
    c0 c1 c2 c3 c4
  norm_num [Finset.sum_range_succ]
  repeat' constructor <;> ring

theorem paperGeneralCoefficient_affine
    (n : ℕ) (a b : ℕ → ℝ) (x : ℤ → ℝ)
    (l : ℕ) (r : ℝ) :
    paperGeneralCoefficient n (fun j => (1-r)*a j+r*b j) x l =
      (1-r)*paperGeneralCoefficient n a x l +
        r*paperGeneralCoefficient n b x l := by
  unfold paperGeneralCoefficient
  calc
    (∑ j ∈ Finset.range (n+1),
      (-1 : ℝ) ^ (l+j) * ((1-r)*a j+r*b j) *
        x (2*(l:ℤ)-(j:ℤ)-1)) =
        ∑ j ∈ Finset.range (n+1),
          ((1-r)*((-1 : ℝ) ^ (l+j)*a j*
            x (2*(l:ℤ)-(j:ℤ)-1)) +
          r*((-1 : ℝ) ^ (l+j)*b j*
            x (2*(l:ℤ)-(j:ℤ)-1))) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [← Finset.mul_sum]

/-- The four `n-2` ellipse interiors in Lemma 7, specialized to `n=6`.
Each has exactly the three zero constraints printed in the paper. -/
def GeneralOmegaE1 (a : MonicSextic) (v : GeneralSixCandidate) : Prop :=
  gc2 a v ^ 2 - 4 * gc1 a v * gc3 a v < 0 ∧
    gc4 a v = 0 ∧ gc5 a v = 0 ∧ gc6 a v = 0
def GeneralOmegaE2 (a : MonicSextic) (v : GeneralSixCandidate) : Prop :=
  gc3 a v ^ 2 - 4 * gc2 a v * gc4 a v < 0 ∧
    gc1 a v = 0 ∧ gc5 a v = 0 ∧ gc6 a v = 0
def GeneralOmegaE3 (a : MonicSextic) (v : GeneralSixCandidate) : Prop :=
  gc4 a v ^ 2 - 4 * gc3 a v * gc5 a v < 0 ∧
    gc1 a v = 0 ∧ gc2 a v = 0 ∧ gc6 a v = 0
def GeneralOmegaE4 (a : MonicSextic) (v : GeneralSixCandidate) : Prop :=
  gc5 a v ^ 2 - 4 * gc4 a v * gc6 a v < 0 ∧
    gc1 a v = 0 ∧ gc2 a v = 0 ∧ gc3 a v = 0

def fullSepVal (v : GeneralSixCandidate) : ℝ :=
  sepVal v.drop - 5 * v.q

private theorem fullA1 (v : GeneralSixCandidate)
    (hv : GeneralOmegaE1 binomialSextic v) : fullSepVal v < 10 := by
  have hq : v.q = 0 := by
    have h := hv.2.2.2
    norm_num [gc6, binomialSextic] at h ⊢
    exact h
  have hold : OmegaE1 binomialSextic v.drop := by
    rcases hv with ⟨h, h4, h5, _⟩
    simpa [GeneralOmegaE1, OmegaE1, gc1, gc2, gc3, gc4, gc5, hq] using
      (show gc2 binomialSextic v ^ 2 - 4 * gc1 binomialSextic v *
        gc3 binomialSextic v < 0 ∧ gc4 binomialSextic v = 0 ∧
        gc5 binomialSextic v = 0 from ⟨h, h4, h5⟩)
  simpa [fullSepVal, hq] using sepA1 v.drop hold

private theorem fullA2 (v : GeneralSixCandidate)
    (hv : GeneralOmegaE2 binomialSextic v) : fullSepVal v < 10 := by
  have hq : v.q = 0 := by
    have h := hv.2.2.2
    norm_num [gc6, binomialSextic] at h ⊢
    exact h
  have hold : OmegaE2 binomialSextic v.drop := by
    rcases hv with ⟨h, h1, h5, _⟩
    simpa [OmegaE2, gc1, gc2, gc3, gc4, gc5, hq] using
      (show gc3 binomialSextic v ^ 2 - 4 * gc2 binomialSextic v *
        gc4 binomialSextic v < 0 ∧ gc1 binomialSextic v = 0 ∧
        gc5 binomialSextic v = 0 from ⟨h, h1, h5⟩)
  simpa [fullSepVal, hq] using sepA2 v.drop hold

private theorem fullA3 (v : GeneralSixCandidate)
    (hv : GeneralOmegaE3 binomialSextic v) : fullSepVal v < 10 := by
  have hq : v.q = 0 := by
    have h := hv.2.2.2
    norm_num [gc6, binomialSextic] at h ⊢
    exact h
  have hold : OmegaE3 binomialSextic v.drop := by
    rcases hv with ⟨h, h1, h2, _⟩
    simpa [OmegaE3, gc1, gc2, gc3, gc4, gc5, hq] using
      (show gc4 binomialSextic v ^ 2 - 4 * gc3 binomialSextic v *
        gc5 binomialSextic v < 0 ∧ gc1 binomialSextic v = 0 ∧
        gc2 binomialSextic v = 0 from ⟨h, h1, h2⟩)
  simpa [fullSepVal, hq] using sepA3 v.drop hold

private theorem fullB1 (v : GeneralSixCandidate)
    (hv : GeneralOmegaE1 gramCounterSimpleB v) : 10 < fullSepVal v := by
  have hq : v.q = 0 := by
    have h := hv.2.2.2
    norm_num [gc6, gramCounterSimpleB] at h ⊢
    exact h
  have hold : OmegaE1 gramCounterSimpleB v.drop := by
    rcases hv with ⟨h, h4, h5, _⟩
    simpa [OmegaE1, gc1, gc2, gc3, gc4, gc5, hq] using
      (show gc2 gramCounterSimpleB v ^ 2 - 4 * gc1 gramCounterSimpleB v *
        gc3 gramCounterSimpleB v < 0 ∧ gc4 gramCounterSimpleB v = 0 ∧
        gc5 gramCounterSimpleB v = 0 from ⟨h, h4, h5⟩)
  simpa [fullSepVal, hq] using sepB1 v.drop hold

private theorem fullB2 (v : GeneralSixCandidate)
    (hv : GeneralOmegaE2 gramCounterSimpleB v) : 10 < fullSepVal v := by
  have hq : v.q = 0 := by
    have h := hv.2.2.2
    norm_num [gc6, gramCounterSimpleB] at h ⊢
    exact h
  have hold : OmegaE2 gramCounterSimpleB v.drop := by
    rcases hv with ⟨h, h1, h5, _⟩
    simpa [OmegaE2, gc1, gc2, gc3, gc4, gc5, hq] using
      (show gc3 gramCounterSimpleB v ^ 2 - 4 * gc2 gramCounterSimpleB v *
        gc4 gramCounterSimpleB v < 0 ∧ gc1 gramCounterSimpleB v = 0 ∧
        gc5 gramCounterSimpleB v = 0 from ⟨h, h1, h5⟩)
  simpa [fullSepVal, hq] using sepB2 v.drop hold

private theorem fullB3 (v : GeneralSixCandidate)
    (hv : GeneralOmegaE3 gramCounterSimpleB v) : 10 < fullSepVal v := by
  have hq : v.q = 0 := by
    have h := hv.2.2.2
    norm_num [gc6, gramCounterSimpleB] at h ⊢
    exact h
  have hold : OmegaE3 gramCounterSimpleB v.drop := by
    rcases hv with ⟨h, h1, h2, _⟩
    simpa [OmegaE3, gc1, gc2, gc3, gc4, gc5, hq] using
      (show gc4 gramCounterSimpleB v ^ 2 - 4 * gc3 gramCounterSimpleB v *
        gc5 gramCounterSimpleB v < 0 ∧ gc1 gramCounterSimpleB v = 0 ∧
        gc2 gramCounterSimpleB v = 0 from ⟨h, h1, h2⟩)
  simpa [fullSepVal, hq] using sepB3 v.drop hold

private theorem fullA4 (v : GeneralSixCandidate)
    (hv : GeneralOmegaE4 binomialSextic v) : fullSepVal v < 10 := by
  rcases v with ⟨x, y, z, p, q⟩
  rcases hv with ⟨hd, h1, h2, h3⟩
  dsimp [gc1, gc2, gc3, gc4, gc5, gc6,
    c0, c1, c2, c3, c4, GeneralSixCandidate.drop,
    binomialSextic] at hd h1 h2 h3
  have hx : x = 6 := by linarith
  have hy : y = 3*p/35 - q/70 + 69/5 := by linarith
  have hz : z = 18*p/35 - 3*q/35 + 64/5 := by linarith
  rw [hx, hy, hz] at hd
  dsimp [fullSepVal, sepVal, GeneralSixCandidate.drop]
  rw [hx, hy, hz]
  nlinarith [sq_nonneg (36864*p - 68864*q - 154091),
    sq_nonneg (q - 5113/1280)]

private theorem fullB4 (v : GeneralSixCandidate)
    (hv : GeneralOmegaE4 gramCounterSimpleB v) : 10 < fullSepVal v := by
  rcases v with ⟨x, y, z, p, q⟩
  rcases hv with ⟨hd, h1, h2, h3⟩
  dsimp [gc1, gc2, gc3, gc4, gc5, gc6,
    c0, c1, c2, c3, c4, GeneralSixCandidate.drop,
    gramCounterSimpleB] at hd h1 h2 h3
  have hx : x = 4 := by linarith
  have hy : y = 2*p/23 - q/46 + 350/23 := by linarith
  have hz : z = 8*p/23 - 2*q/23 + 342/23 := by linarith
  rw [hx, hy, hz] at hd
  dsimp [fullSepVal, sepVal, GeneralSixCandidate.drop]
  rw [hx, hy, hz]
  nlinarith [sq_nonneg (93636*p - 106485*q - 607802),
    sq_nonneg (q - 19186582/1264977)]

def GeneralOmegaEllipse (a : MonicSextic) (k : Fin 4)
    (v : GeneralSixCandidate) : Prop :=
  match k.val with
  | 0 => GeneralOmegaE1 a v
  | 1 => GeneralOmegaE2 a v
  | 2 => GeneralOmegaE3 a v
  | _ => GeneralOmegaE4 a v

def fullMix (u v : GeneralSixCandidate) (r : ℝ) : GeneralSixCandidate where
  x := (1-r)*u.x+r*v.x
  y := (1-r)*u.y+r*v.y
  z := (1-r)*u.z+r*v.z
  p := (1-r)*u.p+r*v.p
  q := (1-r)*u.q+r*v.q

def FullOpenSegment (u v x : GeneralSixCandidate) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r < 1 ∧ x = fullMix u v r

/-- A generous existential reading of the union of pairwise open segments
printed before Lemma 8.  The original universal reading is a subset. -/
def GeneralOmegaIntended (a : MonicSextic) : Set GeneralSixCandidate :=
  paperPairwiseUnion 6 (fun k => {v | GeneralOmegaEllipse a k v})
    FullOpenSegment

private theorem fullSep_mix (u v : GeneralSixCandidate) (r : ℝ) :
    fullSepVal (fullMix u v r) =
      (1-r)*fullSepVal u+r*fullSepVal v := by
  unfold fullSepVal sepVal GeneralSixCandidate.drop fullMix
  ring

private theorem fullSep_open_lt
    {u v w : GeneralSixCandidate}
    (hu : fullSepVal u < 10) (hv : fullSepVal v < 10)
    (hseg : FullOpenSegment u v w) : fullSepVal w < 10 := by
  obtain ⟨r, hr0, hr1, rfl⟩ := hseg
  rw [fullSep_mix]
  have h₁ : 0 < (1-r)*(10-fullSepVal u) :=
    mul_pos (by linarith) (by linarith)
  have h₂ : 0 < r*(10-fullSepVal v) :=
    mul_pos hr0 (by linarith)
  nlinarith

private theorem fullSep_open_gt
    {u v w : GeneralSixCandidate}
    (hu : 10 < fullSepVal u) (hv : 10 < fullSepVal v)
    (hseg : FullOpenSegment u v w) : 10 < fullSepVal w := by
  obtain ⟨r, hr0, hr1, rfl⟩ := hseg
  rw [fullSep_mix]
  have h₁ : 0 < (1-r)*(fullSepVal u-10) :=
    mul_pos (by linarith) (by linarith)
  have h₂ : 0 < r*(fullSepVal v-10) :=
    mul_pos hr0 (by linarith)
  nlinarith

private theorem fullA_sep (k : Fin 4) (v : GeneralSixCandidate)
    (hv : GeneralOmegaEllipse binomialSextic k v) :
    fullSepVal v < 10 := by
  fin_cases k
  · exact fullA1 v hv
  · exact fullA2 v hv
  · exact fullA3 v hv
  · exact fullA4 v hv

private theorem fullB_sep (k : Fin 4) (v : GeneralSixCandidate)
    (hv : GeneralOmegaEllipse gramCounterSimpleB k v) :
    10 < fullSepVal v := by
  fin_cases k
  · exact fullB1 v hv
  · exact fullB2 v hv
  · exact fullB3 v hv
  · exact fullB4 v hv

private theorem fullOmegaA_sep {v : GeneralSixCandidate}
    (hv : v ∈ GeneralOmegaIntended binomialSextic) :
    fullSepVal v < 10 := by
  obtain ⟨i, j, _, A, hA, B, hB, hseg⟩ := hv
  exact fullSep_open_lt (fullA_sep i A hA) (fullA_sep j B hB) hseg

private theorem fullOmegaB_sep {v : GeneralSixCandidate}
    (hv : v ∈ GeneralOmegaIntended gramCounterSimpleB) :
    10 < fullSepVal v := by
  obtain ⟨i, j, _, A, hA, B, hB, hseg⟩ := hv
  exact fullSep_open_gt (fullB_sep i A hA) (fullB_sep j B hB) hseg

/-- The very same Hurwitz segment refutes the common-region conclusion of
Lemma 9 at `n=6`, even after giving it the generous existential reading. -/
theorem generalOmega_six_counterexample :
    Disjoint (GeneralOmegaIntended binomialSextic)
      (GeneralOmegaIntended gramCounterSimpleB) := by
  rw [Set.disjoint_left]
  intro v hA hB
  exact (not_lt_of_ge (le_of_lt (fullOmegaB_sep hB)))
    (fullOmegaA_sep hA)

/-- The `n=6` specialization of Lemma 9's claimed implication. -/
def PaperLemma9SixClaim : Prop :=
  ∀ a b : MonicSextic, a.AllConvexHurwitz b →
    (GeneralOmegaIntended a ∩ GeneralOmegaIntended b).Nonempty

theorem paperLemma9SixClaim_false : ¬ PaperLemma9SixClaim := by
  intro h
  obtain ⟨v, hv⟩ := h binomialSextic gramCounterSimpleB
    gramCounterSimple_segment_hurwitz
  exact (Set.disjoint_left.mp generalOmega_six_counterexample)
    hv.1 hv.2



/-- A continuous positive function on the nonnegative axis remains positive
after a sufficiently small positive perturbation by any continuous function
which is eventually positive. -/
theorem positive_perturbation_of_eventually_positive
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfpos : ∀ t : ℝ, 0 ≤ t → 0 < f t)
    (hgtop : ∀ᶠ t : ℝ in Filter.atTop, 0 < g t) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, 0 ≤ t → 0 < f t + δ * g t := by
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 hgtop
  let T : ℝ := max 1 R
  have hTpos : 0 < T := by
    dsimp [T]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hRT : R ≤ T := le_max_right _ _
  let K : Set ℝ := Set.Icc 0 T
  have hKcompact : IsCompact K := isCompact_Icc
  have hKnonempty : K.Nonempty := ⟨0, by
    dsimp [K]
    exact ⟨le_rfl, hTpos.le⟩⟩
  obtain ⟨t₀, ht₀, hminf⟩ :=
    hKcompact.exists_isMinOn hKnonempty hf.continuousOn
  obtain ⟨t₁, ht₁, hming⟩ :=
    hKcompact.exists_isMinOn hKnonempty hg.continuousOn
  have hminpos : 0 < f t₀ := hfpos t₀ ht₀.1
  let M : ℝ := max 1 (1 - g t₁)
  have hMpos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hMbound : 1 - g t₁ ≤ M := le_max_right _ _
  let δ : ℝ := f t₀ / (2*M)
  have hδ : 0 < δ := div_pos hminpos (mul_pos (by norm_num) hMpos)
  have hδM : δ * M = f t₀ / 2 := by
    dsimp [δ]
    field_simp [ne_of_gt hMpos]
    ring
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  by_cases htT : t ≤ T
  · have htK : t ∈ K := ⟨ht, htT⟩
    have hft : f t₀ ≤ f t := hminf htK
    have hgt : g t₁ ≤ g t := hming htK
    have hδgt : δ * g t₁ ≤ δ * g t :=
      mul_le_mul_of_nonneg_left hgt hδ.le
    have hδMbound : δ * (1 - g t₁) ≤ δ * M :=
      mul_le_mul_of_nonneg_left hMbound hδ.le
    nlinarith
  · have hTt : T < t := lt_of_not_ge htT
    have hgt : 0 < g t := hR t (lt_of_le_of_lt hRT hTt).le
    exact add_pos (hfpos t ht) (mul_pos hδ hgt)

/-- A direct polynomial form of the compactness step in the paper's
Lemma 10.  The second polynomial may be negative on a bounded interval;
its positive leading coefficient makes it positive eventually. -/
theorem polynomial_positive_perturbation
    (f g : Polynomial ℝ)
    (hfpos : ∀ t : ℝ, 0 ≤ t → 0 < f.eval t)
    (hgdeg : 0 < g.degree) (hglead : 0 ≤ g.leadingCoeff) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, 0 ≤ t →
        0 < (f + Polynomial.C δ * g).eval t := by
  have hgtend : Filter.Tendsto (fun t : ℝ => g.eval t)
      Filter.atTop Filter.atTop :=
    g.tendsto_atTop_of_leadingCoeff_nonneg hgdeg hglead
  have hgtop : ∀ᶠ t : ℝ in Filter.atTop, 0 < g.eval t :=
    hgtend.eventually (Filter.eventually_gt_atTop 0)
  obtain ⟨δ, hδ, hpos⟩ :=
    positive_perturbation_of_eventually_positive
      (fun t => f.eval t) (fun t => g.eval t)
      f.continuous g.continuous hfpos hgtop
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  simpa [Polynomial.eval_add, Polynomial.eval_mul] using hpos t ht

private theorem polynomial_perturbation_smaller
    (f g : Polynomial ℝ) {δ δ₀ : ℝ}
    (hf : ∀ t : ℝ, 0 ≤ t → 0 < f.eval t)
    (hδ₀ : 0 < δ₀)
    (hpos : ∀ t : ℝ, 0 ≤ t →
      0 < (f + Polynomial.C δ₀ * g).eval t)
    (hδ : 0 < δ) (hle : δ ≤ δ₀) :
    ∀ t : ℝ, 0 ≤ t →
      0 < (f + Polynomial.C δ * g).eval t := by
  intro t ht
  have hr0 : 0 ≤ δ / δ₀ := (div_nonneg hδ.le hδ₀.le)
  have hr1 : δ / δ₀ ≤ 1 := (div_le_one hδ₀).2 hle
  have hsum := convexCoeff_pos_of_pos (hf t ht)
    (by simpa [Polynomial.eval_add, Polynomial.eval_mul] using hpos t ht)
    hr0 hr1
  have heq : δ / δ₀ * δ₀ = δ := by
    field_simp [ne_of_gt hδ₀]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hsum ⊢
  have hid :
      δ / δ₀ * (f.eval t + δ₀ * g.eval t) +
        (1 - δ / δ₀) * f.eval t = f.eval t + δ * g.eval t := by
    linear_combination (g.eval t) * heq
  rw [hid] at hsum
  exact hsum

/-- The simultaneous polynomial perturbation in Lemma 10: one sufficiently
small positive `δ` works for both endpoint inequalities. -/
theorem polynomial_positive_perturbation_pair
    (fA fB gA gB : Polynomial ℝ)
    (hfA : ∀ t : ℝ, 0 ≤ t → 0 < fA.eval t)
    (hfB : ∀ t : ℝ, 0 ≤ t → 0 < fB.eval t)
    (hgdegA : 0 < gA.degree) (hgleadA : 0 ≤ gA.leadingCoeff)
    (hgdegB : 0 < gB.degree) (hgleadB : 0 ≤ gB.leadingCoeff) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ t : ℝ, 0 ≤ t →
        0 < (fA + Polynomial.C δ * gA).eval t) ∧
      (∀ t : ℝ, 0 ≤ t →
        0 < (fB + Polynomial.C δ * gB).eval t) := by
  obtain ⟨δA, hδA, hposA⟩ :=
    polynomial_positive_perturbation fA gA hfA hgdegA hgleadA
  obtain ⟨δB, hδB, hposB⟩ :=
    polynomial_positive_perturbation fB gB hfB hgdegB hgleadB
  let δ := min δA δB
  have hδ : 0 < δ := lt_min hδA hδB
  exact ⟨δ, hδ,
    polynomial_perturbation_smaller fA gA hfA hδA hposA hδ
      (min_le_left _ _),
    polynomial_perturbation_smaller fB gB hfB hδB hposB hδ
      (min_le_right _ _)⟩



/-- The Section 3 coefficient polynomial at degree six. -/
def generalCrossSix (a : MonicSextic)
    (v : GeneralSixCandidate) (t : ℝ) : ℝ :=
  gc1 a v * t^5 + gc2 a v * t^4 + gc3 a v * t^3 +
    gc4 a v * t^2 + gc5 a v * t + gc6 a v

theorem generalCrossSix_eq_coefficient_sum (a : MonicSextic)
    (v : GeneralSixCandidate) (t : ℝ) :
    generalCrossSix a v t =
      ∑ l ∈ Finset.range 6,
        paperGeneralCoefficient 6 (paperGeneralA6 a)
          (paperGeneralX6 v) (l+1) * t^(5-l) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    paperGeneralCoefficient_six a v
  norm_num [Finset.sum_range_succ, generalCrossSix, h1, h2,
    h3, h4, h5, h6]

theorem generalCrossSix_eq_paperF (a : MonicSextic)
    (v : GeneralSixCandidate) (t : ℝ) :
    generalCrossSix a v t =
      paperF a v.drop 0 t + v.q * a.evenPart t := by
  unfold generalCrossSix gc1 gc2 gc3 gc4 gc5 gc6
    paperF paperG paperH MonicSextic.evenPart
    c0 c1 c2 c3 c4 GeneralSixCandidate.drop
  ring

def generalSixEvalJW (v : GeneralSixCandidate) (ε ω : ℝ) : ℂ :=
  v.drop.evalJW ε ω + (v.q : ℂ)

theorem generalSix_re_div (a : MonicSextic)
    (v : GeneralSixCandidate) (ε ω : ℝ) :
    ((generalSixEvalJW v ε ω) / a.evalJW ω).re =
      (generalCrossSix a v (ω^2) +
        ε * paperH a (ω^2)) /
        Complex.normSq (a.evalJW ω) := by
  have hre : (generalSixEvalJW v ε ω).re =
      v.drop.evenPart ε (ω^2) + v.q := by
    simp [generalSixEvalJW, QuinticCandidate.evalJW_re]
  have him : (generalSixEvalJW v ε ω).im =
      ω * v.drop.oddPart (ω^2) := by
    simp [generalSixEvalJW, QuinticCandidate.evalJW_im]
  rw [complex_div_re_eq, hre, him,
    MonicSextic.evalJW_re, MonicSextic.evalJW_im]
  rw [generalCrossSix_eq_paperF]
  have hF : paperF a v.drop ε (ω^2) =
      paperF a v.drop 0 (ω^2) + ε * paperH a (ω^2) := by
    unfold paperF
    ring
  congr 1
  calc
    (v.drop.evenPart ε (ω^2) + v.q) * a.evenPart (ω^2) +
        ω * v.drop.oddPart (ω^2) *
          (ω * a.oddPart (ω^2)) =
      paperF a v.drop ε (ω^2) + v.q * a.evenPart (ω^2) := by
        rw [← paper_cross_identity]
        ring
    _ = _ := by rw [hF]; ring



/-- The four orientation signs needed for the Section 3 ellipse interiors. -/
def GeneralEllipseSigns (a : MonicSextic) : Prop :=
  (∀ v, GeneralOmegaE1 a v → 0 < gc1 a v) ∧
  (∀ v, GeneralOmegaE2 a v → 0 < gc2 a v) ∧
  (∀ v, GeneralOmegaE3 a v → 0 < gc3 a v) ∧
  (∀ v, GeneralOmegaE4 a v → 0 < gc4 a v)

private theorem quadratic_pos_of_discriminant
    {A B C t : ℝ} (hA : 0 < A)
    (hd : B^2 - 4*A*C < 0) :
    0 < A*t^2 + B*t + C := by
  have hmargin : 0 < 4*A*C - B^2 := by linarith
  have hsq := sq_nonneg (2*A*t+B)
  have hproduct : 0 < 4*A*(A*t^2+B*t+C) := by
    nlinarith
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < 4*A)).mp hproduct

private theorem quadratic_leading_pos_of_value
    {A B C t : ℝ} (hd : B^2 - 4*A*C < 0)
    (hvalue : 0 ≤ A*t^2+B*t+C) : 0 < A := by
  by_contra hn
  have hAneg : A < 0 := by
    rcases lt_or_eq_of_le (le_of_not_gt hn) with h | h
    · exact h
    · rw [h] at hd
      nlinarith [sq_nonneg B]
  have hnegative : 0 < (-A)*t^2+(-B)*t+(-C) :=
    quadratic_pos_of_discriminant (t := t) (by linarith : 0 < -A)
      (by nlinarith : (-B)^2 - 4*(-A)*(-C) < 0)
  nlinarith

theorem generalCrossSix_positive_at_even_root
    {a : MonicSextic} (ha : a.Hurwitz)
    (v : GeneralSixCandidate) :
    ∃ t : ℝ, 0 < t ∧ a.evenPart t = 0 ∧
      0 < generalCrossSix a v t := by
  obtain ⟨t, ht, he, hg⟩ := paperG_positive_at_even_root ha v.drop
  refine ⟨t, ht, he, ?_⟩
  rw [generalCrossSix_eq_paperF]
  simp [paperF, he]
  exact mul_pos ht hg

theorem generalEllipseSigns_proved
    {a : MonicSextic} (ha : a.Hurwitz) :
    GeneralEllipseSigns a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨t, ht, _, hcross⟩ :=
      generalCrossSix_positive_at_even_root ha v
    rcases hv with ⟨hd, h4, h5, h6⟩
    have hfactor : generalCrossSix a v t =
        t^3*(gc1 a v*t^2+gc2 a v*t+gc3 a v) := by
      simp [generalCrossSix,h4,h5,h6]
      ring
    rw [hfactor] at hcross
    have hvalue : 0 ≤ gc1 a v*t^2+gc2 a v*t+gc3 a v :=
      ((mul_pos_iff_of_pos_left (pow_pos ht 3)).mp hcross).le
    exact quadratic_leading_pos_of_value hd hvalue
  · intro v hv
    obtain ⟨t, ht, _, hcross⟩ :=
      generalCrossSix_positive_at_even_root ha v
    rcases hv with ⟨hd, h1, h5, h6⟩
    have hfactor : generalCrossSix a v t =
        t^2*(gc2 a v*t^2+gc3 a v*t+gc4 a v) := by
      simp [generalCrossSix,h1,h5,h6]
      ring
    rw [hfactor] at hcross
    have hvalue : 0 ≤ gc2 a v*t^2+gc3 a v*t+gc4 a v :=
      ((mul_pos_iff_of_pos_left (pow_pos ht 2)).mp hcross).le
    exact quadratic_leading_pos_of_value hd hvalue
  · intro v hv
    obtain ⟨t, ht, _, hcross⟩ :=
      generalCrossSix_positive_at_even_root ha v
    rcases hv with ⟨hd, h1, h2, h6⟩
    have hfactor : generalCrossSix a v t =
        t*(gc3 a v*t^2+gc4 a v*t+gc5 a v) := by
      simp [generalCrossSix,h1,h2,h6]
      ring
    rw [hfactor] at hcross
    have hvalue : 0 ≤ gc3 a v*t^2+gc4 a v*t+gc5 a v :=
      ((mul_pos_iff_of_pos_left ht).mp hcross).le
    exact quadratic_leading_pos_of_value hd hvalue
  · intro v hv
    obtain ⟨t, _, _, hcross⟩ :=
      generalCrossSix_positive_at_even_root ha v
    rcases hv with ⟨hd, h1, h2, h3⟩
    have hfactor : generalCrossSix a v t =
        gc4 a v*t^2+gc5 a v*t+gc6 a v := by
      simp [generalCrossSix,h1,h2,h3]
    rw [hfactor] at hcross
    exact quadratic_leading_pos_of_value hd hcross.le

private theorem generalE1_cross_pos
    (a : MonicSextic) (v : GeneralSixCandidate)
    (hv : GeneralOmegaE1 a v) (hsgn : 0 < gc1 a v)
    (t : ℝ) (ht : 0 < t) :
    0 < generalCrossSix a v t := by
  rcases hv with ⟨hd, h4, h5, h6⟩
  have hq := quadratic_pos_of_discriminant hsgn hd (t := t)
  calc
    generalCrossSix a v t =
        t^3 * (gc1 a v*t^2+gc2 a v*t+gc3 a v) := by
      simp [generalCrossSix,h4,h5,h6]
      ring
    _ > 0 := mul_pos (pow_pos ht 3) hq

private theorem generalE2_cross_pos
    (a : MonicSextic) (v : GeneralSixCandidate)
    (hv : GeneralOmegaE2 a v) (hsgn : 0 < gc2 a v)
    (t : ℝ) (ht : 0 < t) :
    0 < generalCrossSix a v t := by
  rcases hv with ⟨hd, h1, h5, h6⟩
  have hq := quadratic_pos_of_discriminant hsgn hd (t := t)
  calc
    generalCrossSix a v t =
        t^2 * (gc2 a v*t^2+gc3 a v*t+gc4 a v) := by
      simp [generalCrossSix,h1,h5,h6]
      ring
    _ > 0 := mul_pos (pow_pos ht 2) hq

private theorem generalE3_cross_pos
    (a : MonicSextic) (v : GeneralSixCandidate)
    (hv : GeneralOmegaE3 a v) (hsgn : 0 < gc3 a v)
    (t : ℝ) (ht : 0 < t) :
    0 < generalCrossSix a v t := by
  rcases hv with ⟨hd, h1, h2, h6⟩
  have hq := quadratic_pos_of_discriminant hsgn hd (t := t)
  calc
    generalCrossSix a v t =
        t * (gc3 a v*t^2+gc4 a v*t+gc5 a v) := by
      simp [generalCrossSix,h1,h2,h6]
      ring
    _ > 0 := mul_pos ht hq

private theorem generalE4_cross_pos
    (a : MonicSextic) (v : GeneralSixCandidate)
    (hv : GeneralOmegaE4 a v) (hsgn : 0 < gc4 a v)
    (t : ℝ) :
    0 < generalCrossSix a v t := by
  rcases hv with ⟨hd, h1, h2, h3⟩
  have hq := quadratic_pos_of_discriminant hsgn hd (t := t)
  calc
    generalCrossSix a v t =
        gc4 a v*t^2+gc5 a v*t+gc6 a v := by
      simp [generalCrossSix,h1,h2,h3]
    _ > 0 := hq

private theorem generalEllipse_cross_pos
    (a : MonicSextic) (hsgn : GeneralEllipseSigns a)
    (k : Fin 4) (v : GeneralSixCandidate)
    (hv : GeneralOmegaEllipse a k v)
    (t : ℝ) (ht : 0 < t) :
    0 < generalCrossSix a v t := by
  fin_cases k
  · exact generalE1_cross_pos a v hv (hsgn.1 v hv) t ht
  · exact generalE2_cross_pos a v hv (hsgn.2.1 v hv) t ht
  · exact generalE3_cross_pos a v hv (hsgn.2.2.1 v hv) t ht
  · exact generalE4_cross_pos a v hv (hsgn.2.2.2 v hv) t

theorem generalCrossSix_mix (a : MonicSextic)
    (u v : GeneralSixCandidate) (r t : ℝ) :
    generalCrossSix a (fullMix u v r) t =
      (1-r)*generalCrossSix a u t + r*generalCrossSix a v t := by
  unfold generalCrossSix gc1 gc2 gc3 gc4 gc5 gc6
    c0 c1 c2 c3 c4 GeneralSixCandidate.drop fullMix
  ring

theorem generalOmega_cross_pos_of_signs
    (a : MonicSextic) (hsgn : GeneralEllipseSigns a)
    {v : GeneralSixCandidate} (hv : v ∈ GeneralOmegaIntended a)
    (t : ℝ) (ht : 0 < t) :
    0 < generalCrossSix a v t := by
  obtain ⟨i, j, _, A, hA, B, hB, r, hr0, hr1, rfl⟩ := hv
  rw [generalCrossSix_mix]
  simpa [add_comm] using convexCoeff_pos_of_pos
    (generalEllipse_cross_pos a hsgn i A hA t ht)
    (generalEllipse_cross_pos a hsgn j B hB t ht)
    hr0.le hr1.le

theorem generalOmega_cross_pos_of_hurwitz
    {a : MonicSextic} (ha : a.Hurwitz)
    {v : GeneralSixCandidate} (hv : v ∈ GeneralOmegaIntended a)
    (t : ℝ) (ht : 0 < t) :
    0 < generalCrossSix a v t :=
  generalOmega_cross_pos_of_signs a (generalEllipseSigns_proved ha)
    hv t ht

private theorem generalEllipse_endpoint_coeff_nonneg
    (a : MonicSextic) (hsgn : GeneralEllipseSigns a)
    (k : Fin 4) (v : GeneralSixCandidate)
    (hv : GeneralOmegaEllipse a k v) :
    0 ≤ gc1 a v ∧ 0 ≤ gc6 a v := by
  fin_cases k
  · exact ⟨(hsgn.1 v hv).le, hv.2.2.2.ge⟩
  · exact ⟨hv.2.1.ge, hv.2.2.2.ge⟩
  · exact ⟨hv.2.1.ge, hv.2.2.2.ge⟩
  · refine ⟨hv.2.1.ge, ?_⟩
    have hlead := hsgn.2.2.2 v hv
    have hdisc := hv.1
    by_contra hnot
    have hnon : gc6 a v ≤ 0 := le_of_not_ge hnot
    have hmul : gc4 a v * gc6 a v ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hlead.le hnon
    nlinarith [sq_nonneg (gc5 a v)]

private theorem gc1_fullMix (a : MonicSextic)
    (u v : GeneralSixCandidate) (r : ℝ) :
    gc1 a (fullMix u v r) = (1-r)*gc1 a u+r*gc1 a v := by
  unfold gc1 c0 GeneralSixCandidate.drop fullMix
  ring

private theorem gc6_fullMix (a : MonicSextic)
    (u v : GeneralSixCandidate) (r : ℝ) :
    gc6 a (fullMix u v r) = (1-r)*gc6 a u+r*gc6 a v := by
  unfold gc6 fullMix
  ring

theorem generalOmega_endpoint_coeff_nonneg
    {a : MonicSextic} (ha : a.Hurwitz)
    {v : GeneralSixCandidate} (hv : v ∈ GeneralOmegaIntended a) :
    0 ≤ gc1 a v ∧ 0 ≤ gc6 a v := by
  obtain ⟨i, j, _, A, hA, B, hB, r, hr0, hr1, rfl⟩ := hv
  have hAs := generalEllipse_endpoint_coeff_nonneg a
    (generalEllipseSigns_proved ha) i A hA
  have hBs := generalEllipse_endpoint_coeff_nonneg a
    (generalEllipseSigns_proved ha) j B hB
  constructor
  · rw [gc1_fullMix]
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hr1.le) hAs.1)
      (mul_nonneg hr0.le hBs.1)
  · rw [gc6_fullMix]
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hr1.le) hAs.2)
      (mul_nonneg hr0.le hBs.2)

/-- Compactification `t = x/(1-x)` of the Section 3 sixth-order cross
polynomial, including both the zero and infinite frequency endpoints. -/
def compactGeneralCross (a : MonicSextic)
    (v : GeneralSixCandidate) (x : ℝ) : ℝ :=
  gc1 a v*x^5 + gc2 a v*x^4*(1-x) +
    gc3 a v*x^3*(1-x)^2 + gc4 a v*x^2*(1-x)^3 +
    gc5 a v*x*(1-x)^4 + gc6 a v*(1-x)^5

theorem compactGeneralCross_eq
    (a : MonicSextic) (v : GeneralSixCandidate)
    {x : ℝ} (hx : x ≠ 1) :
    compactGeneralCross a v x =
      (1-x)^5 * generalCrossSix a v (x/(1-x)) := by
  have hd : 1-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  unfold compactGeneralCross generalCrossSix
  field_simp [hd]
  ring

@[simp] theorem compactGeneralCross_zero
    (a : MonicSextic) (v : GeneralSixCandidate) :
    compactGeneralCross a v 0 = gc6 a v := by
  simp [compactGeneralCross]

@[simp] theorem compactGeneralCross_one
    (a : MonicSextic) (v : GeneralSixCandidate) :
    compactGeneralCross a v 1 = gc1 a v := by
  simp [compactGeneralCross]

theorem continuous_compactGeneralCross
    (a : MonicSextic) (v : GeneralSixCandidate) :
    Continuous (compactGeneralCross a v) := by
  unfold compactGeneralCross
  fun_prop

theorem compactGeneralCross_interior_pos
    {a : MonicSextic} (ha : a.Hurwitz)
    {v : GeneralSixCandidate} (hv : v ∈ GeneralOmegaIntended a)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < compactGeneralCross a v x := by
  rw [compactGeneralCross_eq a v (ne_of_lt hx1)]
  have hd : 0 < 1-x := sub_pos.mpr hx1
  exact mul_pos (pow_pos hd 5)
    (generalOmega_cross_pos_of_hurwitz ha hv (x/(1-x))
      (div_pos hx0 hd))

theorem compactGeneralCross_nonneg
    {a : MonicSextic} (ha : a.Hurwitz)
    {v : GeneralSixCandidate} (hv : v ∈ GeneralOmegaIntended a)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ compactGeneralCross a v x := by
  by_cases hx0 : x = 0
  · subst x
    simpa using (generalOmega_endpoint_coeff_nonneg ha hv).2
  by_cases hx1 : x = 1
  · subst x
    simpa using (generalOmega_endpoint_coeff_nonneg ha hv).1
  exact (compactGeneralCross_interior_pos ha hv
    (lt_of_le_of_ne hx.1 (Ne.symm hx0))
    (lt_of_le_of_ne hx.2 hx1)).le

theorem compactGeneralCross_positive_perturbation
    {a : MonicSextic} (ha : a.Hurwitz)
    {v : GeneralSixCandidate} (hv : v ∈ GeneralOmegaIntended a) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        0 < compactGeneralCross a v x +
          ε * compactPaperCorrection a x := by
  apply compact_positive_perturbation_general
    (compactGeneralCross a v) (compactPaperCorrection a)
    (continuous_compactGeneralCross a v)
    (continuous_compactPaperCorrection a)
  · intro x hx
    exact compactGeneralCross_nonneg ha hv hx
  · intro x hx hg
    have hx0 : x ≠ 0 := by
      intro heq
      subst x
      have h6 := a.a6_pos_of_hurwitz ha
      simp at hg
      exact (not_le_of_gt h6) hg
    have hx1 : x ≠ 1 := by
      intro heq
      subst x
      norm_num [compactPaperCorrection] at hg
    exact compactGeneralCross_interior_pos ha hv
      (lt_of_le_of_ne hx.1 (Ne.symm hx0))
      (lt_of_le_of_ne hx.2 hx1)

/-- The repaired six-degree instance of Lemma 8's small-`ε` argument. -/
theorem generalCrossSix_positive_for_some_epsilon
    {a : MonicSextic} (ha : a.Hurwitz)
    {v : GeneralSixCandidate} (hv : v ∈ GeneralOmegaIntended a) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, 0 ≤ t →
        0 < generalCrossSix a v t + ε * paperH a t := by
  obtain ⟨ε, hε, hpositive⟩ :=
    compactGeneralCross_positive_perturbation ha hv
  refine ⟨ε, hε, ?_⟩
  intro t ht
  have hden : 0 < 1+t := by linarith
  let x := t/(1+t)
  have hx0 : 0 ≤ x := div_nonneg ht hden.le
  have hx1 : x < 1 := (div_lt_one hden).mpr (by linarith)
  have hpos := hpositive x ⟨hx0, hx1.le⟩
  have hid : x/(1-x) = t := by
    dsimp [x]
    field_simp
  rw [compactGeneralCross_eq a v (ne_of_lt hx1),
    compactPaperCorrection_eq a (ne_of_lt hx1), hid] at hpos
  have heq :
      (1-x)^5 * generalCrossSix a v t +
        ε * ((1-x)^5 * paperH a t) =
        (1-x)^5 * (generalCrossSix a v t + ε * paperH a t) := by
    ring
  rw [heq] at hpos
  exact (mul_pos_iff_of_pos_left
    (pow_pos (sub_pos.mpr hx1) 5)).mp hpos

private theorem generalCrossSix_nonneg_on_nonnegative
    {a : MonicSextic} (ha : a.Hurwitz)
    {v : GeneralSixCandidate} (hv : v ∈ GeneralOmegaIntended a)
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ generalCrossSix a v t := by
  by_cases ht0 : t = 0
  · subst t
    simpa [generalCrossSix] using
      (generalOmega_endpoint_coeff_nonneg ha hv).2
  · exact (generalOmega_cross_pos_of_hurwitz ha hv t
      (lt_of_le_of_ne ht (Ne.symm ht0))).le

theorem generalCrossSix_positive_for_smaller_epsilon
    {a : MonicSextic} (ha : a.Hurwitz)
    {v : GeneralSixCandidate} (hv : v ∈ GeneralOmegaIntended a)
    {ε₀ ε : ℝ} (hε₀ : 0 < ε₀)
    (hpos₀ : ∀ t : ℝ, 0 ≤ t →
      0 < generalCrossSix a v t + ε₀ * paperH a t)
    (hε : 0 < ε) (hle : ε ≤ ε₀) :
    ∀ t : ℝ, 0 ≤ t →
      0 < generalCrossSix a v t + ε * paperH a t := by
  intro t ht
  have hbase := generalCrossSix_nonneg_on_nonnegative ha hv ht
  have hr0 : 0 < ε/ε₀ := div_pos hε hε₀
  have hr1 : ε/ε₀ ≤ 1 := (div_le_one hε₀).2 hle
  have hlin :
      (1-ε/ε₀)*generalCrossSix a v t +
        (ε/ε₀)*(generalCrossSix a v t+ε₀*paperH a t) =
      generalCrossSix a v t+ε*paperH a t := by
    field_simp [ne_of_gt hε₀]
    ring
  rw [←hlin]
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_nonneg.mpr hr1) hbase)
    (mul_pos hr0 (hpos₀ t ht))

/-- The `n=6` instance of Lemma 8, including one common perturbation size
for both stable denominator endpoints. -/
theorem paperLemma8_six_repaired
    {a b : MonicSextic} (ha : a.Hurwitz) (hb : b.Hurwitz)
    {v : GeneralSixCandidate}
    (hva : v ∈ GeneralOmegaIntended a)
    (hvb : v ∈ GeneralOmegaIntended b) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ ω : ℝ, 0 < ((generalSixEvalJW v ε ω) / a.evalJW ω).re) ∧
      (∀ ω : ℝ, 0 < ((generalSixEvalJW v ε ω) / b.evalJW ω).re) := by
  obtain ⟨εa, hεa, hFa⟩ :=
    generalCrossSix_positive_for_some_epsilon ha hva
  obtain ⟨εb, hεb, hFb⟩ :=
    generalCrossSix_positive_for_some_epsilon hb hvb
  let ε := min εa εb
  have hε : 0 < ε := lt_min hεa hεb
  have hFa' := generalCrossSix_positive_for_smaller_epsilon
    ha hva hεa hFa hε (min_le_left _ _)
  have hFb' := generalCrossSix_positive_for_smaller_epsilon
    hb hvb hεb hFb hε (min_le_right _ _)
  refine ⟨ε, hε, ?_, ?_⟩
  · intro ω
    rw [generalSix_re_div]
    exact div_pos (hFa' (ω^2) (sq_nonneg ω))
      (a.evalJW_normSq_pos ha ω)
  · intro ω
    rw [generalSix_re_div]
    exact div_pos (hFb' (ω^2) (sq_nonneg ω))
      (b.evalJW_normSq_pos hb ω)

/-- The Section 3 common-region hypothesis is sufficient by Lemma 8, but
the stable counterexample proves it is not necessary for common SPR synthesis. -/
theorem gramCounterSimple_commonSPR_without_generalOmega :
    binomialSextic.ExistsCommonSPR gramCounterSimpleB ∧
      Disjoint (GeneralOmegaIntended binomialSextic)
        (GeneralOmegaIntended gramCounterSimpleB) := by
  exact ⟨(sixth_order_main _ _).2 gramCounterSimple_segment_hurwitz,
    generalOmega_six_counterexample⟩



noncomputable section


def paperSignedDenominator (n : ℕ) (a : ℕ → ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (n+1),
    Polynomial.monomial j ((-1 : ℝ)^j * a j)

def paperReversedNumerator (n : ℕ) (x : ℕ → ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range n, Polynomial.monomial k (x k)

theorem paperSignedDenominator_coeff
    (n : ℕ) (a : ℕ → ℝ) (m : ℕ) :
    (paperSignedDenominator n a).coeff m =
      if m ≤ n then (-1 : ℝ)^m * a m else 0 := by
  simp [paperSignedDenominator, Polynomial.finset_sum_coeff,
    Polynomial.coeff_monomial, Finset.sum_ite_eq', Nat.lt_succ_iff]

theorem paperReversedNumerator_coeff
    (n : ℕ) (x : ℕ → ℝ) (m : ℕ) :
    (paperReversedNumerator n x).coeff m =
      if m < n then x m else 0 := by
  simp [paperReversedNumerator, Polynomial.finset_sum_coeff,
    Polynomial.coeff_monomial, Finset.sum_ite_eq']

theorem paperConvolution_coefficient
    (n l : ℕ) (hl : 0 < l) (a x : ℕ → ℝ) :
    ((paperSignedDenominator n a) *
      (paperReversedNumerator n x)).coeff (2*l-1) =
      ∑ j ∈ Finset.range (2*l),
        (if j ≤ n then (-1 : ℝ)^j*a j else 0) *
          (if 2*l-1-j < n then x (2*l-1-j) else 0) := by
  have hsucc : (2*l-1).succ = 2*l := by omega
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (paperSignedDenominator n a).coeff i *
      (paperReversedNumerator n x).coeff j) (2*l-1)]
  rw [hsucc]
  simp only [paperSignedDenominator_coeff,
    paperReversedNumerator_coeff]

def paperPaddedNumerator (n : ℕ) (x : ℕ → ℝ) (i : ℤ) : ℝ :=
  if 0 ≤ i ∧ i < n then x i.toNat else 0

private theorem paperPaddedNumerator_at_difference
    (n l j : ℕ) (x : ℕ → ℝ) (hl : 0 < l)
    (hj : j ≤ 2*l-1) :
    paperPaddedNumerator n x (2*(l:ℤ)-(j:ℤ)-1) =
      if 2*l-1-j < n then x (2*l-1-j) else 0 := by
  have hidx : 2*(l:ℤ)-(j:ℤ)-1 = ((2*l-1-j:ℕ):ℤ) := by
    omega
  rw [hidx]
  simp [paperPaddedNumerator]

private theorem paperPaddedNumerator_at_difference_of_gt
    (n l j : ℕ) (x : ℕ → ℝ) (hl : 0 < l)
    (hj : 2*l-1 < j) :
    paperPaddedNumerator n x (2*(l:ℤ)-(j:ℤ)-1) = 0 := by
  have hneg : 2*(l:ℤ)-(j:ℤ)-1 < 0 := by omega
  have hn : ¬ (0 ≤ 2*(l:ℤ)-(j:ℤ)-1 ∧
      2*(l:ℤ)-(j:ℤ)-1 < (n:ℤ)) :=
    fun h => (not_le_of_gt hneg) h.1
  change (if 0 ≤ 2*(l:ℤ)-(j:ℤ)-1 ∧
      2*(l:ℤ)-(j:ℤ)-1 < (n:ℤ) then
      x (2*(l:ℤ)-(j:ℤ)-1).toNat else 0) = 0
  exact if_neg hn

/-- The paper's signed-index formula is exactly the odd coefficient of a
finite product of reversed coefficient polynomials. -/
theorem paperGeneralCoefficient_eq_convolution
    (n l : ℕ) (hl : 0 < l) (a x : ℕ → ℝ) :
    paperGeneralCoefficient n a (paperPaddedNumerator n x) l =
      (-1 : ℝ)^l *
        ((paperSignedDenominator n a) *
          (paperReversedNumerator n x)).coeff (2*l-1) := by
  rw [paperConvolution_coefficient n l hl a x]
  unfold paperGeneralCoefficient
  rw [Finset.mul_sum]
  let m := 2*l-1
  by_cases hnm : n ≤ m
  · have hsubset : Finset.range (n+1) ⊆ Finset.range (2*l) := by
      exact Finset.range_mono (by dsimp [m] at hnm ⊢; omega)
    have htail : ∀ j ∈ Finset.range (2*l),
        j ∉ Finset.range (n+1) →
        (-1 : ℝ)^l *
          ((if j ≤ n then (-1 : ℝ)^j*a j else 0) *
            (if 2*l-1-j < n then x (2*l-1-j) else 0)) = 0 := by
      intro j _ hj
      have hjN : ¬ j ≤ n := by simpa [Nat.lt_succ_iff] using hj
      simp [hjN]
    have hs := Finset.sum_subset hsubset htail
    rw [←hs]
    apply Finset.sum_congr rfl
    intro j hj
    have hjN : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
    have hjM : j ≤ 2*l-1 := by dsimp [m] at hnm ⊢; omega
    rw [paperPaddedNumerator_at_difference n l j x hl hjM,
      if_pos hjN, pow_add]
    ring
  · have hmn : 2*l-1 ≤ n := by dsimp [m] at hnm ⊢; omega
    have hsubset : Finset.range (n+1) ⊇ Finset.range (2*l) := by
      exact Finset.range_mono (by omega)
    have htail : ∀ j ∈ Finset.range (n+1),
        j ∉ Finset.range (2*l) →
        (-1 : ℝ)^(l+j) * a j *
          paperPaddedNumerator n x (2*(l:ℤ)-(j:ℤ)-1) = 0 := by
      intro j _ hj
      have hjM : 2*l-1 < j := by simp at hj; omega
      rw [paperPaddedNumerator_at_difference_of_gt n l j x hl hjM]
      ring
    have hs := Finset.sum_subset hsubset htail
    rw [←hs]
    apply Finset.sum_congr rfl
    intro j hj
    have hjM : j ≤ 2*l-1 := by simp at hj; omega
    have hjN : j ≤ n := le_trans hjM hmn
    rw [paperPaddedNumerator_at_difference n l j x hl hjM,
      if_pos hjN, pow_add]
    ring

end


noncomputable section

theorem paperSignedDenominator_natDegree_le
    (n : ℕ) (a : ℕ → ℝ) :
    (paperSignedDenominator n a).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [paperSignedDenominator_coeff]
  simp [not_le.mpr hm]

theorem paperReversedNumerator_natDegree_le
    (n : ℕ) (hn : 0 < n) (x : ℕ → ℝ) :
    (paperReversedNumerator n x).natDegree ≤ n-1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [paperReversedNumerator_coeff]
  have hmn : ¬ m < n := by omega
  simp [hmn]

theorem paperConvolution_reflect_mul
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) :
    Polynomial.reflect (2*n-1)
      (paperSignedDenominator n a * paperReversedNumerator n x) =
    Polynomial.reflect n (paperSignedDenominator n a) *
      Polynomial.reflect (n-1) (paperReversedNumerator n x) := by
  have hN : n+(n-1) = 2*n-1 := by omega
  rw [←hN]
  exact Polynomial.reflect_mul _ _
    (paperSignedDenominator_natDegree_le n a)
    (paperReversedNumerator_natDegree_le n hn x)

theorem jw_pow_even_re (ω : ℝ) (m : ℕ) :
    ((jw ω)^(2*m)).re = (-1 : ℝ)^m * ω^(2*m) := by
  have hsq : (jw ω)^2 = ((-ω^2 : ℝ) : ℂ) := by
    rw [jw, mul_pow, Complex.I_sq]
    norm_num
  rw [pow_mul, hsq]
  calc
    (((-ω^2 : ℝ) : ℂ)^m).re = (-ω^2)^m := by
      rw [← Complex.ofReal_pow (-ω^2) m]
      simp only [Complex.ofReal_re]
    _ = (-1 : ℝ)^m * (ω^2)^m := by
      rw [neg_eq_neg_one_mul, mul_pow]
    _ = (-1 : ℝ)^m * ω^(2*m) := by rw [pow_mul]

theorem jw_pow_odd_re (ω : ℝ) (m : ℕ) :
    ((jw ω)^(2*m+1)).re = 0 := by
  rw [pow_succ, pow_mul]
  have hsq : (jw ω)^2 = ((-ω^2 : ℝ) : ℂ) := by
    rw [jw, mul_pow, Complex.I_sq]
    norm_num
  rw [hsq]
  have hreal : (((-ω^2 : ℝ) : ℂ)^m).im = 0 := by
    rw [← Complex.ofReal_pow (-ω^2) m]
    simp only [Complex.ofReal_im]
  simp only [Complex.ofReal_neg, Complex.ofReal_pow] at hreal
  rw [Complex.mul_re]
  simp [jw, hreal]

theorem sum_range_pair {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (n : ℕ) :
    (∑ k ∈ Finset.range (2*n), f k) =
      ∑ j ∈ Finset.range n, (f (2*j)+f (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (∑ k ∈ Finset.range (2*(n+1)), f k) =
            (∑ k ∈ Finset.range (2*n), f k) +
              f (2*n) + f (2*n+1) := by
          rw [show 2*(n+1) = (2*n+1)+1 by omega,
            Finset.sum_range_succ, Finset.sum_range_succ]
        _ = ∑ j ∈ Finset.range (n+1),
              (f (2*j)+f (2*j+1)) := by
          rw [Finset.sum_range_succ, ←ih]
          simp only [add_assoc]

theorem real_part_aeval_eq_even_coeff_sum
    (p : Polynomial ℝ) (n : ℕ) (ω : ℝ)
    (hp : p.natDegree < 2*n) :
    (Polynomial.aeval (jw ω) p : ℂ).re =
      ∑ j ∈ Finset.range n,
        p.coeff (2*j) * (-1 : ℝ)^j * ω^(2*j) := by
  rw [Polynomial.aeval_eq_sum_range' hp]
  rw [Complex.re_sum]
  rw [sum_range_pair]
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.smul_re, jw_pow_even_re, jw_pow_odd_re]
  ring

theorem paperReflect_natDegree_le
    (N : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ N) :
    (Polynomial.reflect N p).natDegree ≤ N := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [Polynomial.coeff_reflect,
    Polynomial.revAt_eq_self_of_lt hm]
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mp hp m hm

theorem real_part_reflect_eq_odd_coeff_sum
    (n : ℕ) (hn : 0 < n) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ 2*n-1) (ω : ℝ) :
    (Polynomial.aeval (jw ω)
      (Polynomial.reflect (2*n-1) p) : ℂ).re =
      ∑ j ∈ Finset.range n,
        p.coeff (2*n-1-2*j) * (-1 : ℝ)^j * ω^(2*j) := by
  have hdegree : (Polynomial.reflect (2*n-1) p).natDegree < 2*n := by
    have h := paperReflect_natDegree_le (2*n-1) p hp
    omega
  rw [real_part_aeval_eq_even_coeff_sum _ n ω hdegree]
  apply Finset.sum_congr rfl
  intro j hj
  have hle : 2*j ≤ 2*n-1 := by
    have hjlt := Finset.mem_range.mp hj
    omega
  rw [Polynomial.coeff_reflect, Polynomial.revAt_le hle]

theorem paperConvolution_natDegree_le
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) :
    (paperSignedDenominator n a * paperReversedNumerator n x).natDegree ≤
      2*n-1 := by
  have h := Polynomial.natDegree_mul_le_of_le
    (paperSignedDenominator_natDegree_le n a)
    (paperReversedNumerator_natDegree_le n hn x)
  omega

/-- For every order, the paper's coefficients produce the real part of the
reflected coefficient convolution at imaginary frequency. -/
theorem paperGeneralCoefficient_real_part_reflect
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) (ω : ℝ) :
    (-1 : ℝ)^n *
      (Polynomial.aeval (jw ω)
        (Polynomial.reflect (2*n-1)
          (paperSignedDenominator n a * paperReversedNumerator n x)) : ℂ).re =
      ∑ j ∈ Finset.range n,
        paperGeneralCoefficient n a (paperPaddedNumerator n x)
          (n-j) * ω^(2*j) := by
  rw [real_part_reflect_eq_odd_coeff_sum n hn _
    (paperConvolution_natDegree_le n hn a x) ω]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < n := Finset.mem_range.mp hj
  have hlj : 0 < n-j := by omega
  have hidx : 2*n-1-2*j = 2*(n-j)-1 := by omega
  have hsign : (-1 : ℝ)^n * (-1)^j = (-1)^(n-j) := by
    rw [←pow_add]
    have heq : n+j = (n-j)+2*j := by omega
    rw [heq, pow_add, pow_mul]
    norm_num
  have hcoeff := paperGeneralCoefficient_eq_convolution
    n (n-j) hlj a x
  rw [hidx]
  rw [hcoeff]
  rw [←hsign]
  ring


open ComplexConjugate


def paperGenericDenominator (n : ℕ) (a : ℕ → ℝ) : Polynomial ℝ :=
  Polynomial.C ((-1 : ℝ)^n) *
    (Polynomial.reflect n (paperSignedDenominator n a)).comp (-Polynomial.X)

def paperGenericNumerator (n : ℕ) (x : ℕ → ℝ) : Polynomial ℝ :=
  Polynomial.reflect (n-1) (paperReversedNumerator n x)

theorem paperGenericDenominator_conj_eval
    (n : ℕ) (a : ℕ → ℝ) (ω : ℝ) :
    conj (Polynomial.aeval (jw ω) (paperGenericDenominator n a) : ℂ) =
      ((-1 : ℝ)^n : ℂ) *
        Polynomial.aeval (jw ω)
          (Polynomial.reflect n (paperSignedDenominator n a)) := by
  rw [←Polynomial.aeval_conj]
  simp only [paperGenericDenominator, Polynomial.aeval_mul,
    Polynomial.aeval_C, Polynomial.aeval_comp,
    Polynomial.aeval_X]
  have hc : conj (jw ω) = -(jw ω) := by
    simp [jw]
  rw [hc]
  simp

theorem paperGeneric_cross_identity
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) (ω : ℝ) :
    ((Polynomial.aeval (jw ω) (paperGenericNumerator n x) : ℂ) *
      conj
        (Polynomial.aeval (jw ω) (paperGenericDenominator n a) : ℂ)).re =
      ∑ j ∈ Finset.range n,
        paperGeneralCoefficient n a (paperPaddedNumerator n x)
          (n-j) * ω^(2*j) := by
  rw [paperGenericDenominator_conj_eval]
  rw [show (Polynomial.aeval (jw ω) (paperGenericNumerator n x) : ℂ) *
        (((-1 : ℝ)^n : ℂ) *
          Polynomial.aeval (jw ω)
            (Polynomial.reflect n (paperSignedDenominator n a))) =
      ((-1 : ℝ)^n : ℂ) *
        Polynomial.aeval (jw ω)
          (Polynomial.reflect (2*n-1)
            (paperSignedDenominator n a * paperReversedNumerator n x)) by
      rw [paperConvolution_reflect_mul n hn a x]
      simp [paperGenericNumerator, Polynomial.aeval_mul]
      ring]
  rw [Complex.mul_re]
  rw [←Complex.ofReal_pow]
  simpa only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    using paperGeneralCoefficient_real_part_reflect n hn a x ω

/-- The arbitrary-order frequency numerator is exactly the paper's coefficient
sum, even at a zero of the denominator (using Lean's total division). -/
theorem paperGeneric_div_re_eq_coefficient_sum
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) (ω : ℝ) :
    ((Polynomial.aeval (jw ω) (paperGenericNumerator n x) : ℂ) /
      Polynomial.aeval (jw ω) (paperGenericDenominator n a)).re =
    (∑ j ∈ Finset.range n,
      paperGeneralCoefficient n a (paperPaddedNumerator n x)
        (n-j) * ω^(2*j)) /
      Complex.normSq
        (Polynomial.aeval (jw ω) (paperGenericDenominator n a) : ℂ) := by
  let z : ℂ := Polynomial.aeval (jw ω) (paperGenericNumerator n x)
  let w : ℂ := Polynomial.aeval (jw ω) (paperGenericDenominator n a)
  have hcross : (z * conj w).re =
      ∑ j ∈ Finset.range n,
        paperGeneralCoefficient n a (paperPaddedNumerator n x)
          (n-j) * ω^(2*j) :=
    paperGeneric_cross_identity n hn a x ω
  change (z / w).re = _ / Complex.normSq w
  rw [←hcross, complex_div_re_eq, Complex.mul_re]
  simp only [Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add]

theorem paperGeneric_div_re_eq_polynomial
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) (ω : ℝ) :
    ((Polynomial.aeval (jw ω) (paperGenericNumerator n x) : ℂ) /
      Polynomial.aeval (jw ω) (paperGenericDenominator n a)).re =
    (∑ j ∈ Finset.range n,
      paperGeneralCoefficient n a (paperPaddedNumerator n x)
        (n-j) * (ω^2)^j) /
      Complex.normSq
        (Polynomial.aeval (jw ω) (paperGenericDenominator n a) : ℂ) := by
  rw [paperGeneric_div_re_eq_coefficient_sum n hn a x ω]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_mul]



theorem paperGenericNumerator_coeff
    (n : ℕ) (hn : 0 < n) (x : ℕ → ℝ) (m : ℕ) (hm : m < n) :
    (paperGenericNumerator n x).coeff m = x (n-1-m) := by
  have hle : m ≤ n-1 := by omega
  rw [paperGenericNumerator, Polynomial.coeff_reflect,
    Polynomial.revAt_le hle, paperReversedNumerator_coeff]
  rw [if_pos (show n-1-m < n by omega)]

theorem paperGenericNumerator_natDegree_le
    (n : ℕ) (hn : 0 < n) (x : ℕ → ℝ) :
    (paperGenericNumerator n x).natDegree ≤ n-1 := by
  exact paperReflect_natDegree_le (n-1) _
    (paperReversedNumerator_natDegree_le n hn x)

theorem paperCoeff_comp_neg_X (p : Polynomial ℝ) (m : ℕ) :
    (p.comp (-Polynomial.X)).coeff m =
      (-1 : ℝ)^m * p.coeff m := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.add_comp, Polynomial.coeff_add, hp, hq]
      ring
  | monomial k r =>
      rw [Polynomial.monomial_comp]
      have hpow : (-Polynomial.X : Polynomial ℝ)^k =
          Polynomial.C ((-1 : ℝ)^k) * Polynomial.X^k := by
        rw [neg_eq_neg_one_mul, mul_pow]
        congr 1
        simpa using (Polynomial.C_pow (-1 : ℝ) k).symm
      rw [hpow, ←mul_assoc, ←Polynomial.C_mul,
        Polynomial.C_mul_X_pow_eq_monomial]
      simp only [Polynomial.coeff_monomial]
      split_ifs with h
      · subst m
        ring
      · simp

theorem paperGenericDenominator_coeff
    (n : ℕ) (a : ℕ → ℝ) (m : ℕ) :
    (paperGenericDenominator n a).coeff m =
      if m ≤ n then a (n-m) else 0 := by
  rw [paperGenericDenominator, Polynomial.coeff_C_mul,
    paperCoeff_comp_neg_X, Polynomial.coeff_reflect]
  by_cases hm : m ≤ n
  · rw [if_pos hm, Polynomial.revAt_le hm,
      paperSignedDenominator_coeff, if_pos (show n-m ≤ n by omega)]
    have hsign : (-1 : ℝ)^n * (-1)^m * (-1)^(n-m) = 1 := by
      rw [←pow_add, ←pow_add]
      have hpow : n+m+(n-m) = 2*n := by omega
      rw [hpow, pow_mul]
      norm_num
    calc
      _ = ((-1 : ℝ)^n * (-1)^m * (-1)^(n-m)) * a (n-m) := by ring
      _ = a (n-m) := by rw [hsign, one_mul]
  · rw [if_neg hm,
      Polynomial.revAt_eq_self_of_lt (show n < m by omega),
      paperSignedDenominator_coeff, if_neg (by omega : ¬ m ≤ n)]
    simp

theorem paperGenericNumerator_coeff_all
    (n : ℕ) (hn : 0 < n) (x : ℕ → ℝ) (m : ℕ) :
    (paperGenericNumerator n x).coeff m =
      if m < n then x (n-1-m) else 0 := by
  by_cases hm : m < n
  · rw [if_pos hm, paperGenericNumerator_coeff n hn x m hm]
  · rw [if_neg hm, paperGenericNumerator,
      Polynomial.coeff_reflect,
      Polynomial.revAt_eq_self_of_lt (show n-1 < m by omega),
      paperReversedNumerator_coeff, if_neg hm]

def paperDescendingDenominator (n : ℕ) (a : ℕ → ℝ) : Polynomial ℝ :=
  ∑ m ∈ Finset.range (n+1),
    Polynomial.monomial m (a (n-m))

def paperDescendingNumerator (n : ℕ) (x : ℕ → ℝ) : Polynomial ℝ :=
  ∑ m ∈ Finset.range n,
    Polynomial.monomial m (x (n-1-m))

theorem paperDescendingDenominator_coeff
    (n : ℕ) (a : ℕ → ℝ) (m : ℕ) :
    (paperDescendingDenominator n a).coeff m =
      if m ≤ n then a (n-m) else 0 := by
  simp [paperDescendingDenominator, Polynomial.finset_sum_coeff,
    Polynomial.coeff_monomial, Finset.sum_ite_eq', Nat.lt_succ_iff]

theorem paperDescendingNumerator_coeff
    (n : ℕ) (x : ℕ → ℝ) (m : ℕ) :
    (paperDescendingNumerator n x).coeff m =
      if m < n then x (n-1-m) else 0 := by
  simp [paperDescendingNumerator, Polynomial.finset_sum_coeff,
    Polynomial.coeff_monomial, Finset.sum_ite_eq']

theorem paperGenericDenominator_eq_descending
    (n : ℕ) (a : ℕ → ℝ) :
    paperGenericDenominator n a = paperDescendingDenominator n a := by
  ext m
  rw [paperGenericDenominator_coeff, paperDescendingDenominator_coeff]

theorem paperGenericNumerator_eq_descending
    (n : ℕ) (hn : 0 < n) (x : ℕ → ℝ) :
    paperGenericNumerator n x = paperDescendingNumerator n x := by
  ext m
  rw [paperGenericNumerator_coeff_all n hn,
    paperDescendingNumerator_coeff]

theorem paperDescendingDenominator_monic
    (n : ℕ) (a : ℕ → ℝ) (ha : a 0 = 1) :
    (paperDescendingDenominator n a).Monic := by
  have hdegree : (paperDescendingDenominator n a).natDegree ≤ n := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    rw [paperDescendingDenominator_coeff, if_neg (not_le.mpr hm)]
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one n hdegree
  rw [paperDescendingDenominator_coeff, if_pos le_rfl, Nat.sub_self, ha]

theorem paperDescending_div_re_eq_polynomial
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) (ω : ℝ) :
    ((Polynomial.aeval (jw ω) (paperDescendingNumerator n x) : ℂ) /
      Polynomial.aeval (jw ω) (paperDescendingDenominator n a)).re =
    (∑ j ∈ Finset.range n,
      paperGeneralCoefficient n a (paperPaddedNumerator n x)
        (n-j) * (ω^2)^j) /
      Complex.normSq
        (Polynomial.aeval (jw ω) (paperDescendingDenominator n a) : ℂ) := by
  rw [←paperGenericDenominator_eq_descending,
    ←paperGenericNumerator_eq_descending n hn]
  exact paperGeneric_div_re_eq_polynomial n hn a x ω

theorem paperGeneralCross_affine
    (n : ℕ) (a b x : ℕ → ℝ) (r t : ℝ) :
    (∑ j ∈ Finset.range n,
      paperGeneralCoefficient n
        (fun i => (1-r)*a i+r*b i)
        (paperPaddedNumerator n x) (n-j) * t^j) =
      (1-r) * (∑ j ∈ Finset.range n,
        paperGeneralCoefficient n a (paperPaddedNumerator n x)
          (n-j) * t^j) +
      r * (∑ j ∈ Finset.range n,
        paperGeneralCoefficient n b (paperPaddedNumerator n x)
          (n-j) * t^j) := by
  rw [Finset.mul_sum, Finset.mul_sum, ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [paperGeneralCoefficient_affine]
  ring

theorem paperDescending_segment_positive_real_of_common_cross
    (n : ℕ) (hn : 0 < n) (a b x : ℕ → ℝ)
    (hden : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ ω : ℝ,
      Polynomial.aeval (jw ω)
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i)) ≠ (0 : ℂ))
    (ha : ∀ t : ℝ, 0 ≤ t →
      0 < ∑ j ∈ Finset.range n,
        paperGeneralCoefficient n a (paperPaddedNumerator n x)
          (n-j) * t^j)
    (hb : ∀ t : ℝ, 0 ≤ t →
      0 < ∑ j ∈ Finset.range n,
        paperGeneralCoefficient n b (paperPaddedNumerator n x)
          (n-j) * t^j) :
    ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ ω : ℝ,
      0 < ((Polynomial.aeval (jw ω)
          (paperDescendingNumerator n x) : ℂ) /
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n
            (fun i => (1-r)*a i+r*b i))).re := by
  intro r hr0 hr1 ω
  rw [paperDescending_div_re_eq_polynomial n hn]
  apply div_pos _ (Complex.normSq_pos.mpr (hden r hr0 hr1 ω))
  rw [paperGeneralCross_affine]
  by_cases hrz : r = 0
  · simpa [hrz] using ha (ω^2) (sq_nonneg ω)
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrz)
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr hr1)
        (le_of_lt (ha (ω^2) (sq_nonneg ω))))
      (mul_pos hrpos (hb (ω^2) (sq_nonneg ω)))

/-- Positivity of the paper's coefficient polynomial gives a positive
imaginary-axis real part when the denominator has no imaginary-axis zero. -/
theorem paperGeneric_positive_real_of_coefficient_sum_pos
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ)
    (hden : ∀ ω : ℝ,
      Polynomial.aeval (jw ω) (paperGenericDenominator n a) ≠ (0 : ℂ))
    (hcross : ∀ t : ℝ, 0 ≤ t →
      0 < ∑ j ∈ Finset.range n,
        paperGeneralCoefficient n a (paperPaddedNumerator n x)
          (n-j) * t^j) :
    ∀ ω : ℝ,
      0 < ((Polynomial.aeval (jw ω) (paperGenericNumerator n x) : ℂ) /
        Polynomial.aeval (jw ω) (paperGenericDenominator n a)).re := by
  intro ω
  rw [paperGeneric_div_re_eq_polynomial n hn a x ω]
  exact div_pos (hcross (ω^2) (sq_nonneg ω))
    (Complex.normSq_pos.mpr (hden ω))



/-- Under imaginary-axis zero exclusion, the paper's coefficient polynomial is
positive on the nonnegative half-line exactly when the quotient has positive
real part at every imaginary frequency. -/
theorem paperDescending_quotient_pos_iff_cross_pos
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ)
    (hden : ∀ ω : ℝ,
      Polynomial.aeval (jw ω) (paperDescendingDenominator n a) ≠ (0 : ℂ)) :
    (∀ ω : ℝ,
      0 < ((Polynomial.aeval (jw ω)
          (paperDescendingNumerator n x) : ℂ) /
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n a)).re) ↔
    (∀ t : ℝ, 0 ≤ t →
      0 < ∑ j ∈ Finset.range n,
        paperGeneralCoefficient n a (paperPaddedNumerator n x)
          (n-j) * t^j) := by
  constructor
  · intro h t ht
    have hw := h (Real.sqrt t)
    rw [paperDescending_div_re_eq_polynomial n hn a x,
      Real.sq_sqrt ht] at hw
    exact (div_pos_iff_of_pos_right
      (Complex.normSq_pos.mpr (hden (Real.sqrt t)))).mp hw
  · intro h ω
    rw [paperDescending_div_re_eq_polynomial n hn a x ω]
    exact div_pos (h (ω^2) (sq_nonneg ω))
      (Complex.normSq_pos.mpr (hden ω))



/-- The endpoint-sensitive compactness step needed when the unperturbed
coefficient polynomial vanishes at zero. -/
theorem positive_perturbation_of_positive_open_halfline
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    (hfpos : ∀ t : ℝ, 0 < t → 0 < f t)
    (hgzero : 0 < g 0)
    (hgtop : ∀ᶠ t : ℝ in Filter.atTop, 0 < g t) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, 0 ≤ t → 0 < f t + δ * g t := by
  have hnear : g ⁻¹' Set.Ioi 0 ∈ nhds (0 : ℝ) :=
    hg.continuousAt (isOpen_Ioi.mem_nhds hgzero)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let η : ℝ := min 1 (ρ / 2)
  have hη : 0 < η := lt_min (by norm_num)
    (div_pos hρ (by norm_num))
  have hηρ : η < ρ :=
    lt_of_le_of_lt (min_le_right _ _) (half_lt_self hρ)
  have hgnear : ∀ t : ℝ, 0 ≤ t → t ≤ η → 0 < g t := by
    intro t ht htη
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_of_nonneg ht]
    exact lt_of_le_of_lt htη hηρ
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 hgtop
  let T : ℝ := max (η+1) R
  have hηT : η ≤ T := by
    dsimp [T]
    linarith [le_max_left (η+1) R]
  have hRT : R ≤ T := le_max_right _ _
  let K : Set ℝ := Set.Icc η T
  have hKcompact : IsCompact K := isCompact_Icc
  have hKnonempty : K.Nonempty := ⟨η, ⟨le_rfl, hηT⟩⟩
  obtain ⟨t₀, ht₀, hminf⟩ :=
    hKcompact.exists_isMinOn hKnonempty hf.continuousOn
  obtain ⟨t₁, ht₁, hming⟩ :=
    hKcompact.exists_isMinOn hKnonempty hg.continuousOn
  have hminpos : 0 < f t₀ := hfpos t₀ (lt_of_lt_of_le hη ht₀.1)
  let M : ℝ := max 1 (1 - g t₁)
  have hMpos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hMbound : 1 - g t₁ ≤ M := le_max_right _ _
  let δ : ℝ := f t₀ / (2*M)
  have hδ : 0 < δ := div_pos hminpos (mul_pos (by norm_num) hMpos)
  have hδM : δ * M = f t₀ / 2 := by
    dsimp [δ]
    field_simp [ne_of_gt hMpos]
    ring
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  by_cases htη : t ≤ η
  · exact add_pos_of_nonneg_of_pos (hfnonneg t ht)
      (mul_pos hδ (hgnear t ht htη))
  by_cases htT : t ≤ T
  · have htK : t ∈ K := ⟨le_of_lt (lt_of_not_ge htη), htT⟩
    have hft : f t₀ ≤ f t := hminf htK
    have hgt : g t₁ ≤ g t := hming htK
    have hδgt : δ * g t₁ ≤ δ * g t :=
      mul_le_mul_of_nonneg_left hgt hδ.le
    have hδMbound : δ * (1 - g t₁) ≤ δ * M :=
      mul_le_mul_of_nonneg_left hMbound hδ.le
    nlinarith
  · have hTt : T < t := lt_of_not_ge htT
    have hgt : 0 < g t := hR t (lt_of_le_of_lt hRT hTt).le
    have htt : 0 < t := lt_trans (lt_of_lt_of_le hη hηT) hTt
    exact add_pos (hfpos t htt)
      (mul_pos hδ hgt)

private theorem positive_perturbation_smaller_of_nonneg
    (f g : ℝ → ℝ)
    (hfnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    {δ₀ δ : ℝ} (hδ₀ : 0 < δ₀)
    (hpositive : ∀ t : ℝ, 0 ≤ t → 0 < f t + δ₀ * g t)
    (hδ : 0 < δ) (hle : δ ≤ δ₀) :
    ∀ t : ℝ, 0 ≤ t → 0 < f t + δ * g t := by
  intro t ht
  have hr0 : 0 < δ / δ₀ := div_pos hδ hδ₀
  have hr1 : δ / δ₀ ≤ 1 := (div_le_one hδ₀).2 hle
  have hlin :
      (1 - δ / δ₀) * f t +
        (δ / δ₀) * (f t + δ₀ * g t) = f t + δ * g t := by
    field_simp [ne_of_gt hδ₀]
    ring
  rw [←hlin]
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_nonneg.mpr hr1) (hfnonneg t ht))
    (mul_pos hr0 (hpositive t ht))

/-- A common positive perturbation size for the two endpoint coefficient
polynomials, allowing each base polynomial to vanish at zero. -/
theorem positive_perturbation_pair_of_positive_open_halfline
    (fA fB gA gB : ℝ → ℝ)
    (hfA : Continuous fA) (hfB : Continuous fB)
    (hgA : Continuous gA) (hgB : Continuous gB)
    (hfAnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ fA t)
    (hfBnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ fB t)
    (hfApos : ∀ t : ℝ, 0 < t → 0 < fA t)
    (hfBpos : ∀ t : ℝ, 0 < t → 0 < fB t)
    (hgAzero : 0 < gA 0) (hgBzero : 0 < gB 0)
    (hgAtop : ∀ᶠ t : ℝ in Filter.atTop, 0 < gA t)
    (hgBtop : ∀ᶠ t : ℝ in Filter.atTop, 0 < gB t) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ t : ℝ, 0 ≤ t → 0 < fA t + δ * gA t) ∧
      (∀ t : ℝ, 0 ≤ t → 0 < fB t + δ * gB t) := by
  obtain ⟨δA, hδA, hA⟩ :=
    positive_perturbation_of_positive_open_halfline
      fA gA hfA hgA hfAnonneg hfApos hgAzero hgAtop
  obtain ⟨δB, hδB, hB⟩ :=
    positive_perturbation_of_positive_open_halfline
      fB gB hfB hgB hfBnonneg hfBpos hgBzero hgBtop
  let δ := min δA δB
  have hδ : 0 < δ := lt_min hδA hδB
  exact ⟨δ, hδ,
    positive_perturbation_smaller_of_nonneg fA gA hfAnonneg
      hδA hA hδ (min_le_left _ _),
    positive_perturbation_smaller_of_nonneg fB gB hfBnonneg
      hδB hB hδ (min_le_right _ _)⟩

/-- Polynomial version of the paired endpoint perturbation, with the exact
zero-at-the-origin allowance used in Lemma 10. -/
theorem polynomial_positive_perturbation_pair_at_zero
    (fA fB gA gB : Polynomial ℝ)
    (hfAnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ fA.eval t)
    (hfBnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ fB.eval t)
    (hfApos : ∀ t : ℝ, 0 < t → 0 < fA.eval t)
    (hfBpos : ∀ t : ℝ, 0 < t → 0 < fB.eval t)
    (hgAzero : 0 < gA.eval 0) (hgBzero : 0 < gB.eval 0)
    (hgAdeg : 0 < gA.degree) (hgAlead : 0 ≤ gA.leadingCoeff)
    (hgBdeg : 0 < gB.degree) (hgBlead : 0 ≤ gB.leadingCoeff) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ t : ℝ, 0 ≤ t →
        0 < (fA + Polynomial.C δ * gA).eval t) ∧
      (∀ t : ℝ, 0 ≤ t →
        0 < (fB + Polynomial.C δ * gB).eval t) := by
  have hAtend : Filter.Tendsto (fun t : ℝ => gA.eval t)
      Filter.atTop Filter.atTop :=
    gA.tendsto_atTop_of_leadingCoeff_nonneg hgAdeg hgAlead
  have hBtend : Filter.Tendsto (fun t : ℝ => gB.eval t)
      Filter.atTop Filter.atTop :=
    gB.tendsto_atTop_of_leadingCoeff_nonneg hgBdeg hgBlead
  have hAtop : ∀ᶠ t : ℝ in Filter.atTop, 0 < gA.eval t :=
    hAtend.eventually (Filter.eventually_gt_atTop 0)
  have hBtop : ∀ᶠ t : ℝ in Filter.atTop, 0 < gB.eval t :=
    hBtend.eventually (Filter.eventually_gt_atTop 0)
  obtain ⟨δ, hδ, hA, hB⟩ :=
    positive_perturbation_pair_of_positive_open_halfline
      (fun t => fA.eval t) (fun t => fB.eval t)
      (fun t => gA.eval t) (fun t => gB.eval t)
      fA.continuous fB.continuous gA.continuous gB.continuous
      hfAnonneg hfBnonneg hfApos hfBpos
      hgAzero hgBzero hAtop hBtop
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro t ht
    simpa [Polynomial.eval_add, Polynomial.eval_mul] using hA t ht
  · intro t ht
    simpa [Polynomial.eval_add, Polynomial.eval_mul] using hB t ht



/-- The coefficient change from lowering the second leading numerator
coefficient and raising its constant coefficient. -/
def paperPerturbationDirection (n i : ℕ) : ℝ :=
  (if i = n-1 then 1 else 0) - (if i = 1 then 1 else 0)

theorem paperPerturbationDirection_zero
    (n : ℕ) (hn : 3 ≤ n) :
    paperPerturbationDirection n 0 = 0 := by
  simp [paperPerturbationDirection, show 0 ≠ n-1 by omega]

theorem paperPerturbationDirection_one
    (n : ℕ) (hn : 3 ≤ n) :
    paperPerturbationDirection n 1 = -1 := by
  simp [paperPerturbationDirection, show 1 ≠ n-1 by omega]

theorem paperPerturbationDirection_last
    (n : ℕ) (hn : 3 ≤ n) :
    paperPerturbationDirection n (n-1) = 1 := by
  simp [paperPerturbationDirection, show n-1 ≠ 1 by omega]

theorem paperGeneralCoefficient_direction_first
    (n : ℕ) (hn : 3 ≤ n) (a : ℕ → ℝ) :
    paperGeneralCoefficient n a
      (paperPaddedNumerator n (paperPerturbationDirection n)) 1 = a 0 := by
  unfold paperGeneralCoefficient
  rw [Finset.sum_eq_single_of_mem 0 (by simp)]
  · have hp : paperPaddedNumerator n (paperPerturbationDirection n) 1 = -1 := by
      simp [paperPaddedNumerator, paperPerturbationDirection_one n hn,
        show 1 < n by omega]
    norm_num [hp]
  · intro j hj hne
    have hjpos : 0 < j := Nat.pos_of_ne_zero hne
    by_cases hjone : j = 1
    · subst j
      simp [paperPaddedNumerator, paperPerturbationDirection_zero n hn]
    · have hjtwo : 2 ≤ j := by omega
      have hpad : paperPaddedNumerator n
          (paperPerturbationDirection n) (2*(1:ℤ)-(j:ℤ)-1) = 0 := by
        unfold paperPaddedNumerator
        rw [if_neg]
        intro h
        omega
      norm_num at hpad
      simp [hpad]

theorem paperGeneralCoefficient_direction_last
    (n : ℕ) (hn : 3 ≤ n) (a : ℕ → ℝ) :
    paperGeneralCoefficient n a
      (paperPaddedNumerator n (paperPerturbationDirection n)) n = a n := by
  unfold paperGeneralCoefficient
  rw [Finset.sum_eq_single_of_mem n (by simp)]
  · have hp : paperPaddedNumerator n
        (paperPerturbationDirection n) (n-1:ℕ) = 1 := by
      simp [paperPaddedNumerator, paperPerturbationDirection_last n hn,
        show n-1 < n by omega]
    have hidx : 2*(n:ℤ)-(n:ℤ)-1 = (n-1:ℕ) := by omega
    rw [hidx, hp]
    rw [show n+n = 2*n by omega, pow_mul]
    norm_num
  · intro j hj hne
    have hjlt : j < n := by
      have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      omega
    have hout : ¬ (2*(n:ℤ)-(j:ℤ)-1 < n) := by omega
    simp [paperPaddedNumerator, hout]

def paperGeneralCrossPolynomial
    (n : ℕ) (a x : ℕ → ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range n,
    Polynomial.monomial j
      (paperGeneralCoefficient n a (paperPaddedNumerator n x) (n-j))

theorem paperGeneralCrossPolynomial_coeff
    (n : ℕ) (a x : ℕ → ℝ) (j : ℕ) :
    (paperGeneralCrossPolynomial n a x).coeff j =
      if j < n then
        paperGeneralCoefficient n a (paperPaddedNumerator n x) (n-j)
      else 0 := by
  simp [paperGeneralCrossPolynomial, Polynomial.finset_sum_coeff,
    Polynomial.coeff_monomial, Finset.sum_ite_eq']

theorem paperGeneralCrossPolynomial_eval
    (n : ℕ) (a x : ℕ → ℝ) (t : ℝ) :
    (paperGeneralCrossPolynomial n a x).eval t =
      ∑ j ∈ Finset.range n,
        paperGeneralCoefficient n a (paperPaddedNumerator n x)
          (n-j) * t^j := by
  simp [paperGeneralCrossPolynomial, Polynomial.eval_finset_sum,
    Polynomial.eval_monomial]

theorem paperGeneralCrossPolynomial_natDegree_le
    (n : ℕ) (a x : ℕ → ℝ) :
    (paperGeneralCrossPolynomial n a x).natDegree ≤ n-1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [paperGeneralCrossPolynomial_coeff, if_neg (by omega : ¬ j < n)]

theorem paperGeneralCrossPolynomial_direction_monic
    (n : ℕ) (hn : 3 ≤ n) (a : ℕ → ℝ) (ha : a 0 = 1) :
    (paperGeneralCrossPolynomial n a
      (paperPerturbationDirection n)).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one (n-1)
    (paperGeneralCrossPolynomial_natDegree_le n a _)
  rw [paperGeneralCrossPolynomial_coeff, if_pos (by omega : n-1 < n)]
  have hidx : n-(n-1) = 1 := by omega
  rw [hidx, paperGeneralCoefficient_direction_first n hn a, ha]

theorem paperGeneralCrossPolynomial_direction_degree_pos
    (n : ℕ) (hn : 3 ≤ n) (a : ℕ → ℝ) (ha : a 0 = 1) :
    0 < (paperGeneralCrossPolynomial n a
      (paperPerturbationDirection n)).degree := by
  have hcoeff :
      (paperGeneralCrossPolynomial n a
        (paperPerturbationDirection n)).coeff (n-1) = 1 := by
    rw [paperGeneralCrossPolynomial_coeff, if_pos (by omega : n-1 < n)]
    have hidx : n-(n-1) = 1 := by omega
    rw [hidx, paperGeneralCoefficient_direction_first n hn a, ha]
  have hnat := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (paperGeneralCrossPolynomial_natDegree_le n a
      (paperPerturbationDirection n))
    (by rw [hcoeff]; norm_num)
  apply Polynomial.natDegree_pos_iff_degree_pos.mp
  rw [hnat]
  omega

theorem paperGeneralCrossPolynomial_direction_zero
    (n : ℕ) (hn : 3 ≤ n) (a : ℕ → ℝ) :
    (paperGeneralCrossPolynomial n a
      (paperPerturbationDirection n)).eval 0 = a n := by
  rw [←Polynomial.coeff_zero_eq_eval_zero, paperGeneralCrossPolynomial_coeff,
    if_pos (by omega : 0 < n)]
  simp [paperGeneralCoefficient_direction_last n hn a]

theorem paperPaddedNumerator_add_smul
    (n : ℕ) (x y : ℕ → ℝ) (δ : ℝ) (i : ℤ) :
    paperPaddedNumerator n (fun j => x j + δ*y j) i =
      paperPaddedNumerator n x i +
        δ * paperPaddedNumerator n y i := by
  unfold paperPaddedNumerator
  split_ifs with h
  · ring
  · ring

theorem paperGeneralCoefficient_add_smul_numerator
    (n l : ℕ) (a : ℕ → ℝ) (x y : ℤ → ℝ) (δ : ℝ) :
    paperGeneralCoefficient n a (fun i => x i + δ*y i) l =
      paperGeneralCoefficient n a x l +
        δ * paperGeneralCoefficient n a y l := by
  unfold paperGeneralCoefficient
  calc
    (∑ j ∈ Finset.range (n+1),
        (-1 : ℝ)^(l+j) * a j *
          (x (2*(l:ℤ)-(j:ℤ)-1) +
            δ*y (2*(l:ℤ)-(j:ℤ)-1))) =
      ∑ j ∈ Finset.range (n+1),
        ((-1 : ℝ)^(l+j) * a j *
          x (2*(l:ℤ)-(j:ℤ)-1) +
          δ*((-1 : ℝ)^(l+j) * a j *
            y (2*(l:ℤ)-(j:ℤ)-1))) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

theorem paperGeneralCrossPolynomial_add_smul_numerator
    (n : ℕ) (a x y : ℕ → ℝ) (δ : ℝ) :
    paperGeneralCrossPolynomial n a (fun i => x i + δ*y i) =
      paperGeneralCrossPolynomial n a x +
        Polynomial.C δ * paperGeneralCrossPolynomial n a y := by
  ext j
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul]
  simp only [paperGeneralCrossPolynomial_coeff]
  by_cases hj : j < n
  · rw [if_pos hj, if_pos hj, if_pos hj]
    have hpad : (paperPaddedNumerator n
        (fun i => x i + δ*y i)) =
        (fun i => paperPaddedNumerator n x i +
          δ*paperPaddedNumerator n y i) := by
      funext i
      exact paperPaddedNumerator_add_smul n x y δ i
    rw [hpad, paperGeneralCoefficient_add_smul_numerator]
  · rw [if_neg hj, if_neg hj, if_neg hj]
    ring

def paperPerturbedNumeratorCoeffs
    (n : ℕ) (x : ℕ → ℝ) (δ : ℝ) (i : ℕ) : ℝ :=
  x i + δ * paperPerturbationDirection n i

theorem paperGeneralCrossPolynomial_perturbed
    (n : ℕ) (a x : ℕ → ℝ) (δ : ℝ) :
    paperGeneralCrossPolynomial n a
      (paperPerturbedNumeratorCoeffs n x δ) =
      paperGeneralCrossPolynomial n a x +
        Polynomial.C δ *
          paperGeneralCrossPolynomial n a (paperPerturbationDirection n) := by
  exact paperGeneralCrossPolynomial_add_smul_numerator n a x
    (paperPerturbationDirection n) δ

/-- Repaired arbitrary-order Lemma 10: an interior-positive common candidate
can be perturbed at both coefficient endpoints by one positive amount.  The
segment zero-exclusion hypothesis comes from its assumed Hurwitz stability. -/
theorem paperLemma10_arbitrary_order_frequency_repaired
    (n : ℕ) (hn : 3 ≤ n) (a b x : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (han : 0 < a n) (hbn : 0 < b n)
    (hden : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ ω : ℝ,
      Polynomial.aeval (jw ω)
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i)) ≠ (0 : ℂ))
    (hAnonneg : ∀ t : ℝ, 0 ≤ t →
      0 ≤ (paperGeneralCrossPolynomial n a x).eval t)
    (hBnonneg : ∀ t : ℝ, 0 ≤ t →
      0 ≤ (paperGeneralCrossPolynomial n b x).eval t)
    (hApos : ∀ t : ℝ, 0 < t →
      0 < (paperGeneralCrossPolynomial n a x).eval t)
    (hBpos : ∀ t : ℝ, 0 < t →
      0 < (paperGeneralCrossPolynomial n b x).eval t) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ ω : ℝ,
        0 < ((Polynomial.aeval (jw ω)
            (paperDescendingNumerator n
              (paperPerturbedNumeratorCoeffs n x δ)) : ℂ) /
          Polynomial.aeval (jw ω)
            (paperDescendingDenominator n
              (fun i => (1-r)*a i+r*b i))).re := by
  let fA := paperGeneralCrossPolynomial n a x
  let fB := paperGeneralCrossPolynomial n b x
  let gA := paperGeneralCrossPolynomial n a (paperPerturbationDirection n)
  let gB := paperGeneralCrossPolynomial n b (paperPerturbationDirection n)
  have hgAzero : 0 < gA.eval 0 := by
    change 0 < (paperGeneralCrossPolynomial n a
      (paperPerturbationDirection n)).eval 0
    rw [paperGeneralCrossPolynomial_direction_zero n hn a]
    exact han
  have hgBzero : 0 < gB.eval 0 := by
    change 0 < (paperGeneralCrossPolynomial n b
      (paperPerturbationDirection n)).eval 0
    rw [paperGeneralCrossPolynomial_direction_zero n hn b]
    exact hbn
  have hgAdeg : 0 < gA.degree :=
    paperGeneralCrossPolynomial_direction_degree_pos n hn a ha0
  have hgBdeg : 0 < gB.degree :=
    paperGeneralCrossPolynomial_direction_degree_pos n hn b hb0
  have hgAlead : 0 ≤ gA.leadingCoeff := by
    have hm := paperGeneralCrossPolynomial_direction_monic n hn a ha0
    change 0 ≤ (paperGeneralCrossPolynomial n a
      (paperPerturbationDirection n)).leadingCoeff
    rw [hm]
    norm_num
  have hgBlead : 0 ≤ gB.leadingCoeff := by
    have hm := paperGeneralCrossPolynomial_direction_monic n hn b hb0
    change 0 ≤ (paperGeneralCrossPolynomial n b
      (paperPerturbationDirection n)).leadingCoeff
    rw [hm]
    norm_num
  obtain ⟨δ, hδ, hA, hB⟩ :=
    polynomial_positive_perturbation_pair_at_zero
      fA fB gA gB hAnonneg hBnonneg hApos hBpos
      hgAzero hgBzero hgAdeg hgAlead hgBdeg hgBlead
  have hcrossA : ∀ t : ℝ, 0 ≤ t →
      0 < ∑ j ∈ Finset.range n,
        paperGeneralCoefficient n a
          (paperPaddedNumerator n (paperPerturbedNumeratorCoeffs n x δ))
          (n-j) * t^j := by
    intro t ht
    rw [←paperGeneralCrossPolynomial_eval]
    rw [paperGeneralCrossPolynomial_perturbed]
    exact hA t ht
  have hcrossB : ∀ t : ℝ, 0 ≤ t →
      0 < ∑ j ∈ Finset.range n,
        paperGeneralCoefficient n b
          (paperPaddedNumerator n (paperPerturbedNumeratorCoeffs n x δ))
          (n-j) * t^j := by
    intro t ht
    rw [←paperGeneralCrossPolynomial_eval]
    rw [paperGeneralCrossPolynomial_perturbed]
    exact hB t ht
  exact ⟨δ, hδ,
    paperDescending_segment_positive_real_of_common_cross
      n (by omega) a b (paperPerturbedNumeratorCoeffs n x δ)
      hden hcrossA hcrossB⟩


open ComplexConjugate


def paperRaiseProduct (n : ℕ) (a : ℕ → ℝ) : Polynomial ℝ :=
  Polynomial.X^n *
    (paperDescendingDenominator n a).comp (-Polynomial.X)

def paperRaiseCorrection (n : ℕ) (a : ℕ → ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (n+1),
    Polynomial.monomial j
      ((-1 : ℝ)^j * (paperRaiseProduct n a).coeff (2*j))

theorem paperRaiseCorrection_coeff
    (n : ℕ) (a : ℕ → ℝ) (j : ℕ) :
    (paperRaiseCorrection n a).coeff j =
      if j ≤ n then
        (-1 : ℝ)^j * (paperRaiseProduct n a).coeff (2*j)
      else 0 := by
  simp [paperRaiseCorrection, Polynomial.finset_sum_coeff,
    Polynomial.coeff_monomial, Finset.sum_ite_eq', Nat.lt_succ_iff]

theorem paperRaiseProduct_natDegree_le
    (n : ℕ) (a : ℕ → ℝ) :
    (paperRaiseProduct n a).natDegree ≤ 2*n := by
  have hden : (paperDescendingDenominator n a).natDegree ≤ n := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    rw [paperDescendingDenominator_coeff, if_neg (not_le.mpr hm)]
  have hcomp :
      ((paperDescendingDenominator n a).comp (-Polynomial.X)).natDegree ≤ n := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    rw [paperCoeff_comp_neg_X, paperDescendingDenominator_coeff,
      if_neg (not_le.mpr hm)]
    ring
  unfold paperRaiseProduct
  have h := Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_X_pow_le n) hcomp
  omega

theorem paperRaiseProduct_top_coeff
    (n : ℕ) (a : ℕ → ℝ) (ha : a 0 = 1) :
    (paperRaiseProduct n a).coeff (2*n) = (-1 : ℝ)^n := by
  rw [paperRaiseProduct]
  have hidx : 2*n = n+n := by omega
  rw [hidx, Polynomial.coeff_X_pow_mul]
  rw [paperCoeff_comp_neg_X,
    paperDescendingDenominator_coeff, if_pos le_rfl,
    Nat.sub_self, ha, mul_one]

theorem paperRaiseCorrection_monic
    (n : ℕ) (a : ℕ → ℝ) (ha : a 0 = 1) :
    (paperRaiseCorrection n a).Monic := by
  have hdegree : (paperRaiseCorrection n a).natDegree ≤ n := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [paperRaiseCorrection_coeff, if_neg (not_le.mpr hj)]
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one n hdegree
  rw [paperRaiseCorrection_coeff, if_pos le_rfl,
    paperRaiseProduct_top_coeff n a ha, ←pow_add]
  rw [show n+n=2*n by omega, pow_mul]
  norm_num

theorem paperRaiseCorrection_degree_pos
    (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ) (ha : a 0 = 1) :
    0 < (paperRaiseCorrection n a).degree := by
  have hdegree : (paperRaiseCorrection n a).natDegree ≤ n := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [paperRaiseCorrection_coeff, if_neg (not_le.mpr hj)]
  have hcoeff : (paperRaiseCorrection n a).coeff n = 1 := by
    rw [paperRaiseCorrection_coeff, if_pos le_rfl,
      paperRaiseProduct_top_coeff n a ha, ←pow_add]
    rw [show n+n=2*n by omega, pow_mul]
    norm_num
  have hnat := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    hdegree (by rw [hcoeff]; norm_num)
  apply Polynomial.natDegree_pos_iff_degree_pos.mp
  rw [hnat]
  exact hn

theorem paperRaiseCorrection_eval
    (n : ℕ) (a : ℕ → ℝ) (ω : ℝ) :
    (paperRaiseCorrection n a).eval (ω^2) =
      ((jw ω)^n *
        conj (Polynomial.aeval (jw ω)
          (paperDescendingDenominator n a) : ℂ)).re := by
  have hdegree : (paperRaiseProduct n a).natDegree < 2*(n+1) := by
    have h := paperRaiseProduct_natDegree_le n a
    omega
  have hconj : conj (Polynomial.aeval (jw ω)
      (paperDescendingDenominator n a) : ℂ) =
      Polynomial.aeval (jw ω)
        ((paperDescendingDenominator n a).comp (-Polynomial.X)) := by
    rw [←Polynomial.aeval_conj]
    simp only [Polynomial.aeval_comp, Polynomial.aeval_X]
    have hc : conj (jw ω) = -(jw ω) := by simp [jw]
    rw [hc]
    simp
  have hident : (Polynomial.aeval (jw ω) (paperRaiseProduct n a) : ℂ) =
      (jw ω)^n *
        conj (Polynomial.aeval (jw ω)
          (paperDescendingDenominator n a) : ℂ) := by
    simp [paperRaiseProduct, Polynomial.aeval_mul, hconj]
  rw [←hident]
  rw [real_part_aeval_eq_even_coeff_sum
    (paperRaiseProduct n a) (n+1) ω hdegree]
  rw [paperRaiseCorrection]
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_mul]
  ring

theorem paperDescending_cross_identity
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) (ω : ℝ) :
    ((Polynomial.aeval (jw ω) (paperDescendingNumerator n x) : ℂ) *
      conj (Polynomial.aeval (jw ω)
        (paperDescendingDenominator n a) : ℂ)).re =
      (paperGeneralCrossPolynomial n a x).eval (ω^2) := by
  rw [←paperGenericDenominator_eq_descending,
    ←paperGenericNumerator_eq_descending n hn]
  rw [paperGeneric_cross_identity n hn a x ω]
  rw [paperGeneralCrossPolynomial_eval]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_mul]

theorem complex_div_re_eq_cross_product (z w : ℂ) :
    (z / w).re = (z * conj w).re / Complex.normSq w := by
  rw [complex_div_re_eq, Complex.mul_re]
  simp only [Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add]

theorem paperDescending_degree_raised_re
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ)
    (ε ω : ℝ) :
    ((Polynomial.aeval (jw ω)
      (paperDescendingNumerator n x +
        Polynomial.C ε * Polynomial.X^n) : ℂ) /
      Polynomial.aeval (jw ω) (paperDescendingDenominator n a)).re =
      ((paperGeneralCrossPolynomial n a x).eval (ω^2) +
        ε * (paperRaiseCorrection n a).eval (ω^2)) /
      Complex.normSq
        (Polynomial.aeval (jw ω) (paperDescendingDenominator n a) : ℂ) := by
  let z : ℂ := Polynomial.aeval (jw ω) (paperDescendingNumerator n x)
  let w : ℂ := Polynomial.aeval (jw ω) (paperDescendingDenominator n a)
  have hz : (Polynomial.aeval (jw ω)
      (paperDescendingNumerator n x +
        Polynomial.C ε * Polynomial.X^n) : ℂ) =
      z + (ε : ℂ) * (jw ω)^n := by
    simp [z, Polynomial.aeval_add, Polynomial.aeval_mul]
  rw [hz, complex_div_re_eq_cross_product]
  rw [add_mul, Complex.add_re]
  rw [paperDescending_cross_identity n hn a x ω]
  rw [mul_assoc, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [←paperRaiseCorrection_eval]

theorem paperDescending_degree_raise_pair
    (n : ℕ) (hn : 0 < n) (a b x : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hdenA : ∀ ω : ℝ,
      Polynomial.aeval (jw ω) (paperDescendingDenominator n a) ≠ (0 : ℂ))
    (hdenB : ∀ ω : ℝ,
      Polynomial.aeval (jw ω) (paperDescendingDenominator n b) ≠ (0 : ℂ))
    (hcrossA : ∀ t : ℝ, 0 ≤ t →
      0 < (paperGeneralCrossPolynomial n a x).eval t)
    (hcrossB : ∀ t : ℝ, 0 ≤ t →
      0 < (paperGeneralCrossPolynomial n b x).eval t) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ ω : ℝ,
        0 < ((Polynomial.aeval (jw ω)
            (paperDescendingNumerator n x +
              Polynomial.C ε * Polynomial.X^n) : ℂ) /
          Polynomial.aeval (jw ω)
            (paperDescendingDenominator n a)).re) ∧
      (∀ ω : ℝ,
        0 < ((Polynomial.aeval (jw ω)
            (paperDescendingNumerator n x +
              Polynomial.C ε * Polynomial.X^n) : ℂ) /
          Polynomial.aeval (jw ω)
            (paperDescendingDenominator n b)).re) := by
  let fA := paperGeneralCrossPolynomial n a x
  let fB := paperGeneralCrossPolynomial n b x
  let gA := paperRaiseCorrection n a
  let gB := paperRaiseCorrection n b
  have hAgmonic : gA.Monic := paperRaiseCorrection_monic n a ha0
  have hBgmonic : gB.Monic := paperRaiseCorrection_monic n b hb0
  have hAgdegree : 0 < gA.degree :=
    paperRaiseCorrection_degree_pos n hn a ha0
  have hBgdegree : 0 < gB.degree :=
    paperRaiseCorrection_degree_pos n hn b hb0
  have hAglead : 0 ≤ gA.leadingCoeff := by
    rw [hAgmonic]
    norm_num
  have hBglead : 0 ≤ gB.leadingCoeff := by
    rw [hBgmonic]
    norm_num
  obtain ⟨ε, hε, hA, hB⟩ :=
    polynomial_positive_perturbation_pair fA fB gA gB
      hcrossA hcrossB hAgdegree hAglead hBgdegree hBglead
  refine ⟨ε, hε, ?_, ?_⟩
  · intro ω
    rw [paperDescending_degree_raised_re n hn a x ε ω]
    exact div_pos (by
      simpa [fA, gA, Polynomial.eval_add, Polynomial.eval_mul]
        using hA (ω^2) (sq_nonneg ω))
      (Complex.normSq_pos.mpr (hdenA ω))
  · intro ω
    rw [paperDescending_degree_raised_re n hn b x ε ω]
    exact div_pos (by
      simpa [fB, gB, Polynomial.eval_add, Polynomial.eval_mul]
        using hB (ω^2) (sq_nonneg ω))
      (Complex.normSq_pos.mpr (hdenB ω))

theorem paperDescendingDenominator_affine
    (n : ℕ) (a b : ℕ → ℝ) (r : ℝ) :
    paperDescendingDenominator n
      (fun i => (1-r)*a i+r*b i) =
      Polynomial.C (1-r) * paperDescendingDenominator n a +
        Polynomial.C r * paperDescendingDenominator n b := by
  ext m
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul]
  simp only [paperDescendingDenominator_coeff]
  by_cases hm : m ≤ n
  · rw [if_pos hm, if_pos hm, if_pos hm]
  · rw [if_neg hm, if_neg hm, if_neg hm]
    ring

/-- A fixed numerator with positive real part at both denominator endpoints
has positive real part throughout a zero-free polynomial segment. -/
theorem paperDescending_common_numerator_segment_re_pos
    (n : ℕ) (a b : ℕ → ℝ) (p : Polynomial ℝ)
    (hden : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ ω : ℝ,
      Polynomial.aeval (jw ω)
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i)) ≠ (0 : ℂ))
    (ha : ∀ ω : ℝ,
      0 < ((Polynomial.aeval (jw ω) p : ℂ) /
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n a)).re)
    (hb : ∀ ω : ℝ,
      0 < ((Polynomial.aeval (jw ω) p : ℂ) /
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n b)).re) :
    ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ ω : ℝ,
      0 < ((Polynomial.aeval (jw ω) p : ℂ) /
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n
            (fun i => (1-r)*a i+r*b i))).re := by
  intro r hr0 hr1 ω
  let z : ℂ := Polynomial.aeval (jw ω) p
  let wa : ℂ := Polynomial.aeval (jw ω) (paperDescendingDenominator n a)
  let wb : ℂ := Polynomial.aeval (jw ω) (paperDescendingDenominator n b)
  let wr : ℂ := Polynomial.aeval (jw ω)
    (paperDescendingDenominator n (fun i => (1-r)*a i+r*b i))
  have hwa : wa ≠ 0 := by
    have h := hden 0 (by norm_num) (by norm_num) ω
    simpa [wa] using h
  have hwb : wb ≠ 0 := by
    have h := hden 1 (by norm_num) (by norm_num) ω
    simpa [wb] using h
  have hcrossA : 0 < z.re * wa.re + z.im * wa.im := by
    have h := ha ω
    change 0 < (z / wa).re at h
    rw [complex_div_re_eq] at h
    exact (div_pos_iff_of_pos_right (Complex.normSq_pos.mpr hwa)).mp h
  have hcrossB : 0 < z.re * wb.re + z.im * wb.im := by
    have h := hb ω
    change 0 < (z / wb).re at h
    rw [complex_div_re_eq] at h
    exact (div_pos_iff_of_pos_right (Complex.normSq_pos.mpr hwb)).mp h
  have hwr : wr = ((1-r : ℝ) : ℂ) * wa + (r : ℂ) * wb := by
    dsimp [wr, wa, wb]
    rw [paperDescendingDenominator_affine]
    simp [Polynomial.aeval_add, Polynomial.aeval_mul]
  have hwrre : wr.re = (1-r)*wa.re+r*wb.re := by
    rw [hwr]
    simp [Complex.add_re, Complex.mul_re]
  have hwrim : wr.im = (1-r)*wa.im+r*wb.im := by
    rw [hwr]
    simp [Complex.add_im, Complex.mul_im]
  have hcross : 0 < z.re * wr.re + z.im * wr.im := by
    rw [hwrre, hwrim]
    convert convexCoeff_pos_of_pos hcrossA hcrossB hr0 hr1 using 1;
      ring
  change 0 < (z / wr).re
  rw [complex_div_re_eq]
  exact div_pos hcross (Complex.normSq_pos.mpr (hden r hr0 hr1 ω))

/-- Once a common degree-(n-1) numerator has a positive coefficient
polynomial at both endpoints, one common leading coefficient makes its
degree-n extension positive real on the full segment. -/
theorem paperDescending_degree_raise_segment
    (n : ℕ) (hn : 0 < n) (a b x : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hden : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ ω : ℝ,
      Polynomial.aeval (jw ω)
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i)) ≠ (0 : ℂ))
    (hcrossA : ∀ t : ℝ, 0 ≤ t →
      0 < (paperGeneralCrossPolynomial n a x).eval t)
    (hcrossB : ∀ t : ℝ, 0 ≤ t →
      0 < (paperGeneralCrossPolynomial n b x).eval t) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ ω : ℝ,
        0 < ((Polynomial.aeval (jw ω)
            (paperDescendingNumerator n x +
              Polynomial.C ε * Polynomial.X^n) : ℂ) /
          Polynomial.aeval (jw ω)
            (paperDescendingDenominator n
              (fun i => (1-r)*a i+r*b i))).re := by
  have hdenA : ∀ ω : ℝ,
      Polynomial.aeval (jw ω)
        (paperDescendingDenominator n a) ≠ (0 : ℂ) := by
    intro ω
    simpa using hden 0 (by norm_num) (by norm_num) ω
  have hdenB : ∀ ω : ℝ,
      Polynomial.aeval (jw ω)
        (paperDescendingDenominator n b) ≠ (0 : ℂ) := by
    intro ω
    simpa using hden 1 (by norm_num) (by norm_num) ω
  obtain ⟨ε, hε, hA, hB⟩ :=
    paperDescending_degree_raise_pair n hn a b x ha0 hb0
      hdenA hdenB hcrossA hcrossB
  exact ⟨ε, hε,
    paperDescending_common_numerator_segment_re_pos n a b
      (paperDescendingNumerator n x +
        Polynomial.C ε * Polynomial.X^n) hden hA hB⟩



theorem paperDescendingNumerator_raise_natDegree_eq
    (n : ℕ) (x : ℕ → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    (paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    rw [Polynomial.coeff_add, paperDescendingNumerator_coeff,
      if_neg (by omega : ¬m<n), Polynomial.coeff_C_mul]
    simp [Polynomial.coeff_X_pow, show m ≠ n by omega]
  · rw [Polynomial.coeff_add, paperDescendingNumerator_coeff,
      if_neg (by omega : ¬n<n), Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow_self]
    simpa using ne_of_gt hε

/-- Full conditional Lemma 10 for arbitrary order: the paper's coefficient
perturbation gives a common degree-(n-1) numerator, and a second small
positive leading term gives a common degree-n numerator for the segment. -/
theorem paperLemma10_arbitrary_order_repaired
    (n : ℕ) (hn : 3 ≤ n) (a b x : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (han : 0 < a n) (hbn : 0 < b n)
    (hden : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ ω : ℝ,
      Polynomial.aeval (jw ω)
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i)) ≠ (0 : ℂ))
    (hAnonneg : ∀ t : ℝ, 0 ≤ t →
      0 ≤ (paperGeneralCrossPolynomial n a x).eval t)
    (hBnonneg : ∀ t : ℝ, 0 ≤ t →
      0 ≤ (paperGeneralCrossPolynomial n b x).eval t)
    (hApos : ∀ t : ℝ, 0 < t →
      0 < (paperGeneralCrossPolynomial n a x).eval t)
    (hBpos : ∀ t : ℝ, 0 < t →
      0 < (paperGeneralCrossPolynomial n b x).eval t) :
    ∃ δ ε : ℝ, 0 < δ ∧ 0 < ε ∧
      (paperDescendingNumerator n
          (paperPerturbedNumeratorCoeffs n x δ) +
        Polynomial.C ε * Polynomial.X^n).natDegree = n ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ ω : ℝ,
        0 < ((Polynomial.aeval (jw ω)
            (paperDescendingNumerator n
                (paperPerturbedNumeratorCoeffs n x δ) +
              Polynomial.C ε * Polynomial.X^n) : ℂ) /
          Polynomial.aeval (jw ω)
            (paperDescendingDenominator n
              (fun i => (1-r)*a i+r*b i))).re := by
  obtain ⟨δ, hδ, hfrequency⟩ :=
    paperLemma10_arbitrary_order_frequency_repaired
      n hn a b x ha0 hb0 han hbn hden
      hAnonneg hBnonneg hApos hBpos
  have hdenA : ∀ ω : ℝ,
      Polynomial.aeval (jw ω)
        (paperDescendingDenominator n a) ≠ (0 : ℂ) := by
    intro ω
    simpa using hden 0 (by norm_num) (by norm_num) ω
  have hdenB : ∀ ω : ℝ,
      Polynomial.aeval (jw ω)
        (paperDescendingDenominator n b) ≠ (0 : ℂ) := by
    intro ω
    simpa using hden 1 (by norm_num) (by norm_num) ω
  have hqa : ∀ ω : ℝ,
      0 < ((Polynomial.aeval (jw ω)
          (paperDescendingNumerator n
            (paperPerturbedNumeratorCoeffs n x δ)) : ℂ) /
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n a)).re := by
    intro ω
    simpa using hfrequency 0 (by norm_num) (by norm_num) ω
  have hqb : ∀ ω : ℝ,
      0 < ((Polynomial.aeval (jw ω)
          (paperDescendingNumerator n
            (paperPerturbedNumeratorCoeffs n x δ)) : ℂ) /
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n b)).re := by
    intro ω
    simpa using hfrequency 1 (by norm_num) (by norm_num) ω
  have hcrossA : ∀ t : ℝ, 0 ≤ t →
      0 < (paperGeneralCrossPolynomial n a
        (paperPerturbedNumeratorCoeffs n x δ)).eval t := by
    have h := (paperDescending_quotient_pos_iff_cross_pos n
      (by omega : 0 < n) a (paperPerturbedNumeratorCoeffs n x δ)
      hdenA).mp hqa
    intro t ht
    rw [paperGeneralCrossPolynomial_eval]
    exact h t ht
  have hcrossB : ∀ t : ℝ, 0 ≤ t →
      0 < (paperGeneralCrossPolynomial n b
        (paperPerturbedNumeratorCoeffs n x δ)).eval t := by
    have h := (paperDescending_quotient_pos_iff_cross_pos n
      (by omega : 0 < n) b (paperPerturbedNumeratorCoeffs n x δ)
      hdenB).mp hqb
    intro t ht
    rw [paperGeneralCrossPolynomial_eval]
    exact h t ht
  obtain ⟨ε, hε, hfull⟩ :=
    paperDescending_degree_raise_segment n (by omega) a b
      (paperPerturbedNumeratorCoeffs n x δ)
      ha0 hb0 hden hcrossA hcrossB
  exact ⟨δ, ε, hδ, hε,
    paperDescendingNumerator_raise_natDegree_eq n
      (paperPerturbedNumeratorCoeffs n x δ) ε hε,
    hfull⟩



/-- Root-location form of Hurwitz stability for a real polynomial. -/
def paperPolynomialHurwitz (p : Polynomial ℝ) : Prop :=
  ∀ z : ℂ, 0 ≤ z.re → Polynomial.aeval z p ≠ (0 : ℂ)

/-- The paper's degree-matched, analytic, positive-frequency definition. -/
def paperPolynomialSPR (n : ℕ)
    (p q : Polynomial ℝ) : Prop :=
  p.natDegree = n ∧ q.natDegree = n ∧
    paperPolynomialHurwitz q ∧
    ∀ ω : ℝ,
      0 < ((Polynomial.aeval (jw ω) p : ℂ) /
        Polynomial.aeval (jw ω) q).re

theorem paperPolynomialHurwitz_imag_ne_zero
    (p : Polynomial ℝ) (hp : paperPolynomialHurwitz p)
    (ω : ℝ) :
    Polynomial.aeval (jw ω) p ≠ (0 : ℂ) := by
  exact hp (jw ω) (by simp [jw])

theorem paperDescendingDenominator_natDegree_eq
    (n : ℕ) (a : ℕ → ℝ) (ha : a 0 = 1) :
    (paperDescendingDenominator n a).natDegree = n := by
  have hdegree : (paperDescendingDenominator n a).natDegree ≤ n := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    rw [paperDescendingDenominator_coeff, if_neg (not_le.mpr hm)]
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdegree
  rw [paperDescendingDenominator_coeff, if_pos le_rfl,
    Nat.sub_self, ha]
  norm_num

/-- The repaired conditional Lemma 10, stated as a common SPR numerator for
every member of the stable polynomial segment. -/
theorem paperLemma10_arbitrary_order_spr
    (n : ℕ) (hn : 3 ≤ n) (a b x : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (han : 0 < a n) (hbn : 0 < b n)
    (hstable : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i)))
    (hAnonneg : ∀ t : ℝ, 0 ≤ t →
      0 ≤ (paperGeneralCrossPolynomial n a x).eval t)
    (hBnonneg : ∀ t : ℝ, 0 ≤ t →
      0 ≤ (paperGeneralCrossPolynomial n b x).eval t)
    (hApos : ∀ t : ℝ, 0 < t →
      0 < (paperGeneralCrossPolynomial n a x).eval t)
    (hBpos : ∀ t : ℝ, 0 < t →
      0 < (paperGeneralCrossPolynomial n b x).eval t) :
    ∃ δ ε : ℝ, 0 < δ ∧ 0 < ε ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        paperPolynomialSPR n
          (paperDescendingNumerator n
              (paperPerturbedNumeratorCoeffs n x δ) +
            Polynomial.C ε * Polynomial.X^n)
          (paperDescendingDenominator n
            (fun i => (1-r)*a i+r*b i)) := by
  have hden : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ ω : ℝ,
      Polynomial.aeval (jw ω)
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i)) ≠ (0 : ℂ) := by
    intro r hr0 hr1 ω
    exact paperPolynomialHurwitz_imag_ne_zero _
      (hstable r hr0 hr1) ω
  obtain ⟨δ, ε, hδ, hε, hdegree, hfreq⟩ :=
    paperLemma10_arbitrary_order_repaired n hn a b x
      ha0 hb0 han hbn hden hAnonneg hBnonneg hApos hBpos
  refine ⟨δ, ε, hδ, hε, ?_⟩
  intro r hr0 hr1
  have hmix0 : (fun i => (1-r)*a i+r*b i) 0 = 1 := by
    simp [ha0, hb0]
  exact ⟨hdegree,
    paperDescendingDenominator_natDegree_eq n _ hmix0,
    hstable r hr0 hr1,
    hfreq r hr0 hr1⟩



/-- A monic Hurwitz polynomial of positive degree has a positive constant
coefficient.  This removes an auxiliary sign hypothesis from Lemma 10. -/
theorem paperPolynomialHurwitz_monic_eval_zero_pos
    (p : Polynomial ℝ) (hp : p.Monic)
    (hdegree : 0 < p.degree)
    (hstable : paperPolynomialHurwitz p) :
    0 < p.eval 0 := by
  have hlead : 0 ≤ p.leadingCoeff := by
    rw [hp]
    norm_num
  have htend : Filter.Tendsto (fun t : ℝ => p.eval t)
      Filter.atTop Filter.atTop :=
    p.tendsto_atTop_of_leadingCoeff_nonneg hdegree hlead
  have htop : ∀ᶠ t : ℝ in Filter.atTop, 0 < p.eval t :=
    htend.eventually (Filter.eventually_gt_atTop 0)
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 htop
  let T : ℝ := max 1 R
  have hTpos : 0 < T := by
    dsimp [T]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (le_max_left _ _)
  have hpT : 0 < p.eval T := hR T (le_max_right _ _)
  by_contra hnot
  have hp0 : p.eval 0 ≤ 0 := le_of_not_gt hnot
  have hmem : (0 : ℝ) ∈ (fun t : ℝ => p.eval t) '' Set.Icc 0 T :=
    (intermediate_value_Icc hTpos.le p.continuous.continuousOn)
      ⟨hp0, hpT.le⟩
  obtain ⟨t, ht, hroot⟩ := hmem
  have hno := hstable (t : ℂ) (by simpa using ht.1)
  apply hno
  have hz : ((p.eval t : ℝ) : ℂ) = 0 := by exact_mod_cast hroot
  exact (Polynomial.ofReal_eval (K := ℂ) p t).symm.trans hz

theorem paperDescendingDenominator_const_pos_of_hurwitz
    (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (ha0 : a 0 = 1)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a)) :
    0 < a n := by
  have hm : (paperDescendingDenominator n a).Monic :=
    paperDescendingDenominator_monic n a ha0
  have hd : 0 < (paperDescendingDenominator n a).degree := by
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    rw [paperDescendingDenominator_natDegree_eq n a ha0]
    exact hn
  have hpos := paperPolynomialHurwitz_monic_eval_zero_pos _ hm hd hstable
  rw [←Polynomial.coeff_zero_eq_eval_zero,
    paperDescendingDenominator_coeff, if_pos (by omega : 0 ≤ n)] at hpos
  simpa using hpos

/-- Lemma 10 with the denominator coefficient signs derived from stability. -/
theorem paperLemma10_arbitrary_order_spr_of_stable_segment
    (n : ℕ) (hn : 3 ≤ n) (a b x : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstable : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i)))
    (hAnonneg : ∀ t : ℝ, 0 ≤ t →
      0 ≤ (paperGeneralCrossPolynomial n a x).eval t)
    (hBnonneg : ∀ t : ℝ, 0 ≤ t →
      0 ≤ (paperGeneralCrossPolynomial n b x).eval t)
    (hApos : ∀ t : ℝ, 0 < t →
      0 < (paperGeneralCrossPolynomial n a x).eval t)
    (hBpos : ∀ t : ℝ, 0 < t →
      0 < (paperGeneralCrossPolynomial n b x).eval t) :
    ∃ δ ε : ℝ, 0 < δ ∧ 0 < ε ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        paperPolynomialSPR n
          (paperDescendingNumerator n
              (paperPerturbedNumeratorCoeffs n x δ) +
            Polynomial.C ε * Polynomial.X^n)
          (paperDescendingDenominator n
            (fun i => (1-r)*a i+r*b i)) := by
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa using hstable 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa using hstable 1 (by norm_num) (by norm_num)
  have han : 0 < a n :=
    paperDescendingDenominator_const_pos_of_hurwitz n (by omega)
      a ha0 hstableA
  have hbn : 0 < b n :=
    paperDescendingDenominator_const_pos_of_hurwitz n (by omega)
      b hb0 hstableB
  exact paperLemma10_arbitrary_order_spr n hn a b x
    ha0 hb0 han hbn hstable hAnonneg hBnonneg hApos hBpos



theorem paperDescendingDenominator_six (a : MonicSextic) :
    paperDescendingDenominator 6 (paperGeneralA6 a) =
      a.realPolynomial := by
  simp [paperDescendingDenominator, paperGeneralA6,
    MonicSextic.realPolynomial, Finset.sum_range_succ,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

theorem sextic_realPolynomial_natDegree_six (a : MonicSextic) :
    a.realPolynomial.natDegree = 6 := by
  unfold MonicSextic.realPolynomial
  compute_degree!

theorem sextic_realPolynomial_aeval
    (a : MonicSextic) (z : ℂ) :
    Polynomial.aeval z a.realPolynomial = a.eval z := by
  simp [MonicSextic.realPolynomial, MonicSextic.eval]

theorem sextic_paperPolynomialHurwitz
    (a : MonicSextic) (ha : a.Hurwitz) :
    paperPolynomialHurwitz a.realPolynomial := by
  intro z hz hzero
  rw [sextic_realPolynomial_aeval] at hzero
  exact (not_lt_of_ge hz) (ha z hzero)

theorem sextic_SPRFor_to_paperPolynomialSPR
    (a n : MonicSextic) (ha : a.SPRFor n) :
    paperPolynomialSPR 6 n.realPolynomial a.realPolynomial := by
  rcases ha with ⟨hstable, hpositive⟩
  refine ⟨sextic_realPolynomial_natDegree_six n,
    sextic_realPolynomial_natDegree_six a,
    sextic_paperPolynomialHurwitz a hstable, ?_⟩
  intro ω
  simpa [sextic_realPolynomial_aeval, MonicSextic.evalJW]
    using hpositive ω

theorem sixth_order_main_paperPolynomialSPR
    (a b : MonicSextic) (h : a.AllConvexHurwitz b) :
    ∃ p : Polynomial ℝ,
      paperPolynomialSPR 6 p
        (paperDescendingDenominator 6 (paperGeneralA6 a)) ∧
      paperPolynomialSPR 6 p
        (paperDescendingDenominator 6 (paperGeneralA6 b)) := by
  obtain ⟨n, ha, hb⟩ := (sixth_order_main a b).2 h
  refine ⟨n.realPolynomial, ?_, ?_⟩
  · rw [paperDescendingDenominator_six]
    exact sextic_SPRFor_to_paperPolynomialSPR a n ha
  · rw [paperDescendingDenominator_six]
    exact sextic_SPRFor_to_paperPolynomialSPR b n hb

theorem sixth_order_main_paperPolynomialSPR_segment
    (a b : MonicSextic) (h : a.AllConvexHurwitz b) :
    ∃ p : Polynomial ℝ,
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        paperPolynomialSPR 6 p
          (paperDescendingDenominator 6
            (paperGeneralA6 (a.convex b r))) := by
  obtain ⟨n, hpositive⟩ :=
    MonicSextic.commonSPR_segment_frequency_positive
      ((sixth_order_main a b).2 h)
  refine ⟨n.realPolynomial, ?_⟩
  intro r hr0 hr1
  rw [paperDescendingDenominator_six]
  exact sextic_SPRFor_to_paperPolynomialSPR
    (a.convex b r) n ⟨h r hr0 hr1, hpositive r hr0 hr1⟩




/-- Interpret the paper's leading-one coefficient sequence as a sextic. -/
def paperSexticOfCoeffs (a : ℕ → ℝ) : MonicSextic :=
  ⟨a 1, a 2, a 3, a 4, a 5, a 6⟩

theorem paperDescendingDenominator_six_of_monic
    (a : ℕ → ℝ) (ha0 : a 0 = 1) :
    paperDescendingDenominator 6 a =
      (paperSexticOfCoeffs a).realPolynomial := by
  simp [paperDescendingDenominator, paperSexticOfCoeffs,
    MonicSextic.realPolynomial, Finset.sum_range_succ,
    ← Polynomial.C_mul_X_pow_eq_monomial, ha0]
  ring

theorem sextic_Hurwitz_of_paperPolynomialHurwitz
    (a : MonicSextic)
    (ha : paperPolynomialHurwitz a.realPolynomial) :
    a.Hurwitz := by
  intro z hz
  by_contra hnot
  have hnonneg : 0 ≤ z.re := le_of_not_gt hnot
  exact ha z hnonneg (by
    rw [sextic_realPolynomial_aeval]
    exact hz)

theorem paperSexticOfCoeffs_convex_polynomial
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (r : ℝ) :
    paperDescendingDenominator 6
      (fun i => (1-r)*a i+r*b i) =
        ((paperSexticOfCoeffs a).convex
          (paperSexticOfCoeffs b) r).realPolynomial := by
  rw [paperDescendingDenominator_affine,
    paperDescendingDenominator_six_of_monic a ha0,
    paperDescendingDenominator_six_of_monic b hb0]
  unfold MonicSextic.realPolynomial MonicSextic.convex
    paperSexticOfCoeffs
  simp only [map_add, map_mul, map_sub, map_one]
  ring

theorem sixth_order_paper_coefficient_sequence
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator 6
          (fun i => (1-r)*a i+r*b i))) ↔
      ∃ p : Polynomial ℝ,
        ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
          paperPolynomialSPR 6 p
            (paperDescendingDenominator 6
              (fun i => (1-r)*a i+r*b i)) := by
  let A := paperSexticOfCoeffs a
  let B := paperSexticOfCoeffs b
  constructor
  · intro hstable
    have hAB : A.AllConvexHurwitz B := by
      intro r hr0 hr1
      apply sextic_Hurwitz_of_paperPolynomialHurwitz
      rw [← paperSexticOfCoeffs_convex_polynomial
        a b ha0 hb0 r]
      exact hstable r hr0 hr1
    obtain ⟨p, hp⟩ := sixth_order_main_paperPolynomialSPR_segment
      A B hAB
    refine ⟨p, ?_⟩
    intro r hr0 hr1
    have hpr := hp r hr0 hr1
    rw [paperDescendingDenominator_six] at hpr
    rw [paperSexticOfCoeffs_convex_polynomial
      a b ha0 hb0 r]
    exact hpr
  · rintro ⟨p, hp⟩ r hr0 hr1
    exact (hp r hr0 hr1).2.2.1



open scoped ComplexOrder


/-- Zero exclusion on a complex segment rules out antipodal endpoint
phases.  This is the pointwise alternative to the paper's ellipse regions. -/
theorem no_segment_zero_imp_ratio_not_nonpositive
    (a b : ℂ) (ha : a ≠ 0)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      ((1-r : ℝ) : ℂ) * a + (r : ℂ) * b ≠ 0) :
    ¬ b / a ≤ 0 := by
  intro hratio
  have hre : (b/a).re ≤ 0 := (Complex.nonpos_iff.mp hratio).1
  have him : (b/a).im = 0 := (Complex.nonpos_iff.mp hratio).2
  have hreal : b/a = (((b/a).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  let t : ℝ := -(b/a).re
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hb : b = -(t : ℂ) * a := by
    have hmul : b/a*a = b := div_mul_cancel₀ b ha
    rw [hreal] at hmul
    simpa [t] using hmul.symm
  let r : ℝ := 1/(1+t)
  have hden : 0 < 1+t := by linarith
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    apply (div_le_iff₀ hden).2
    nlinarith
  have hrt : 1-r-r*t = 0 := by
    dsimp [r]
    field_simp [ne_of_gt hden]
  have hrtC : (((1-r : ℝ) : ℂ) - (r : ℂ)*(t : ℂ)) = 0 := by
    exact_mod_cast hrt
  have hz : ((1-r : ℝ) : ℂ)*a + (r : ℂ)*b = 0 := by
    rw [hb]
    calc
      ((1-r : ℝ) : ℂ)*a + (r : ℂ)*(-(t : ℂ)*a) =
          ((((1-r : ℝ) : ℂ) - (r : ℂ)*(t : ℂ))*a) := by ring
      _ = 0 := by rw [hrtC, zero_mul]
  exact hsegment r hr0 hr1 hz

theorem complex_norm_add_re_pos_of_not_nonpositive
    (z : ℂ) (hz : ¬ z ≤ 0) :
    0 < ‖z‖ + z.re := by
  have hbound : -‖z‖ ≤ z.re := (abs_le.mp (Complex.abs_re_le_norm z)).1
  by_contra hnot
  have hsumle : ‖z‖ + z.re ≤ 0 := le_of_not_gt hnot
  have hreverse : z.re ≤ -‖z‖ := by linarith only [hsumle]
  have heq : z.re = -‖z‖ := le_antisymm hreverse hbound
  exact hz (Complex.re_eq_neg_norm.mp heq)

/-- At each frequency, the two endpoint values admit a common complex phase.
The norm-weighted sum is an explicit pointwise witness. -/
theorem no_segment_zero_imp_pointwise_bisector_positive
    (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      ((1-r : ℝ) : ℂ) * a + (r : ℂ) * b ≠ 0) :
    0 < ((((‖b‖ : ℂ)*a+(‖a‖ : ℂ)*b)/a)).re ∧
      0 < ((((‖b‖ : ℂ)*a+(‖a‖ : ℂ)*b)/b)).re := by
  have hnotba : ¬ b/a ≤ 0 :=
    no_segment_zero_imp_ratio_not_nonpositive a b ha hsegment
  have hswap : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      ((1-r : ℝ) : ℂ) * b + (r : ℂ) * a ≠ 0 := by
    intro r hr0 hr1
    have h := hsegment (1-r)
      (by linarith only [hr1]) (by linarith only [hr0])
    have heq : ((1-(1-r) : ℝ) : ℂ) * a +
        ((1-r : ℝ) : ℂ) * b =
        ((1-r : ℝ) : ℂ) * b + (r : ℂ) * a := by ring
    rw [heq] at h
    exact h
  have hnotab : ¬ a/b ≤ 0 :=
    no_segment_zero_imp_ratio_not_nonpositive b a hb hswap
  let c : ℂ := (‖b‖ : ℂ)*a+(‖a‖ : ℂ)*b
  change 0 < (c/a).re ∧ 0 < (c/b).re
  constructor
  · have hdiv : c/a = (‖b‖ : ℂ) + (‖a‖ : ℂ)*(b/a) := by
      dsimp [c]
      field_simp [ha]
    have hnorm : ‖a‖ * ‖b/a‖ = ‖b‖ := by
      rw [norm_div]
      field_simp [norm_ne_zero_iff.mpr ha]
    rw [hdiv, Complex.add_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hpos := complex_norm_add_re_pos_of_not_nonpositive (b/a) hnotba
    have hmul := mul_pos (norm_pos_iff.mpr ha) hpos
    nlinarith only [hmul, hnorm]
  · have hdiv : c/b = (‖b‖ : ℂ)*(a/b) + (‖a‖ : ℂ) := by
      dsimp [c]
      field_simp [hb]
    have hnorm : ‖b‖ * ‖a/b‖ = ‖a‖ := by
      rw [norm_div]
      field_simp [norm_ne_zero_iff.mpr hb]
    rw [hdiv, Complex.add_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hpos := complex_norm_add_re_pos_of_not_nonpositive (a/b) hnotab
    have hmul := mul_pos (norm_pos_iff.mpr hb) hpos
    nlinarith only [hmul, hnorm]

theorem no_segment_zero_imp_pointwise_common_positive_phase
    (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      ((1-r : ℝ) : ℂ) * a + (r : ℂ) * b ≠ 0) :
    ∃ c : ℂ, 0 < (c/a).re ∧ 0 < (c/b).re := by
  exact ⟨(‖b‖ : ℂ)*a+(‖a‖ : ℂ)*b,
    no_segment_zero_imp_pointwise_bisector_positive a b ha hb hsegment⟩

/-- A continuous-in-frequency complex witness, built from the two endpoint
denominator values.  It is not asserted to be a polynomial evaluation. -/
def paperPointwiseBisector
    (n : ℕ) (a b : ℕ → ℝ) (ω : ℝ) : ℂ :=
  let A : ℂ := Polynomial.aeval (jw ω) (paperDescendingDenominator n a)
  let B : ℂ := Polynomial.aeval (jw ω) (paperDescendingDenominator n b)
  (‖B‖ : ℂ)*A+(‖A‖ : ℂ)*B

theorem paperStableSegment_pointwise_bisector_positive
    (n : ℕ) (a b : ℕ → ℝ)
    (hstable : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i)))
    (ω : ℝ) :
    0 < ((paperPointwiseBisector n a b ω) /
      Polynomial.aeval (jw ω)
        (paperDescendingDenominator n a)).re ∧
    0 < ((paperPointwiseBisector n a b ω) /
      Polynomial.aeval (jw ω)
        (paperDescendingDenominator n b)).re := by
  let A : ℂ := Polynomial.aeval (jw ω) (paperDescendingDenominator n a)
  let B : ℂ := Polynomial.aeval (jw ω) (paperDescendingDenominator n b)
  have hA : A ≠ 0 := by
    have h := hstable 0 (by norm_num) (by norm_num)
    simpa [A] using paperPolynomialHurwitz_imag_ne_zero _ h ω
  have hB : B ≠ 0 := by
    have h := hstable 1 (by norm_num) (by norm_num)
    simpa [B] using paperPolynomialHurwitz_imag_ne_zero _ h ω
  have hseg : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      ((1-r : ℝ) : ℂ) * A + (r : ℂ) * B ≠ 0 := by
    intro r hr0 hr1
    have h := paperPolynomialHurwitz_imag_ne_zero _
      (hstable r hr0 hr1) ω
    rw [paperDescendingDenominator_affine] at h
    simpa [A, B, Polynomial.aeval_add, Polynomial.aeval_mul] using h
  exact no_segment_zero_imp_pointwise_bisector_positive A B hA hB hseg

theorem paperPointwiseBisector_continuous
    (n : ℕ) (a b : ℕ → ℝ) :
    Continuous (paperPointwiseBisector n a b) := by
  unfold paperPointwiseBisector jw
  fun_prop

/-- The pointwise phase respects conjugation, as required of evaluations of
real-coefficient functions on the imaginary axis. -/
theorem paperPointwiseBisector_conj
    (n : ℕ) (a b : ℕ → ℝ) (ω : ℝ) :
    paperPointwiseBisector n a b (-ω) =
      conj (paperPointwiseBisector n a b ω) := by
  have hA : Polynomial.aeval (jw (-ω)) (paperDescendingDenominator n a) =
      conj (Polynomial.aeval (jw ω) (paperDescendingDenominator n a) : ℂ) := by
    rw [← Polynomial.aeval_conj]
    congr 1
    simp [jw]
  have hB : Polynomial.aeval (jw (-ω)) (paperDescendingDenominator n b) =
      conj (Polynomial.aeval (jw ω) (paperDescendingDenominator n b) : ℂ) := by
    rw [← Polynomial.aeval_conj]
    congr 1
    simp [jw]
  simp [paperPointwiseBisector, hA, hB, Complex.norm_conj]



theorem no_segment_zero_imp_bisector_positive_all
    (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      ((1-r : ℝ) : ℂ) * a + (r : ℂ) * b ≠ 0) :
    ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      0 < (((‖b‖ : ℂ)*a+(‖a‖ : ℂ)*b) /
        (((1-r : ℝ) : ℂ)*a+(r : ℂ)*b)).re := by
  let c : ℂ := (‖b‖ : ℂ)*a+(‖a‖ : ℂ)*b
  have hends := no_segment_zero_imp_pointwise_bisector_positive
    a b ha hb hsegment
  have hc : c ≠ 0 := by
    intro hzero
    have h := hends.1
    change 0 < (c/a).re at h
    simp [hzero] at h
  have hInvA : 0 < (a/c).re :=
    (complex_div_re_pos_comm hc ha).mp hends.1
  have hInvB : 0 < (b/c).re :=
    (complex_div_re_pos_comm hc hb).mp hends.2
  intro r hr0 hr1
  let d : ℂ := ((1-r : ℝ) : ℂ)*a+(r : ℂ)*b
  have hd : d ≠ 0 := hsegment r hr0 hr1
  have hlin : (d/c).re =
      (1-r)*(a/c).re+r*(b/c).re := by
    dsimp [d]
    rw [add_div, mul_div_assoc, mul_div_assoc,
      Complex.add_re, Complex.mul_re, Complex.mul_re]
    simp
  have hpos : 0 < (d/c).re := by
    rw [hlin]
    simpa [add_comm] using
      convexCoeff_pos_of_pos hInvA hInvB hr0 hr1
  exact (complex_div_re_pos_comm hc hd).mpr hpos

theorem paperStableSegment_pointwise_bisector_positive_all
    (n : ℕ) (a b : ℕ → ℝ)
    (hstable : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i)))
    (ω : ℝ) :
    ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      0 < ((paperPointwiseBisector n a b ω) /
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n
            (fun i => (1-r)*a i+r*b i))).re := by
  let A : ℂ := Polynomial.aeval (jw ω) (paperDescendingDenominator n a)
  let B : ℂ := Polynomial.aeval (jw ω) (paperDescendingDenominator n b)
  have hA : A ≠ 0 := by
    have h := hstable 0 (by norm_num) (by norm_num)
    simpa [A] using paperPolynomialHurwitz_imag_ne_zero _ h ω
  have hB : B ≠ 0 := by
    have h := hstable 1 (by norm_num) (by norm_num)
    simpa [B] using paperPolynomialHurwitz_imag_ne_zero _ h ω
  have hseg : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      ((1-r : ℝ) : ℂ)*A+(r : ℂ)*B ≠ 0 := by
    intro r hr0 hr1
    have h := paperPolynomialHurwitz_imag_ne_zero _
      (hstable r hr0 hr1) ω
    rw [paperDescendingDenominator_affine] at h
    simpa [A, B, Polynomial.aeval_add, Polynomial.aeval_mul] using h
  intro r hr0 hr1
  have h := no_segment_zero_imp_bisector_positive_all
    A B hA hB hseg r hr0 hr1
  simpa [paperPointwiseBisector, A, B,
    paperDescendingDenominator_affine,
    Polynomial.aeval_add, Polynomial.aeval_mul] using h


/-- The algebraic core of the paper's convexity property, independent of
polynomial degree. -/
theorem common_positive_phase_convex
    (c a b : ℂ)
    (ha : 0 < (c/a).re) (hb : 0 < (c/b).re)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 < (c / (((1-r : ℝ) : ℂ)*a+(r : ℂ)*b)).re := by
  have hc : c ≠ 0 := by
    intro hz
    simp [hz] at ha
  have hA : a ≠ 0 := by
    intro hz
    simp [hz] at ha
  have hB : b ≠ 0 := by
    intro hz
    simp [hz] at hb
  have hInvA : 0 < (a/c).re :=
    (complex_div_re_pos_comm hc hA).mp ha
  have hInvB : 0 < (b/c).re :=
    (complex_div_re_pos_comm hc hB).mp hb
  let d : ℂ := ((1-r : ℝ) : ℂ)*a+(r : ℂ)*b
  have hlin : (d/c).re =
      (1-r)*(a/c).re+r*(b/c).re := by
    dsimp [d]
    rw [add_div, mul_div_assoc, mul_div_assoc,
      Complex.add_re, Complex.mul_re, Complex.mul_re]
    simp
  have hpos : 0 < (d/c).re := by
    rw [hlin]
    simpa [add_comm] using
      convexCoeff_pos_of_pos hInvA hInvB hr0 hr1
  have hd : d ≠ 0 := by
    intro hz
    simp [hz] at hpos
  exact (complex_div_re_pos_comm hc hd).mpr hpos

theorem common_positive_phase_convex_ne_zero
    (c a b : ℂ)
    (ha : 0 < (c/a).re) (hb : 0 < (c/b).re)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (((1-r : ℝ) : ℂ)*a+(r : ℂ)*b) ≠ 0 := by
  intro hz
  have h := common_positive_phase_convex
    c a b ha hb r hr0 hr1
  rw [hz] at h
  norm_num at h

theorem paperCommonSPR_segment_frequency
    (n : ℕ) (a b : ℕ → ℝ) (p : Polynomial ℝ)
    (ha : paperPolynomialSPR n p
      (paperDescendingDenominator n a))
    (hb : paperPolynomialSPR n p
      (paperDescendingDenominator n b)) :
    ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ ω : ℝ,
      0 < ((Polynomial.aeval (jw ω) p : ℂ) /
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n
            (fun i => (1-r)*a i+r*b i))).re := by
  intro r hr0 hr1 ω
  have hA := ha.2.2.2 ω
  have hB := hb.2.2.2 ω
  have h := common_positive_phase_convex
    (Polynomial.aeval (jw ω) p)
    (Polynomial.aeval (jw ω) (paperDescendingDenominator n a))
    (Polynomial.aeval (jw ω) (paperDescendingDenominator n b))
    hA hB r hr0 hr1
  simpa [paperDescendingDenominator_affine,
    Polynomial.aeval_add, Polynomial.aeval_mul] using h

theorem paperCommonSPR_segment_imag_ne_zero
    (n : ℕ) (a b : ℕ → ℝ) (p : Polynomial ℝ)
    (ha : paperPolynomialSPR n p
      (paperDescendingDenominator n a))
    (hb : paperPolynomialSPR n p
      (paperDescendingDenominator n b)) :
    ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ ω : ℝ,
      Polynomial.aeval (jw ω)
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i)) ≠ (0 : ℂ) := by
  intro r hr0 hr1 ω hz
  have h := paperCommonSPR_segment_frequency
    n a b p ha hb r hr0 hr1 ω
  rw [hz] at h
  norm_num at h



private theorem general_prod_map_eq_prod_occurrences
    {α β : Type*} [DecidableEq α] [CommMonoid β]
    (m : Multiset α) (f : α → β) :
    (m.map f).prod = ∏ z : m, f z := by
  rw [← m.map_univ f]
  rfl

/-- The monic root product gives a uniform lower bound at a point in the
open right half-plane whenever all roots are in the closed left half-plane. -/
theorem paperMonic_eval_norm_lower_of_roots_nonpos
    (p : Polynomial ℝ) (hp : p.Monic) (z : ℂ) (hz : 0 < z.re)
    (hroots : ∀ w : ℂ, Polynomial.aeval w p = 0 → w.re ≤ 0) :
    z.re ^ p.natDegree ≤ ‖(Polynomial.aeval z p : ℂ)‖ := by
  let P := p.map (algebraMap ℝ ℂ)
  have hmonic : P.Monic := hp.map _
  have hsplit : P.Splits (RingHom.id ℂ) := IsAlgClosed.splits P
  have hfactor (w : P.roots) : z.re ≤ ‖z - (w : ℂ)‖ := by
    have hwroot : Polynomial.aeval (w : ℂ) p = 0 := by
      have h := (Polynomial.mem_roots hmonic.ne_zero).mp
        (Multiset.coe_mem (x := w))
      simpa [P] using h
    have hw := hroots w hwroot
    have hre : z.re ≤ (z - (w : ℂ)).re := by
      simp only [Complex.sub_re]
      linarith
    exact hre.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hprod :
      (∏ w : P.roots, z.re) ≤
        ∏ w : P.roots, ‖z - (w : ℂ)‖ :=
    Finset.prod_le_prod (fun _ _ => hz.le) (fun w _ => hfactor w)
  have hcard : P.roots.card = p.natDegree := by
    simpa [P, Polynomial.natDegree_map] using
      (Polynomial.natDegree_eq_card_roots' hsplit).symm
  simp only [Finset.prod_const, Finset.card_univ, Multiset.card_coe,
    hcard] at hprod
  have hEval : P.eval z = Polynomial.aeval z p := by
    simp [P]
  rw [← hEval,
    Polynomial.eval_eq_prod_roots_sub_of_monic_of_splits_id hmonic hsplit,
    general_prod_map_eq_prod_occurrences, norm_prod]
  exact hprod

noncomputable def paperSegmentDenominator
    (n : ℕ) (a b : ℕ → ℝ) (r : ℝ) : Polynomial ℝ :=
  paperDescendingDenominator n (fun i => (1-r)*a i+r*b i)

theorem paperSegmentDenominator_eval_affine
    (n : ℕ) (a b : ℕ → ℝ) (r : ℝ) (z : ℂ) :
    Polynomial.aeval z (paperSegmentDenominator n a b r) =
      ((1-r : ℝ) : ℂ) *
          Polynomial.aeval z (paperDescendingDenominator n a) +
        (r : ℂ) *
          Polynomial.aeval z (paperDescendingDenominator n b) := by
  simp [paperSegmentDenominator,
    paperDescendingDenominator_affine, Polynomial.aeval_add,
    Polynomial.aeval_mul]

theorem paperSegmentDenominator_monic
    (n : ℕ) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1) (r : ℝ) :
    (paperSegmentDenominator n a b r).Monic := by
  apply paperDescendingDenominator_monic
  change (1-r)*a 0+r*b 0 = 1
  rw [ha0, hb0]
  ring

/-- A root with strictly positive real part persists locally when the
parameter of a monic polynomial segment changes. -/
theorem paperSegment_right_root_persists
    (n : ℕ) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (u : ℝ) (z : ℂ)
    (hzroot : Polynomial.aeval z
      (paperSegmentDenominator n a b u) = 0)
    (hzre : 0 < z.re) :
    ∀ᶠ r : ℝ in 𝓝 u,
      ∃ w : ℂ,
        Polynomial.aeval w (paperSegmentDenominator n a b r) = 0 ∧
          0 < w.re := by
  have hcont : Continuous (fun r : ℝ =>
      Polynomial.aeval z (paperSegmentDenominator n a b r)) := by
    simp only [paperSegmentDenominator_eval_affine]
    fun_prop
  have hsmall : ∀ᶠ r : ℝ in 𝓝 u,
      ‖(Polynomial.aeval z
        (paperSegmentDenominator n a b r) : ℂ)‖ <
          z.re ^ (paperSegmentDenominator n a b r).natDegree := by
    have hdeg : ∀ r : ℝ,
        (paperSegmentDenominator n a b r).natDegree = n := by
      intro r
      apply paperDescendingDenominator_natDegree_eq
      change (1-r)*a 0+r*b 0 = 1
      rw [ha0, hb0]
      ring
    have hs : ∀ᶠ r : ℝ in 𝓝 u,
        ‖(Polynomial.aeval z
          (paperSegmentDenominator n a b r) : ℂ)‖ < z.re ^ n :=
      (isOpen_lt hcont.norm continuous_const).mem_nhds (by
        simpa [hzroot] using pow_pos hzre n)
    filter_upwards [hs] with r hr
    simpa [hdeg r] using hr
  filter_upwards [hsmall] with r hr
  by_contra hnone
  have hnonpos : ∀ w : ℂ,
      Polynomial.aeval w (paperSegmentDenominator n a b r) = 0 →
        w.re ≤ 0 := by
    intro w hw
    exact le_of_not_gt (fun hwpos => hnone ⟨w, hw, hwpos⟩)
  exact (not_le_of_gt hr)
    (paperMonic_eval_norm_lower_of_roots_nonpos
      _ (paperSegmentDenominator_monic n a b ha0 hb0 r)
      z hzre hnonpos)

private theorem paperSegment_coeff_continuous
    (n : ℕ) (a b : ℕ → ℝ) (i : ℕ) :
    Continuous (fun r : ℝ =>
      ((paperSegmentDenominator n a b r).map
        (algebraMap ℝ ℂ)).coeff i) := by
  simp only [Polynomial.coeff_map, paperSegmentDenominator,
    paperDescendingDenominator_affine,
    Polynomial.coeff_add, Polynomial.coeff_C_mul]
  fun_prop

private theorem paperSegment_cauchyBound_continuous
    (n : ℕ) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    Continuous (fun r : ℝ =>
      Polynomial.cauchyBound
        ((paperSegmentDenominator n a b r).map
          (algebraMap ℝ ℂ))) := by
  have hdeg (r : ℝ) :
      ((paperSegmentDenominator n a b r).map
        (algebraMap ℝ ℂ)).natDegree = n := by
    rw [Polynomial.natDegree_map]
    apply paperDescendingDenominator_natDegree_eq
    change (1-r)*a 0+r*b 0 = 1
    rw [ha0, hb0]
    ring
  have hmonic (r : ℝ) :
      ((paperSegmentDenominator n a b r).map
        (algebraMap ℝ ℂ)).Monic :=
    (paperSegmentDenominator_monic n a b ha0 hb0 r).map _
  have hsup : Continuous (fun r : ℝ =>
      (Finset.range n).sup (fun i =>
        ‖((paperSegmentDenominator n a b r).map
          (algebraMap ℝ ℂ)).coeff i‖₊)) := by
    exact Continuous.finset_sup_apply (fun i _ =>
      (paperSegment_coeff_continuous n a b i).nnnorm)
  have heq : (fun r : ℝ =>
      Polynomial.cauchyBound
        ((paperSegmentDenominator n a b r).map
          (algebraMap ℝ ℂ))) =
      (fun r : ℝ =>
        (Finset.range n).sup (fun i =>
          ‖((paperSegmentDenominator n a b r).map
            (algebraMap ℝ ℂ)).coeff i‖₊) + 1) := by
    funext r
    simp [Polynomial.cauchyBound, hdeg r, (hmonic r).leadingCoeff]
  rw [heq]
  exact hsup.add continuous_const

private theorem paperSegment_roots_uniformly_bounded
    (n : ℕ) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (l h : ℝ) (hlh : l ≤ h) :
    ∃ B : ℝ, ∀ r : ℝ, l ≤ r → r ≤ h →
      ∀ z : ℂ,
        Polynomial.aeval z (paperSegmentDenominator n a b r) = 0 →
        ‖z‖ ≤ B := by
  let f : ℝ → NNReal := fun r =>
    Polynomial.cauchyBound
      ((paperSegmentDenominator n a b r).map
        (algebraMap ℝ ℂ))
  have hf : Continuous f :=
    paperSegment_cauchyBound_continuous n a b ha0 hb0
  obtain ⟨u, hu, humax⟩ :=
    isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.mpr hlh) hf.continuousOn
  refine ⟨(f u : ℝ), ?_⟩
  intro r hr0 hr1 z hz
  let P := (paperSegmentDenominator n a b r).map
    (algebraMap ℝ ℂ)
  have hmonic : P.Monic :=
    (paperSegmentDenominator_monic n a b ha0 hb0 r).map _
  have hroot : P.IsRoot z := by
    change P.eval z = 0
    simpa [P] using hz
  have hbound : ‖z‖₊ < f r :=
    Polynomial.IsRoot.norm_lt_cauchyBound hmonic.ne_zero hroot
  have hmax : f r ≤ f u := humax ⟨hr0, hr1⟩
  exact_mod_cast (hbound.le.trans hmax)

private theorem paperSegment_right_closed_root_parameters
    (n : ℕ) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    IsClosed {r : ℝ | r ∈ Set.Icc (-1) 2 ∧
      ∃ z : ℂ,
        Polynomial.aeval z (paperSegmentDenominator n a b r) = 0 ∧
          0 ≤ z.re} := by
  obtain ⟨B, hB⟩ :=
    paperSegment_roots_uniformly_bounded
      n a b ha0 hb0 (-1) 2 (by norm_num)
  let K : Set (ℝ × ℂ) :=
    (Set.Icc (-1) 2 ×ˢ Metric.closedBall (0 : ℂ) B) ∩
      {p | Polynomial.aeval p.2
        (paperSegmentDenominator n a b p.1) = 0 ∧
          0 ≤ p.2.re}
  have hcont : Continuous (fun p : ℝ × ℂ =>
      Polynomial.aeval p.2
        (paperSegmentDenominator n a b p.1)) := by
    simp only [paperSegmentDenominator_eval_affine]
    fun_prop
  have hclosed : IsClosed
      {p : ℝ × ℂ | Polynomial.aeval p.2
        (paperSegmentDenominator n a b p.1) = 0 ∧
          0 ≤ p.2.re} := by
    have hrecont : Continuous (fun p : ℝ × ℂ => p.2.re) := by fun_prop
    exact (isClosed_eq hcont continuous_const).inter
      (isClosed_le continuous_const hrecont)
  have hK : IsCompact K :=
    (isCompact_Icc.prod (isCompact_closedBall (0 : ℂ) B)).inter_right hclosed
  have hproj : (Prod.fst '' K) =
      {r : ℝ | r ∈ Set.Icc (-1) 2 ∧
        ∃ z : ℂ,
          Polynomial.aeval z (paperSegmentDenominator n a b r) = 0 ∧
            0 ≤ z.re} := by
    ext r
    constructor
    · rintro ⟨⟨s, z⟩, ⟨⟨hs, _⟩, hroot, hre⟩, hsr⟩
      dsimp at hsr
      subst s
      exact ⟨hs, z, hroot, hre⟩
    · rintro ⟨hr, z, hroot, hre⟩
      refine ⟨(r, z), ⟨⟨hr, ?_⟩, hroot, hre⟩, rfl⟩
      simpa [Metric.mem_closedBall] using hB r hr.1 hr.2 z hroot
  rw [← hproj]
  exact (hK.image continuous_fst).isClosed

/-- Degree-independent zero exclusion for a monic polynomial segment.
The argument uses local persistence of right-half-plane roots, compactness
of the uniformly bounded root set, and connectedness of `[0,1]`. -/
theorem paperMonicSegment_zero_exclusion
    (n : ℕ) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (ha : paperPolynomialHurwitz (paperDescendingDenominator n a))
    (hno : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ ω : ℝ,
      Polynomial.aeval (jw ω)
        (paperSegmentDenominator n a b r) ≠ (0 : ℂ)) :
    ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b r) := by
  let U : Set ℝ := {r | ∃ z : ℂ,
    Polynomial.aeval z (paperSegmentDenominator n a b r) = 0 ∧
      0 < z.re}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro r hr
    obtain ⟨z, hzroot, hzre⟩ := hr
    exact paperSegment_right_root_persists
      n a b ha0 hb0 r z hzroot hzre
  let V : Set ℝ := U ∩ Set.Ioo (-1) 2
  have hV : IsOpen V := hU.inter isOpen_Ioo
  let T : Set ℝ := {r | r ∈ Set.Icc (-1) 2 ∧
    ∃ z : ℂ,
      Polynomial.aeval z (paperSegmentDenominator n a b r) = 0 ∧
        0 ≤ z.re}
  have hT : IsClosed T :=
    paperSegment_right_closed_root_parameters
      n a b ha0 hb0
  have hVT : V ⊆ T := by
    rintro r ⟨⟨z, hroot, hzre⟩, hr⟩
    exact ⟨⟨hr.1.le, hr.2.le⟩, z, hroot, hzre.le⟩
  have hclosure : closure V ∩ Set.Icc (0 : ℝ) 1 ⊆ V := by
    rintro r ⟨hrcl, hrseg⟩
    obtain ⟨_, z, hzroot, hznonneg⟩ :=
      closure_minimal hVT hT hrcl
    have hzpos : 0 < z.re := by
      by_contra hn
      have hzre : z.re = 0 := le_antisymm (le_of_not_gt hn) hznonneg
      have hzjw : z = jw z.im := by
        apply Complex.ext <;> simp [jw, hzre]
      exact hno r hrseg.1 hrseg.2 z.im (by simpa [← hzjw] using hzroot)
    exact ⟨⟨z, hzroot, hzpos⟩,
      ⟨by linarith [hrseg.1], by linarith [hrseg.2]⟩⟩
  have hnone : (Set.Icc (0 : ℝ) 1 ∩ V).Nonempty → False := by
    intro hsome
    have hall : Set.Icc (0 : ℝ) 1 ⊆ V :=
      isPreconnected_Icc.subset_of_closure_inter_subset hV hsome hclosure
    obtain ⟨⟨z, hroot, hzpos⟩, _⟩ :=
      hall (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    have hroota : Polynomial.aeval z (paperDescendingDenominator n a) = 0 := by
      simpa [paperSegmentDenominator] using hroot
    exact ha z hzpos.le hroota
  intro r hr0 hr1 z hzre hzroot
  have hzpos : 0 < z.re := by
    by_contra hn0
    have hzrealzero : z.re = 0 := le_antisymm (le_of_not_gt hn0) hzre
    have hzjw : z = jw z.im := by
      apply Complex.ext <;> simp [jw, hzrealzero]
    exact hno r hr0 hr1 z.im (by simpa [← hzjw] using hzroot)
  apply hnone
  exact ⟨r, ⟨hr0, hr1⟩,
    ⟨⟨z, hzroot, hzpos⟩, ⟨by linarith, by linarith⟩⟩⟩



/-- The necessary implication in the paper's arbitrary-order Theorem 2. -/
theorem paperTheorem2_necessity
    (n : ℕ) (a b : ℕ → ℝ) (p : Polynomial ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (ha : paperPolynomialSPR n p
      (paperDescendingDenominator n a))
    (hb : paperPolynomialSPR n p
      (paperDescendingDenominator n b)) :
    ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i)) := by
  exact paperMonicSegment_zero_exclusion n a b ha0 hb0 ha.2.2.1
    (paperCommonSPR_segment_imag_ne_zero n a b p ha hb)

/-- The same numerator remains SPR for every member of the segment. -/
theorem paperTheorem2_commonSPR_on_segment
    (n : ℕ) (a b : ℕ → ℝ) (p : Polynomial ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (ha : paperPolynomialSPR n p
      (paperDescendingDenominator n a))
    (hb : paperPolynomialSPR n p
      (paperDescendingDenominator n b)) :
    ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialSPR n p
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i)) := by
  intro r hr0 hr1
  refine ⟨ha.1, ?_,
    paperTheorem2_necessity n a b p ha0 hb0 ha hb r hr0 hr1,
    paperCommonSPR_segment_frequency n a b p ha hb r hr0 hr1⟩
  apply paperDescendingDenominator_natDegree_eq
  change (1-r)*a 0+r*b 0 = 1
  rw [ha0, hb0]
  ring



private def crossA (t : ℝ) : ℝ :=
  t^6+21*t^5-185*t^4+473*t^3-444*t^2+230*t+8

private def crossB (t : ℝ) : ℝ :=
  t^6-12*t^5+92*t^4-501*t^3+1358*t^2-1024*t+648

private theorem crossA_pos (t : ℝ) (ht : 0 ≤ t) : 0 < crossA t := by
  by_cases h2 : t ≤ 2
  · let x : ℝ := t
    let y : ℝ := 2-t
    have hx : 0 ≤ x := ht
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hrep : 64*crossA t =
        8*y^6 + 508*x*y^5 + 644*x^2*y^4 +
        1440*x^3*y^3 + 2456*x^4*y^2 +
        1348*x^5*y + 252*x^6 := by
      dsimp [crossA, x, y]
      ring
    have hpos : 0 <
        8*y^6 + 508*x*y^5 + 644*x^2*y^4 +
        1440*x^3*y^3 + 2456*x^4*y^2 +
        1348*x^5*y + 252*x^6 := by
      by_cases hxzero : x = 0
      · have hypos : 0 < y := by dsimp [x,y] at *; linarith
        simp [hxzero]
        positivity
      · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
        positivity
    nlinarith only [hrep, hpos]
  · have h2lo : 2 ≤ t := le_of_lt (lt_of_not_ge h2)
    by_cases h4 : t ≤ 4
    · let x : ℝ := t-2
      let y : ℝ := 4-t
      have hx : 0 ≤ x := by dsimp [x]; linarith
      have hy : 0 ≤ y := by dsimp [y]; linarith
      have hrep : 64*crossA t =
          252*y^6 + 1676*x*y^5 + 4096*x^2*y^4 +
          4608*x^3*y^3 + 3588*x^4*y^2 +
          3924*x^5*y + 2336*x^6 := by
        dsimp [crossA, x, y]
        ring
      have hpos : 0 <
          252*y^6 + 1676*x*y^5 + 4096*x^2*y^4 +
          4608*x^3*y^3 + 3588*x^4*y^2 +
          3924*x^5*y + 2336*x^6 := by
        by_cases hxzero : x = 0
        · have hypos : 0 < y := by dsimp [x,y] at *; linarith
          simp [hxzero]
          positivity
        · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
          positivity
      nlinarith only [hrep, hpos]
    · let u : ℝ := t-4
      have hu : 0 ≤ u := by dsimp [u]; linarith
      have hrep : crossA t =
          u^6+45*u^5+475*u^4+2153*u^3+
          4752*u^2+5046*u+2336 := by
        dsimp [crossA,u]
        ring
      rw [hrep]
      positivity

private theorem crossB_pos (t : ℝ) (ht : 0 ≤ t) : 0 < crossB t := by
  by_cases h2 : t ≤ 2
  · let x : ℝ := t
    let y : ℝ := 2-t
    have hx : 0 ≤ x := ht
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hrep : 64*crossB t =
        648*y^6 + 1840*x*y^5 + 4912*x^2*y^4 +
        10200*x^3*y^3 + 11280*x^4*y^2 +
        5912*x^5*y + 1176*x^6 := by
      dsimp [crossB, x, y]
      ring
    have hpos : 0 <
        648*y^6 + 1840*x*y^5 + 4912*x^2*y^4 +
        10200*x^3*y^3 + 11280*x^4*y^2 +
        5912*x^5*y + 1176*x^6 := by
      by_cases hxzero : x = 0
      · have hypos : 0 < y := by dsimp [x,y] at *; linarith
        simp [hxzero]
        positivity
      · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
        positivity
    nlinarith only [hrep, hpos]
  · have h2lo : 2 ≤ t := le_of_lt (lt_of_not_ge h2)
    by_cases h4 : t ≤ 4
    · let x : ℝ := t-2
      let y : ℝ := 4-t
      have hx : 0 ≤ x := by dsimp [x]; linarith
      have hy : 0 ≤ y := by dsimp [y]; linarith
      have hrep : 64*crossB t =
          1176*y^6 + 8200*x*y^5 + 22720*x^2*y^4 +
          31720*x^3*y^3 + 23712*x^4*y^2 +
          9200*x^5*y + 1576*x^6 := by
        dsimp [crossB, x, y]
        ring
      have hpos : 0 <
          1176*y^6 + 8200*x*y^5 + 22720*x^2*y^4 +
          31720*x^3*y^3 + 23712*x^4*y^2 +
          9200*x^5*y + 1576*x^6 := by
        by_cases hxzero : x = 0
        · have hypos : 0 < y := by dsimp [x,y] at *; linarith
          simp [hxzero]
          positivity
        · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
          positivity
      nlinarith only [hrep, hpos]
    · let u : ℝ := t-4
      have hu : 0 ≤ u := by dsimp [u]; linarith
      have hrep : crossB t =
          u^6+12*u^5+92*u^4+331*u^3+
          338*u^2+128*u+1576 := by
        dsimp [crossB,u]
        ring
      rw [hrep]
      positivity

/-- A concrete common numerator for the stable segment that refutes the
paper's common-ellipse-region lemma. -/
def gramCounterExplicitNumerator : MonicSextic :=
  ⟨12, 36, 100, 100, 75, 8⟩

private theorem gramCounterExplicit_crossA (t : ℝ) :
    vectorCross binomialSextic
      (monicNumeratorVector gramCounterExplicitNumerator) t =
        crossA t := by
  rw [vectorCross_monic]
  dsimp [binomialSextic, gramCounterExplicitNumerator,
    MonicSextic.evenPart, MonicSextic.oddPart, crossA]
  ring

private theorem gramCounterExplicit_crossB (t : ℝ) :
    vectorCross gramCounterSimpleB
      (monicNumeratorVector gramCounterExplicitNumerator) t =
        crossB t := by
  rw [vectorCross_monic]
  dsimp [gramCounterSimpleB, gramCounterExplicitNumerator,
    MonicSextic.evenPart, MonicSextic.oddPart, crossB]
  ring

theorem gramCounterExplicit_commonSPR :
    binomialSextic.SPRFor gramCounterExplicitNumerator ∧
      gramCounterSimpleB.SPRFor gramCounterExplicitNumerator := by
  have hB : gramCounterSimpleB.Hurwitz := by
    simpa using gramCounterSimple_segment_hurwitz 1
      (by norm_num) (by norm_num)
  constructor
  · refine ⟨binomialSextic_hurwitz, ?_⟩
    intro ω
    rw [re_monicSextic_div, gramCounterExplicit_crossA]
    exact div_pos (crossA_pos (ω^2) (sq_nonneg ω))
      (Complex.normSq_pos.mpr
        (MonicSextic.evalJW_ne_zero binomialSextic_hurwitz ω))
  · refine ⟨hB, ?_⟩
    intro ω
    rw [re_monicSextic_div, gramCounterExplicit_crossB]
    exact div_pos (crossB_pos (ω^2) (sq_nonneg ω))
      (Complex.normSq_pos.mpr
        (MonicSextic.evalJW_ne_zero hB ω))

theorem gramCounterExplicit_SPR_on_segment :
    ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      (binomialSextic.convex gramCounterSimpleB r).SPRFor
        gramCounterExplicitNumerator := by
  have hpos := common_frequency_numerator_on_segment
    binomialSextic gramCounterSimpleB
    (fun ω => gramCounterExplicitNumerator.evalJW ω)
    gramCounterExplicit_commonSPR.1.1
    gramCounterExplicit_commonSPR.2.1
    gramCounterExplicit_commonSPR.1.2
    gramCounterExplicit_commonSPR.2.2
  intro r hr0 hr1
  refine ⟨gramCounterSimple_segment_hurwitz r hr0 hr1, ?_⟩
  exact hpos.2 r hr0 hr1



theorem ratio_not_nonpositive_imp_no_segment_zero
    (a b : ℂ) (ha : a ≠ 0) (hphase : ¬ b/a ≤ 0) :
    ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      ((1-r : ℝ) : ℂ)*a+(r : ℂ)*b ≠ 0 := by
  intro r hr0 hr1 hz
  have hrpos : 0 < r := by
    by_contra hnot
    have hrzero : r = 0 := le_antisymm (le_of_not_gt hnot) hr0
    subst r
    exact ha (by simpa using hz)
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hrpos
  have hdiv : b/a = -((((1-r)/r : ℝ) : ℂ)) := by
    field_simp [ha, hrC]
    push_cast at hz ⊢
    linear_combination hz
  have hnonneg : 0 ≤ (1-r)/r :=
    div_nonneg (by linarith only [hr1]) hr0
  have hnonpos : -((((1-r)/r : ℝ) : ℂ)) ≤ 0 := by
    exact Complex.nonpos_iff.mpr ⟨by simp [hnonneg], by simp⟩
  exact hphase (hdiv ▸ hnonpos)

theorem no_segment_zero_iff_ratio_not_nonpositive
    (a b : ℂ) (ha : a ≠ 0) :
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      ((1-r : ℝ) : ℂ)*a+(r : ℂ)*b ≠ 0) ↔
      ¬ b/a ≤ 0 := by
  constructor
  · exact no_segment_zero_imp_ratio_not_nonpositive a b ha
  · exact ratio_not_nonpositive_imp_no_segment_zero a b ha

/-- A frequency-domain characterization of Hurwitz stability for a monic
polynomial segment, independent of the paper's ellipse regions. -/
theorem paperStableSegment_iff_phase_avoidance
    (n : ℕ) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (ha : paperPolynomialHurwitz (paperDescendingDenominator n a)) :
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i))) ↔
    (∀ ω : ℝ,
      ¬ (Polynomial.aeval (jw ω) (paperDescendingDenominator n b) /
        Polynomial.aeval (jw ω) (paperDescendingDenominator n a) : ℂ) ≤ 0) := by
  constructor
  · intro hstable ω
    let A : ℂ := Polynomial.aeval (jw ω) (paperDescendingDenominator n a)
    let B : ℂ := Polynomial.aeval (jw ω) (paperDescendingDenominator n b)
    have hA : A ≠ 0 :=
      paperPolynomialHurwitz_imag_ne_zero _ ha ω
    have hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        ((1-r : ℝ) : ℂ)*A+(r : ℂ)*B ≠ 0 := by
      intro r hr0 hr1
      have h := paperPolynomialHurwitz_imag_ne_zero _
        (hstable r hr0 hr1) ω
      rw [paperDescendingDenominator_affine] at h
      simpa [A, B, Polynomial.aeval_add,
        Polynomial.aeval_mul] using h
    exact no_segment_zero_imp_ratio_not_nonpositive
      A B hA hsegment
  · intro hphase
    apply paperMonicSegment_zero_exclusion n a b ha0 hb0 ha
    intro r hr0 hr1 ω
    let A : ℂ := Polynomial.aeval (jw ω) (paperDescendingDenominator n a)
    let B : ℂ := Polynomial.aeval (jw ω) (paperDescendingDenominator n b)
    have hA : A ≠ 0 :=
      paperPolynomialHurwitz_imag_ne_zero _ ha ω
    have hsegment := ratio_not_nonpositive_imp_no_segment_zero
      A B hA (hphase ω) r hr0 hr1
    simpa [A, B, paperSegmentDenominator,
      paperDescendingDenominator_affine,
      Polynomial.aeval_add, Polynomial.aeval_mul] using hsegment

theorem paperPhaseAvoidance_pointwise_bisector
    (n : ℕ) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (ha : paperPolynomialHurwitz (paperDescendingDenominator n a))
    (hphase : ∀ ω : ℝ,
      ¬ (Polynomial.aeval (jw ω) (paperDescendingDenominator n b) /
        Polynomial.aeval (jw ω) (paperDescendingDenominator n a) : ℂ) ≤ 0) :
    Continuous (paperPointwiseBisector n a b) ∧
      ∀ ω r : ℝ, 0 ≤ r → r ≤ 1 →
        0 < ((paperPointwiseBisector n a b ω) /
          Polynomial.aeval (jw ω)
            (paperDescendingDenominator n
              (fun i => (1-r)*a i+r*b i))).re := by
  have hstable :=
    (paperStableSegment_iff_phase_avoidance
      n a b ha0 hb0 ha).2 hphase
  exact ⟨paperPointwiseBisector_continuous n a b,
    fun ω r hr0 hr1 =>
      paperStableSegment_pointwise_bisector_positive_all
        n a b hstable ω r hr0 hr1⟩



theorem ratio_not_nonpositive_iff_dot_or_det
    (a b : ℂ) (ha : a ≠ 0) :
    (¬ b/a ≤ 0) ↔
      (b.im*a.re-b.re*a.im ≠ 0 ∨
        0 < b.re*a.re+b.im*a.im) := by
  let dot : ℝ := b.re*a.re+b.im*a.im
  let det : ℝ := b.im*a.re-b.re*a.im
  have hnorm : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha
  have hre : (b/a).re = dot/Complex.normSq a := by
    rw [Complex.div_re]
    dsimp [dot]
    ring
  have him : (b/a).im = det/Complex.normSq a := by
    rw [Complex.div_im]
    dsimp [det]
    ring
  have hdot : 0 < (b/a).re ↔ 0 < dot := by
    rw [hre]
    exact div_pos_iff_of_pos_right hnorm
  have hdet : (b/a).im = 0 ↔ det = 0 := by
    rw [him]
    simp [hnorm.ne']
  change (¬ b/a ≤ 0) ↔ (det ≠ 0 ∨ 0 < dot)
  rw [Complex.nonpos_iff]
  constructor
  · intro h
    by_cases hi : det = 0
    · right
      have hIm : (b/a).im = 0 := hdet.mpr hi
      have hRe : 0 < (b/a).re := lt_of_not_ge (fun hle => h ⟨hle, hIm⟩)
      exact hdot.mp hRe
    · exact Or.inl hi
  · intro h hnonpos
    rcases h with hi | hp
    · exact hi (hdet.mp hnonpos.2)
    · have hnot : ¬ 0 < dot := by
        intro hd
        exact (not_lt_of_ge hnonpos.1) (hdot.mpr hd)
      exact hnot hp

noncomputable def paperFrequencyDot
    (n : ℕ) (a b : ℕ → ℝ) (ω : ℝ) : ℝ :=
  let A : ℂ := Polynomial.aeval (jw ω) (paperDescendingDenominator n a)
  let B : ℂ := Polynomial.aeval (jw ω) (paperDescendingDenominator n b)
  B.re*A.re+B.im*A.im

noncomputable def paperFrequencyDet
    (n : ℕ) (a b : ℕ → ℝ) (ω : ℝ) : ℝ :=
  let A : ℂ := Polynomial.aeval (jw ω) (paperDescendingDenominator n a)
  let B : ℂ := Polynomial.aeval (jw ω) (paperDescendingDenominator n b)
  B.im*A.re-B.re*A.im

/-- An algebraic frequency test for Hurwitz stability of a monic segment:
at each frequency either the endpoint values have nonzero oriented area, or
their real inner product is positive. -/
theorem paperStableSegment_iff_frequency_dot_or_det
    (n : ℕ) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (ha : paperPolynomialHurwitz (paperDescendingDenominator n a)) :
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i))) ↔
    (∀ ω : ℝ,
      paperFrequencyDet n a b ω ≠ 0 ∨
        0 < paperFrequencyDot n a b ω) := by
  rw [paperStableSegment_iff_phase_avoidance n a b ha0 hb0 ha]
  constructor
  · intro h ω
    have hA : Polynomial.aeval (jw ω)
        (paperDescendingDenominator n a) ≠ (0 : ℂ) :=
      paperPolynomialHurwitz_imag_ne_zero _ ha ω
    exact (ratio_not_nonpositive_iff_dot_or_det
      _ _ hA).mp (h ω)
  · intro h ω
    have hA : Polynomial.aeval (jw ω)
        (paperDescendingDenominator n a) ≠ (0 : ℂ) :=
      paperPolynomialHurwitz_imag_ne_zero _ ha ω
    exact (ratio_not_nonpositive_iff_dot_or_det
      _ _ hA).mpr (h ω)



/-- Exact algebraic test for a fixed degree-`n` numerator, after the paper's
coefficient convolution and degree-raising identity. -/
theorem paperSPR_iff_cross_positive
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (ha0 : a 0 = 1)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a)) :
    paperPolynomialSPR n
      (paperDescendingNumerator n x + Polynomial.C ε * Polynomial.X^n)
      (paperDescendingDenominator n a) ↔
      ∀ t : ℝ, 0 ≤ t →
        0 < (paperGeneralCrossPolynomial n a x).eval t +
          ε * (paperRaiseCorrection n a).eval t := by
  have hden (ω : ℝ) :
      0 < Complex.normSq
        (Polynomial.aeval (jw ω) (paperDescendingDenominator n a) : ℂ) :=
    Complex.normSq_pos.mpr
      (paperPolynomialHurwitz_imag_ne_zero _ hstable ω)
  constructor
  · intro hSPR t ht
    let ω : ℝ := Real.sqrt t
    have hω : ω^2 = t := Real.sq_sqrt ht
    have hpos := hSPR.2.2.2 ω
    rw [paperDescending_degree_raised_re n hn a x ε ω,
      hω] at hpos
    exact (div_pos_iff_of_pos_right (hden ω)).mp hpos
  · intro hcross
    refine ⟨paperDescendingNumerator_raise_natDegree_eq n x ε hε,
      paperDescendingDenominator_natDegree_eq n a ha0,
      hstable, ?_⟩
    intro ω
    rw [paperDescending_degree_raised_re n hn a x ε ω]
    exact (div_pos_iff_of_pos_right (hden ω)).mpr
      (hcross (ω^2) (sq_nonneg ω))

theorem paperCommonSPR_iff_pair_cross_positive
    (n : ℕ) (hn : 0 < n) (a b x : ℕ → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    (paperPolynomialSPR n
        (paperDescendingNumerator n x + Polynomial.C ε * Polynomial.X^n)
        (paperDescendingDenominator n a) ∧
      paperPolynomialSPR n
        (paperDescendingNumerator n x + Polynomial.C ε * Polynomial.X^n)
        (paperDescendingDenominator n b)) ↔
      ((∀ t : ℝ, 0 ≤ t →
          0 < (paperGeneralCrossPolynomial n a x).eval t +
            ε * (paperRaiseCorrection n a).eval t) ∧
       (∀ t : ℝ, 0 ≤ t →
          0 < (paperGeneralCrossPolynomial n b x).eval t +
            ε * (paperRaiseCorrection n b).eval t)) := by
  have hA := paperSPR_iff_cross_positive
    n hn a x ε hε ha0 hstableA
  have hB := paperSPR_iff_cross_positive
    n hn b x ε hε hb0 hstableB
  exact and_congr hA hB

/-- Repaired arbitrary-order sufficiency, reduced to simultaneous positivity
of two explicit degree-`n` real coefficient polynomials. -/
theorem paperTheorem2_sufficiency_of_cross_feasible
    (n : ℕ) (hn : 0 < n) (a b x : ℕ → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstable : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i)))
    (hA : ∀ t : ℝ, 0 ≤ t →
      0 < (paperGeneralCrossPolynomial n a x).eval t +
        ε * (paperRaiseCorrection n a).eval t)
    (hB : ∀ t : ℝ, 0 ≤ t →
      0 < (paperGeneralCrossPolynomial n b x).eval t +
        ε * (paperRaiseCorrection n b).eval t) :
    ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialSPR n
        (paperDescendingNumerator n x + Polynomial.C ε * Polynomial.X^n)
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i)) := by
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa using hstable 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa using hstable 1 (by norm_num) (by norm_num)
  have hpair :=
    (paperCommonSPR_iff_pair_cross_positive
      n hn a b x ε hε ha0 hb0 hstableA hstableB).mpr
      ⟨hA,hB⟩
  exact paperTheorem2_commonSPR_on_segment n a b
    (paperDescendingNumerator n x + Polynomial.C ε * Polynomial.X^n)
    ha0 hb0 hpair.1 hpair.2

noncomputable def paperNumeratorCoordinates
    (n : ℕ) (p : Polynomial ℝ) (i : ℕ) : ℝ :=
  if i < n then p.coeff (n-1-i) else 0

theorem paperNumerator_coordinates_repr
    (n : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ n) :
    p = paperDescendingNumerator n
          (paperNumeratorCoordinates n p) +
        Polynomial.C (p.coeff n) * Polynomial.X^n := by
  ext m
  rw [Polynomial.coeff_add, paperDescendingNumerator_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hm : m < n
  · have hidx : n-1-m < n := by omega
    have hrev : n-1-(n-1-m) = m := by omega
    have hmn : m ≠ n := by omega
    simp [hm, hmn, paperNumeratorCoordinates, hidx, hrev]
  · by_cases hmn : m = n
    · subst m
      simp
    · have hgt : n < m := by omega
      have hcoeff : p.coeff m = 0 :=
        (Polynomial.natDegree_le_iff_coeff_eq_zero.mp hp) m hgt
      simp [hm, hmn, hcoeff]

theorem polynomial_leadingCoeff_pos_of_pos_on_nonneg
    (p : Polynomial ℝ)
    (hdeg : 0 < p.degree)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 < p.eval t) :
    0 < p.leadingCoeff := by
  by_contra hnot
  have hlead : p.leadingCoeff ≤ 0 := le_of_not_gt hnot
  have htend : Filter.Tendsto (fun t : ℝ => p.eval t)
      Filter.atTop Filter.atBot :=
    p.tendsto_atBot_of_leadingCoeff_nonpos hdeg hlead
  have hev : ∀ᶠ t : ℝ in Filter.atTop, p.eval t ≤ -1 :=
    (Filter.tendsto_atBot.1 htend) (-1)
  obtain ⟨t, hneg, ht⟩ :=
    (hev.and (Filter.eventually_ge_atTop (0 : ℝ))).exists
  linarith only [hneg, hpos t ht]

noncomputable def paperRaisedCrossPolynomial
    (n : ℕ) (a x : ℕ → ℝ) (ε : ℝ) : Polynomial ℝ :=
  paperGeneralCrossPolynomial n a x +
    Polynomial.C ε * paperRaiseCorrection n a

theorem paperRaisedCrossPolynomial_top_coeff
    (n : ℕ) (a x : ℕ → ℝ) (ε : ℝ)
    (ha0 : a 0 = 1) :
    (paperRaisedCrossPolynomial n a x ε).coeff n = ε := by
  rw [paperRaisedCrossPolynomial,
    Polynomial.coeff_add, paperGeneralCrossPolynomial_coeff,
    if_neg (by omega : ¬ n < n), Polynomial.coeff_C_mul,
    paperRaiseCorrection_coeff, if_pos le_rfl,
    paperRaiseProduct_top_coeff n a ha0]
  rw [← pow_add, show n+n=2*n by omega, pow_mul]
  norm_num

theorem paperRaisedCrossPolynomial_natDegree_le
    (n : ℕ) (a x : ℕ → ℝ) (ε : ℝ) :
    (paperRaisedCrossPolynomial n a x ε).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [paperRaisedCrossPolynomial,
    Polynomial.coeff_add, paperGeneralCrossPolynomial_coeff,
    if_neg (by omega : ¬ m < n), Polynomial.coeff_C_mul,
    paperRaiseCorrection_coeff, if_neg (by omega : ¬ m ≤ n)]
  ring

theorem paperRaisedCrossPolynomial_natDegree_eq
    (n : ℕ) (a x : ℕ → ℝ) (ε : ℝ)
    (ha0 : a 0 = 1) (hε : ε ≠ 0) :
    (paperRaisedCrossPolynomial n a x ε).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (paperRaisedCrossPolynomial_natDegree_le n a x ε)
  rw [paperRaisedCrossPolynomial_top_coeff n a x ε ha0]
  exact hε

theorem paperRaisedCrossPolynomial_leadingCoeff
    (n : ℕ) (a x : ℕ → ℝ) (ε : ℝ)
    (ha0 : a 0 = 1) (hε : ε ≠ 0) :
    (paperRaisedCrossPolynomial n a x ε).leadingCoeff = ε := by
  rw [Polynomial.leadingCoeff,
    paperRaisedCrossPolynomial_natDegree_eq n a x ε ha0 hε,
    paperRaisedCrossPolynomial_top_coeff n a x ε ha0]

theorem paperRaisedSPR_epsilon_pos
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) (ε : ℝ)
    (ha0 : a 0 = 1) (hεne : ε ≠ 0)
    (hSPR : paperPolynomialSPR n
      (paperDescendingNumerator n x + Polynomial.C ε * Polynomial.X^n)
      (paperDescendingDenominator n a)) :
    0 < ε := by
  let F := paperRaisedCrossPolynomial n a x ε
  have hFpos : ∀ t : ℝ, 0 ≤ t → 0 < F.eval t := by
    intro t ht
    let ω : ℝ := Real.sqrt t
    have hω : ω^2 = t := Real.sq_sqrt ht
    have hq := hSPR.2.2.2 ω
    rw [paperDescending_degree_raised_re n hn a x ε ω,
      hω] at hq
    have hden : 0 < Complex.normSq
        (Polynomial.aeval (jw ω)
          (paperDescendingDenominator n a) : ℂ) :=
      Complex.normSq_pos.mpr
        (paperPolynomialHurwitz_imag_ne_zero _ hSPR.2.2.1 ω)
    have hnum := (div_pos_iff_of_pos_right hden).mp hq
    simpa [F, paperRaisedCrossPolynomial] using hnum
  have hnat : F.natDegree = n :=
    paperRaisedCrossPolynomial_natDegree_eq
      n a x ε ha0 hεne
  have hdegree : 0 < F.degree := by
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    rw [hnat]
    exact hn
  have hlead := polynomial_leadingCoeff_pos_of_pos_on_nonneg
    F hdegree hFpos
  simpa [F, paperRaisedCrossPolynomial_leadingCoeff
    n a x ε ha0 hεne] using hlead

theorem paperSPR_top_coeff_pos
    (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (p : Polynomial ℝ) (ha0 : a 0 = 1)
    (hSPR : paperPolynomialSPR n p
      (paperDescendingDenominator n a)) :
    0 < p.coeff n := by
  have hpne : p ≠ 0 := by
    intro hp0
    have hzero : n = 0 := by simpa [hp0] using hSPR.1.symm
    omega
  have hcoeff : p.coeff n ≠ 0 := by
    rw [←hSPR.1, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hpne
  have hrepr := paperNumerator_coordinates_repr
    n p hSPR.1.le
  rw [hrepr] at hSPR
  exact paperRaisedSPR_epsilon_pos
    n hn a (paperNumeratorCoordinates n p)
    (p.coeff n) ha0 hcoeff hSPR

/-- For fixed Hurwitz endpoints, common SPR synthesis is exactly the
finite-dimensional feasibility of two positive coefficient polynomials. -/
theorem paperCommonSPR_exists_iff_cross_feasible
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    (∃ p : Polynomial ℝ,
      paperPolynomialSPR n p
        (paperDescendingDenominator n a) ∧
      paperPolynomialSPR n p
        (paperDescendingDenominator n b)) ↔
    (∃ x : ℕ → ℝ, ∃ ε : ℝ, 0 < ε ∧
      (∀ t : ℝ, 0 ≤ t →
        0 < (paperGeneralCrossPolynomial n a x).eval t +
          ε * (paperRaiseCorrection n a).eval t) ∧
      (∀ t : ℝ, 0 ≤ t →
        0 < (paperGeneralCrossPolynomial n b x).eval t +
          ε * (paperRaiseCorrection n b).eval t)) := by
  constructor
  · rintro ⟨p, hA, hB⟩
    have hε : 0 < p.coeff n :=
      paperSPR_top_coeff_pos n hn a p ha0 hA
    have hrepr := paperNumerator_coordinates_repr n p hA.1.le
    rw [hrepr] at hA hB
    have hcross :=
      (paperCommonSPR_iff_pair_cross_positive
        n hn a b (paperNumeratorCoordinates n p)
        (p.coeff n) hε ha0 hb0 hstableA hstableB).mp
        ⟨hA, hB⟩
    exact ⟨paperNumeratorCoordinates n p,
      p.coeff n, hε, hcross.1, hcross.2⟩
  · rintro ⟨x, ε, hε, hA, hB⟩
    refine ⟨paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n, ?_⟩
    exact (paperCommonSPR_iff_pair_cross_positive
      n hn a b x ε hε ha0 hb0 hstableA hstableB).mpr
      ⟨hA,hB⟩



theorem paperGeneralCrossPolynomial_zero
    (n : ℕ) (a : ℕ → ℝ) :
    paperGeneralCrossPolynomial n a (fun _ => 0) = 0 := by
  ext j
  rw [paperGeneralCrossPolynomial_coeff]
  by_cases hj : j < n
  · simp [hj, paperGeneralCoefficient, paperPaddedNumerator]
  · simp [hj]

theorem paperGeneralCrossPolynomial_smul
    (n : ℕ) (a x : ℕ → ℝ) (c : ℝ) :
    paperGeneralCrossPolynomial n a (fun i => c*x i) =
      Polynomial.C c * paperGeneralCrossPolynomial n a x := by
  have h := paperGeneralCrossPolynomial_add_smul_numerator
    n a (fun _ => 0) x c
  simpa [paperGeneralCrossPolynomial_zero] using h

theorem paperCross_normalize_positive
    (n : ℕ) (a x : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hcross : ∀ t : ℝ, 0 ≤ t →
      0 < (paperGeneralCrossPolynomial n a x).eval t +
        ε * (paperRaiseCorrection n a).eval t) :
    ∀ t : ℝ, 0 ≤ t →
      0 < (paperGeneralCrossPolynomial n a
        (fun i => x i/ε)).eval t +
          (paperRaiseCorrection n a).eval t := by
  intro t ht
  have hfun : (fun i => x i/ε) = (fun i => (1/ε)*x i) := by
    funext i
    ring
  rw [hfun, paperGeneralCrossPolynomial_smul,
    Polynomial.eval_mul]
  simp only [Polynomial.eval_C]
  have hpos := div_pos (hcross t ht) hε
  convert hpos using 1 <;> field_simp [ne_of_gt hε]; ring

/-- Common SPR synthesis is equivalent to a monic degree-`n` numerator
feasibility problem, with no free leading coefficient. -/
theorem paperCommonSPR_exists_iff_monic_cross_feasible
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    (∃ p : Polynomial ℝ,
      paperPolynomialSPR n p
        (paperDescendingDenominator n a) ∧
      paperPolynomialSPR n p
        (paperDescendingDenominator n b)) ↔
    (∃ x : ℕ → ℝ,
      (∀ t : ℝ, 0 ≤ t →
        0 < (paperGeneralCrossPolynomial n a x).eval t +
          (paperRaiseCorrection n a).eval t) ∧
      (∀ t : ℝ, 0 ≤ t →
        0 < (paperGeneralCrossPolynomial n b x).eval t +
          (paperRaiseCorrection n b).eval t)) := by
  rw [paperCommonSPR_exists_iff_cross_feasible
    n hn a b ha0 hb0 hstableA hstableB]
  constructor
  · rintro ⟨x, ε, hε, hA, hB⟩
    exact ⟨fun i => x i/ε,
      paperCross_normalize_positive n a x ε hε hA,
      paperCross_normalize_positive n b x ε hε hB⟩
  · rintro ⟨x, hA, hB⟩
    refine ⟨x, 1, by norm_num, ?_, ?_⟩
    · simpa using hA
    · simpa using hB



/-- The sixth-order instance of the missing existence step in the paper's
arbitrary-order proof, expressed with a monic common numerator. -/
theorem sixth_order_monic_cross_feasible_of_stable_segment
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator 6
          (fun i => (1-r)*a i+r*b i))) :
    ∃ x : ℕ → ℝ,
      (∀ t : ℝ, 0 ≤ t →
        0 < (paperGeneralCrossPolynomial 6 a x).eval t +
          (paperRaiseCorrection 6 a).eval t) ∧
      (∀ t : ℝ, 0 ≤ t →
        0 < (paperGeneralCrossPolynomial 6 b x).eval t +
          (paperRaiseCorrection 6 b).eval t) := by
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator 6 a) := by
    simpa using hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator 6 b) := by
    simpa using hsegment 1 (by norm_num) (by norm_num)
  obtain ⟨p, hp⟩ :=
    (sixth_order_paper_coefficient_sequence a b ha0 hb0).mp hsegment
  apply (paperCommonSPR_exists_iff_monic_cross_feasible
    6 (by norm_num) a b ha0 hb0 hstableA hstableB).mp
  exact ⟨p,
    by simpa using hp 0 (by norm_num) (by norm_num),
    by simpa using hp 1 (by norm_num) (by norm_num)⟩

/-- An exact sextic coefficient criterion: endpoint Hurwitz stability and
simultaneous positivity of two monic cross polynomials characterize the
stability of the whole segment. -/
theorem sixth_order_stable_segment_iff_monic_cross_feasible
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator 6
          (fun i => (1-r)*a i+r*b i))) ↔
    paperPolynomialHurwitz (paperDescendingDenominator 6 a) ∧
    paperPolynomialHurwitz (paperDescendingDenominator 6 b) ∧
    ∃ x : ℕ → ℝ,
      (∀ t : ℝ, 0 ≤ t →
        0 < (paperGeneralCrossPolynomial 6 a x).eval t +
          (paperRaiseCorrection 6 a).eval t) ∧
      (∀ t : ℝ, 0 ≤ t →
        0 < (paperGeneralCrossPolynomial 6 b x).eval t +
          (paperRaiseCorrection 6 b).eval t) := by
  constructor
  · intro hsegment
    refine ⟨?_, ?_, sixth_order_monic_cross_feasible_of_stable_segment
      a b ha0 hb0 hsegment⟩
    · simpa using hsegment 0 (by norm_num) (by norm_num)
    · simpa using hsegment 1 (by norm_num) (by norm_num)
  · rintro ⟨hstableA, hstableB, x, hA, hB⟩
    obtain ⟨p, hpA, hpB⟩ :=
      (paperCommonSPR_exists_iff_monic_cross_feasible
        6 (by norm_num) a b ha0 hb0 hstableA hstableB).mpr
        ⟨x, hA, hB⟩
    exact paperTheorem2_necessity 6 a b p ha0 hb0 hpA hpB



/-- Degree-`n` homogenization of a real polynomial on the half-line. -/
def paperHomogenizedPolynomial (n : ℕ) (p : Polynomial ℝ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), p.coeff j * u^j * (1-u)^(n-j)

theorem paperHomogenizedPolynomial_eq
    (n : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ n)
    (u : ℝ) (hu : u ≠ 1) :
    paperHomogenizedPolynomial n p u =
      (1-u)^n * p.eval (u/(1-u)) := by
  have hdegree : p.natDegree < n+1 := by omega
  rw [Polynomial.eval_eq_sum_range' hdegree]
  rw [paperHomogenizedPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hne : 1-u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have hfactor : (1-u) * (u/(1-u)) = u := by field_simp
  have hpow : (1-u)^j * (u/(1-u))^j = u^j := by
    rw [← mul_pow, hfactor]
  calc
    p.coeff j * u^j * (1-u)^(n-j) =
        (1-u)^(n-j) * p.coeff j * u^j := by ring
    _ = (1-u)^(n-j) * (1-u)^j *
        (p.coeff j * (u/(1-u))^j) := by
          rw [← hpow]
          ring
    _ = (1-u)^n * (p.coeff j * (u/(1-u))^j) := by
          rw [← pow_add, Nat.sub_add_cancel hjle]

theorem paperHomogenizedPolynomial_one
    (n : ℕ) (p : Polynomial ℝ) :
    paperHomogenizedPolynomial n p 1 = p.coeff n := by
  rw [paperHomogenizedPolynomial]
  rw [Finset.sum_eq_single n]
  · simp
  · intro j hj hne
    have hjlt : j < n := by
      have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      omega
    have hpos : n-j ≠ 0 := by omega
    simp [hpos]
  · simp

theorem paperHomogenizedPolynomial_pos_iff
    (n : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ n)
    (hlead : 0 < p.coeff n) :
    (∀ t : ℝ, 0 ≤ t → 0 < p.eval t) ↔
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        0 < paperHomogenizedPolynomial n p u) := by
  constructor
  · intro hpos u hu0 hu1
    by_cases hu : u = 1
    · subst u
      simpa [paperHomogenizedPolynomial_one] using hlead
    · have hu' : u < 1 := lt_of_le_of_ne hu1 hu
      have hden : 0 < 1-u := sub_pos.mpr hu'
      rw [paperHomogenizedPolynomial_eq n p hp u hu]
      exact mul_pos (pow_pos hden n) (hpos _ (div_nonneg hu0 hden.le))
  · intro hcompact t ht
    let u : ℝ := t/(1+t)
    have hden : 0 < 1+t := by linarith
    have hu0 : 0 ≤ u := div_nonneg ht hden.le
    have hu1 : u < 1 := by
      dsimp [u]
      rw [div_lt_one hden]
      linarith
    have hfactor : u/(1-u) = t := by
      dsimp [u]
      field_simp
    have h := hcompact u hu0 hu1.le
    rw [paperHomogenizedPolynomial_eq n p hp u hu1.ne, hfactor] at h
    exact (mul_pos_iff_of_pos_left (pow_pos (sub_pos.mpr hu1) n)).mp h

theorem paperHomogenizedPolynomial_continuous
    (n : ℕ) (p : Polynomial ℝ) :
    Continuous (paperHomogenizedPolynomial n p) := by
  unfold paperHomogenizedPolynomial
  fun_prop

/-- Compactified cross polynomial for a monic degree-`n` numerator. -/
noncomputable def paperCompactRaisedCross (n : ℕ) (a x : ℕ → ℝ) (u : ℝ) : ℝ :=
  paperHomogenizedPolynomial n (paperRaisedCrossPolynomial n a x 1) u

theorem paperCompactRaisedCross_one
    (n : ℕ) (a x : ℕ → ℝ) (ha0 : a 0 = 1) :
    paperCompactRaisedCross n a x 1 = 1 := by
  rw [paperCompactRaisedCross, paperHomogenizedPolynomial_one]
  exact paperRaisedCrossPolynomial_top_coeff n a x 1 ha0

theorem paperCompactRaisedCross_continuous
    (n : ℕ) (a x : ℕ → ℝ) :
    Continuous (paperCompactRaisedCross n a x) :=
  paperHomogenizedPolynomial_continuous n _

theorem paperRaisedCross_positive_iff_compact
    (n : ℕ) (a x : ℕ → ℝ) (ha0 : a 0 = 1) :
    (∀ t : ℝ, 0 ≤ t →
      0 < (paperGeneralCrossPolynomial n a x).eval t +
        (paperRaiseCorrection n a).eval t) ↔
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      0 < paperCompactRaisedCross n a x u) := by
  have hlead : 0 < (paperRaisedCrossPolynomial n a x 1).coeff n := by
    rw [paperRaisedCrossPolynomial_top_coeff n a x 1 ha0]
    norm_num
  have h := paperHomogenizedPolynomial_pos_iff
    n (paperRaisedCrossPolynomial n a x 1)
    (paperRaisedCrossPolynomial_natDegree_le n a x 1) hlead
  simpa [paperCompactRaisedCross, paperRaisedCrossPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul] using h

/-- Common SPR synthesis is equivalently strict positivity on a compact
frequency interval.  At `u = 1` positivity is automatic from monicity. -/
theorem paperCommonSPR_exists_iff_compact_cross_feasible
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    (∃ p : Polynomial ℝ,
      paperPolynomialSPR n p
        (paperDescendingDenominator n a) ∧
      paperPolynomialSPR n p
        (paperDescendingDenominator n b)) ↔
    (∃ x : ℕ → ℝ,
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        0 < paperCompactRaisedCross n a x u) ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        0 < paperCompactRaisedCross n b x u)) := by
  rw [paperCommonSPR_exists_iff_monic_cross_feasible
    n hn a b ha0 hb0 hstableA hstableB]
  simp only [paperRaisedCross_positive_iff_compact n a _ ha0,
    paperRaisedCross_positive_iff_compact n b _ hb0]

/-- The only effective numerator coordinates are the first `n` entries. -/
def paperFiniteNumeratorCoeffs (n : ℕ) (v : Fin n → ℝ) (i : ℕ) : ℝ :=
  if hi : i < n then v ⟨i, hi⟩ else 0

theorem paperPaddedNumerator_eq_of_below
    (n : ℕ) (x y : ℕ → ℝ)
    (hxy : ∀ i, i < n → x i = y i) :
    paperPaddedNumerator n x = paperPaddedNumerator n y := by
  funext i
  unfold paperPaddedNumerator
  split_ifs with hi
  · exact hxy i.toNat (by omega)
  · rfl

theorem paperGeneralCrossPolynomial_eq_of_below
    (n : ℕ) (a x y : ℕ → ℝ)
    (hxy : ∀ i, i < n → x i = y i) :
    paperGeneralCrossPolynomial n a x =
      paperGeneralCrossPolynomial n a y := by
  unfold paperGeneralCrossPolynomial
  rw [paperPaddedNumerator_eq_of_below n x y hxy]

theorem paperCompactRaisedCross_eq_of_below
    (n : ℕ) (a x y : ℕ → ℝ)
    (hxy : ∀ i, i < n → x i = y i) :
    paperCompactRaisedCross n a x = paperCompactRaisedCross n a y := by
  funext u
  unfold paperCompactRaisedCross paperRaisedCrossPolynomial
  rw [paperGeneralCrossPolynomial_eq_of_below n a x y hxy]

theorem paperFiniteNumeratorCoeffs_of_nat
    (n : ℕ) (x : ℕ → ℝ) (i : ℕ) (hi : i < n) :
    paperFiniteNumeratorCoeffs n (fun j => x j) i = x i := by
  simp [paperFiniteNumeratorCoeffs, hi]

/-- The compact feasibility problem really has `n` real variables. -/
theorem paperCommonSPR_exists_iff_fin_compact_feasible
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    (∃ p : Polynomial ℝ,
      paperPolynomialSPR n p
        (paperDescendingDenominator n a) ∧
      paperPolynomialSPR n p
        (paperDescendingDenominator n b)) ↔
    (∃ v : Fin n → ℝ,
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        0 < paperCompactRaisedCross n a
          (paperFiniteNumeratorCoeffs n v) u) ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        0 < paperCompactRaisedCross n b
          (paperFiniteNumeratorCoeffs n v) u)) := by
  rw [paperCommonSPR_exists_iff_compact_cross_feasible
    n hn a b ha0 hb0 hstableA hstableB]
  constructor
  · rintro ⟨x, hA, hB⟩
    refine ⟨fun j => x j, ?_, ?_⟩
    · simpa only [paperCompactRaisedCross_eq_of_below n a
        (paperFiniteNumeratorCoeffs n (fun j => x j)) x
        (paperFiniteNumeratorCoeffs_of_nat n x)] using hA
    · simpa only [paperCompactRaisedCross_eq_of_below n b
        (paperFiniteNumeratorCoeffs n (fun j => x j)) x
        (paperFiniteNumeratorCoeffs_of_nat n x)] using hB
  · rintro ⟨v, hA, hB⟩
    exact ⟨paperFiniteNumeratorCoeffs n v, hA, hB⟩

theorem paperGeneralCrossPolynomial_combo
    (n : ℕ) (a x y : ℕ → ℝ) (α β : ℝ) :
    paperGeneralCrossPolynomial n a
        (fun i => α*x i+β*y i) =
      Polynomial.C α * paperGeneralCrossPolynomial n a x +
        Polynomial.C β * paperGeneralCrossPolynomial n a y := by
  have h := paperGeneralCrossPolynomial_add_smul_numerator
    n a (fun i => α*x i) y β
  rw [paperGeneralCrossPolynomial_smul] at h
  exact h

theorem paperFiniteNumeratorCoeffs_combo
    (n : ℕ) (v w : Fin n → ℝ) (α β : ℝ) :
    paperFiniteNumeratorCoeffs n (α • v + β • w) =
      fun i => α*paperFiniteNumeratorCoeffs n v i +
        β*paperFiniteNumeratorCoeffs n w i := by
  funext i
  by_cases hi : i < n
  · simp [paperFiniteNumeratorCoeffs, hi, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
  · simp [paperFiniteNumeratorCoeffs, hi]

theorem paperRaisedCrossPolynomial_fin_combo
    (n : ℕ) (a : ℕ → ℝ) (v w : Fin n → ℝ)
    (α β : ℝ) (hab : α+β=1) :
    paperRaisedCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n (α • v + β • w)) 1 =
      Polynomial.C α * paperRaisedCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n v) 1 +
      Polynomial.C β * paperRaisedCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n w) 1 := by
  rw [paperFiniteNumeratorCoeffs_combo,
    paperRaisedCrossPolynomial,
    paperGeneralCrossPolynomial_combo]
  simp only [paperRaisedCrossPolynomial]
  have hscalar : Polynomial.C α + Polynomial.C β =
      (1 : Polynomial ℝ) := by
    rw [← Polynomial.C_add, hab, map_one]
  calc
    Polynomial.C α * paperGeneralCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n v) +
      Polynomial.C β * paperGeneralCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n w) +
      Polynomial.C 1 * paperRaiseCorrection n a =
        Polynomial.C α * paperGeneralCrossPolynomial n a
          (paperFiniteNumeratorCoeffs n v) +
        Polynomial.C β * paperGeneralCrossPolynomial n a
          (paperFiniteNumeratorCoeffs n w) +
        (Polynomial.C α + Polynomial.C β) * paperRaiseCorrection n a := by
          rw [hscalar]
          simp
    _ = _ := by simp only [map_one, one_mul]; ring

/-- The compact, finite-dimensional coefficient feasible region. -/
def paperFiniteCompactFeasibleSet
    (n : ℕ) (a b : ℕ → ℝ) : Set (Fin n → ℝ) :=
  {v | (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      0 < paperCompactRaisedCross n a
        (paperFiniteNumeratorCoeffs n v) u) ∧
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      0 < paperCompactRaisedCross n b
        (paperFiniteNumeratorCoeffs n v) u)}

theorem paperFiniteCompactFeasibleSet_convex
    (n : ℕ) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    Convex ℝ (paperFiniteCompactFeasibleSet n a b) := by
  intro v hv w hw α β hα hβ hab
  change (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      0 < paperCompactRaisedCross n a
        (paperFiniteNumeratorCoeffs n (α • v + β • w)) u) ∧
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      0 < paperCompactRaisedCross n b
        (paperFiniteNumeratorCoeffs n (α • v + β • w)) u)
  constructor
  · have hvA := (paperRaisedCross_positive_iff_compact n a _ ha0).mpr hv.1
    have hwA := (paperRaisedCross_positive_iff_compact n a _ ha0).mpr hw.1
    apply (paperRaisedCross_positive_iff_compact n a _ ha0).mp
    intro t ht
    have hpos : 0 <
        α * ((paperGeneralCrossPolynomial n a
          (paperFiniteNumeratorCoeffs n v)).eval t +
          (paperRaiseCorrection n a).eval t) +
        β * ((paperGeneralCrossPolynomial n a
          (paperFiniteNumeratorCoeffs n w)).eval t +
          (paperRaiseCorrection n a).eval t) := by
      by_cases hα0 : α = 0
      · have hβpos : 0 < β := by linarith
        exact add_pos_of_nonneg_of_pos
          (mul_nonneg hα (hvA t ht).le)
          (mul_pos hβpos (hwA t ht))
      · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
        exact add_pos_of_pos_of_nonneg
          (mul_pos hαpos (hvA t ht))
          (mul_nonneg hβ (hwA t ht).le)
    have hpoly := congrArg (Polynomial.eval t)
      (paperRaisedCrossPolynomial_fin_combo n a v w α β hab)
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C] at hpoly
    have hpos' : 0 <
        α * (paperRaisedCrossPolynomial n a
          (paperFiniteNumeratorCoeffs n v) 1).eval t +
        β * (paperRaisedCrossPolynomial n a
          (paperFiniteNumeratorCoeffs n w) 1).eval t := by
      simpa [paperRaisedCrossPolynomial] using hpos
    have hfinal := hpoly.symm ▸ hpos'
    simpa [paperRaisedCrossPolynomial] using hfinal
  · have hvB := (paperRaisedCross_positive_iff_compact n b _ hb0).mpr hv.2
    have hwB := (paperRaisedCross_positive_iff_compact n b _ hb0).mpr hw.2
    apply (paperRaisedCross_positive_iff_compact n b _ hb0).mp
    intro t ht
    have hpos : 0 <
        α * ((paperGeneralCrossPolynomial n b
          (paperFiniteNumeratorCoeffs n v)).eval t +
          (paperRaiseCorrection n b).eval t) +
        β * ((paperGeneralCrossPolynomial n b
          (paperFiniteNumeratorCoeffs n w)).eval t +
          (paperRaiseCorrection n b).eval t) := by
      by_cases hα0 : α = 0
      · have hβpos : 0 < β := by linarith
        exact add_pos_of_nonneg_of_pos
          (mul_nonneg hα (hvB t ht).le)
          (mul_pos hβpos (hwB t ht))
      · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
        exact add_pos_of_pos_of_nonneg
          (mul_pos hαpos (hvB t ht))
          (mul_nonneg hβ (hwB t ht).le)
    have hpoly := congrArg (Polynomial.eval t)
      (paperRaisedCrossPolynomial_fin_combo n b v w α β hab)
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C] at hpoly
    have hpos' : 0 <
        α * (paperRaisedCrossPolynomial n b
          (paperFiniteNumeratorCoeffs n v) 1).eval t +
        β * (paperRaisedCrossPolynomial n b
          (paperFiniteNumeratorCoeffs n w) 1).eval t := by
      simpa [paperRaisedCrossPolynomial] using hpos
    have hfinal := hpoly.symm ▸ hpos'
    simpa [paperRaisedCrossPolynomial] using hfinal

theorem paperFiniteCompactFeasibleSet_nonempty_iff_commonSPR
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    (paperFiniteCompactFeasibleSet n a b).Nonempty ↔
      ∃ p : Polynomial ℝ,
        paperPolynomialSPR n p
          (paperDescendingDenominator n a) ∧
        paperPolynomialSPR n p
          (paperDescendingDenominator n b) := by
  simpa [Set.Nonempty, paperFiniteCompactFeasibleSet]
    using (paperCommonSPR_exists_iff_fin_compact_feasible
      n hn a b ha0 hb0 hstableA hstableB).symm

theorem paperFiniteCompactFeasibleSet_nonempty_imp_stable_segment
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hfeasible : (paperFiniteCompactFeasibleSet n a b).Nonempty) :
    ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i)) := by
  obtain ⟨p, hpA, hpB⟩ :=
    (paperFiniteCompactFeasibleSet_nonempty_iff_commonSPR
      n hn a b ha0 hb0 hstableA hstableB).mp hfeasible
  exact paperTheorem2_necessity n a b p ha0 hb0 hpA hpB

theorem sixth_order_stable_segment_iff_fin_compact_feasible
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator 6
          (fun i => (1-r)*a i+r*b i))) ↔
    paperPolynomialHurwitz (paperDescendingDenominator 6 a) ∧
    paperPolynomialHurwitz (paperDescendingDenominator 6 b) ∧
      (paperFiniteCompactFeasibleSet 6 a b).Nonempty := by
  rw [sixth_order_stable_segment_iff_monic_cross_feasible a b ha0 hb0]
  apply and_congr_right
  intro hstableA
  apply and_congr_right
  intro hstableB
  rw [paperFiniteCompactFeasibleSet_nonempty_iff_commonSPR
    6 (by norm_num) a b ha0 hb0 hstableA hstableB]
  exact (paperCommonSPR_exists_iff_monic_cross_feasible
    6 (by norm_num) a b ha0 hb0 hstableA hstableB).symm



theorem paperFiniteNumeratorCoeffs_continuous
    (n i : ℕ) :
    Continuous (fun v : Fin n → ℝ => paperFiniteNumeratorCoeffs n v i) := by
  by_cases hi : i < n
  · simpa [paperFiniteNumeratorCoeffs, hi] using
      (continuous_apply (⟨i, hi⟩ : Fin n) :
        Continuous (fun v : Fin n → ℝ => v ⟨i, hi⟩))
  · simpa [paperFiniteNumeratorCoeffs, hi] using
      (continuous_const : Continuous (fun _ : Fin n → ℝ => (0 : ℝ)))

theorem paperPaddedFiniteNumerator_continuous
    (n : ℕ) (i : ℤ) :
    Continuous (fun v : Fin n → ℝ =>
      paperPaddedNumerator n (paperFiniteNumeratorCoeffs n v) i) := by
  by_cases hi : 0 ≤ i ∧ i < n
  · simpa [paperPaddedNumerator, hi] using
      paperFiniteNumeratorCoeffs_continuous n i.toNat
  · simpa [paperPaddedNumerator, hi] using
      (continuous_const : Continuous (fun _ : Fin n → ℝ => (0 : ℝ)))

theorem paperGeneralCrossPolynomial_fin_coeff_continuous
    (n : ℕ) (a : ℕ → ℝ) (j : ℕ) :
    Continuous (fun v : Fin n → ℝ =>
      (paperGeneralCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n v)).coeff j) := by
  by_cases hj : j < n
  · simp only [paperGeneralCrossPolynomial_coeff, if_pos hj,
      paperGeneralCoefficient]
    apply continuous_finset_sum
    intro k hk
    exact continuous_const.mul
      (paperPaddedFiniteNumerator_continuous n _)
  · simpa [paperGeneralCrossPolynomial_coeff, hj] using
      (continuous_const : Continuous (fun _ : Fin n → ℝ => (0 : ℝ)))

theorem paperRaisedCrossPolynomial_fin_coeff_continuous
    (n : ℕ) (a : ℕ → ℝ) (j : ℕ) :
    Continuous (fun v : Fin n → ℝ =>
      (paperRaisedCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n v) 1).coeff j) := by
  simp only [paperRaisedCrossPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_C_mul]
  exact (paperGeneralCrossPolynomial_fin_coeff_continuous n a j).add
    continuous_const

theorem paperCompactRaisedCross_fin_joint_continuous
    (n : ℕ) (a : ℕ → ℝ) :
    Continuous (fun z : (Fin n → ℝ) × ℝ =>
      paperCompactRaisedCross n a
        (paperFiniteNumeratorCoeffs n z.1) z.2) := by
  unfold paperCompactRaisedCross paperHomogenizedPolynomial
  apply continuous_finset_sum
  intro j hj
  exact (((paperRaisedCrossPolynomial_fin_coeff_continuous
      n a j).comp continuous_fst).mul (continuous_snd.pow j)).mul
      ((continuous_const.sub continuous_snd).pow (n-j))

/-- Compactness of the frequency interval makes strict feasibility open. -/
theorem paperFiniteCompactFeasibleSet_isOpen
    (n : ℕ) (a b : ℕ → ℝ) :
    IsOpen (paperFiniteCompactFeasibleSet n a b) := by
  let F (c : ℕ → ℝ) (v : Fin n → ℝ) : C(ℝ, ℝ) :=
    ⟨fun u => paperCompactRaisedCross n c
        (paperFiniteNumeratorCoeffs n v) u,
      paperCompactRaisedCross_continuous n c _⟩
  have hF (c : ℕ → ℝ) : Continuous (F c) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact paperCompactRaisedCross_fin_joint_continuous n c
  have hsingle (c : ℕ → ℝ) :
      IsOpen {v : Fin n → ℝ | ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        0 < paperCompactRaisedCross n c
          (paperFiniteNumeratorCoeffs n v) u} := by
    have hmaps := (ContinuousMap.isOpen_setOf_mapsTo
      (K := Set.Icc (0 : ℝ) 1) (U := Set.Ioi (0 : ℝ))
      isCompact_Icc isOpen_Ioi).preimage (hF c)
    simpa [F, Set.MapsTo, Set.mem_Icc, Set.mem_Ioi, and_imp]
      using hmaps
  exact (hsingle a).inter (hsingle b)



theorem paperFiniteNumeratorCoeffs_add
    (n : ℕ) (v w : Fin n → ℝ) :
    paperFiniteNumeratorCoeffs n (v+w) =
      fun i => paperFiniteNumeratorCoeffs n v i +
        paperFiniteNumeratorCoeffs n w i := by
  simpa using paperFiniteNumeratorCoeffs_combo n v w 1 1

theorem paperFiniteNumeratorCoeffs_smul
    (n : ℕ) (v : Fin n → ℝ) (c : ℝ) :
    paperFiniteNumeratorCoeffs n (c • v) =
      fun i => c * paperFiniteNumeratorCoeffs n v i := by
  funext i
  by_cases hi : i < n
  · simp [paperFiniteNumeratorCoeffs, hi, Pi.smul_apply, smul_eq_mul]
  · simp [paperFiniteNumeratorCoeffs, hi]

noncomputable def paperFiniteCrossLinear
    (n : ℕ) (a : ℕ → ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] Polynomial ℝ where
  toFun v := paperGeneralCrossPolynomial n a
    (paperFiniteNumeratorCoeffs n v)
  map_add' v w := by
    rw [paperFiniteNumeratorCoeffs_add]
    have h := paperGeneralCrossPolynomial_combo n a
      (paperFiniteNumeratorCoeffs n v)
      (paperFiniteNumeratorCoeffs n w) 1 1
    simpa using h
  map_smul' c v := by
    rw [paperFiniteNumeratorCoeffs_smul]
    rw [paperGeneralCrossPolynomial_smul]
    rw [Polynomial.smul_eq_C_mul]
    simp

theorem paperHomogenizedPolynomial_add
    (n : ℕ) (p q : Polynomial ℝ) (u : ℝ) :
    paperHomogenizedPolynomial n (p+q) u =
      paperHomogenizedPolynomial n p u +
        paperHomogenizedPolynomial n q u := by
  simp only [paperHomogenizedPolynomial, Polynomial.coeff_add,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem paperHomogenizedPolynomial_smul
    (n : ℕ) (p : Polynomial ℝ) (c u : ℝ) :
    paperHomogenizedPolynomial n (c • p) u =
      c * paperHomogenizedPolynomial n p u := by
  simp only [paperHomogenizedPolynomial,
    Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

noncomputable def paperHomogenizedLinear (n : ℕ) (u : ℝ) :
    Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := paperHomogenizedPolynomial n p u
  map_add' p q := paperHomogenizedPolynomial_add n p q u
  map_smul' c p := paperHomogenizedPolynomial_smul n p c u

noncomputable def paperFiniteCompactCrossLinear
    (n : ℕ) (a : ℕ → ℝ) (u : ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  (paperHomogenizedLinear n u).comp (paperFiniteCrossLinear n a)

theorem paperFiniteCompactCrossLinear_apply
    (n : ℕ) (a : ℕ → ℝ) (u : ℝ) (v : Fin n → ℝ) :
    paperFiniteCompactCrossLinear n a u v =
      paperHomogenizedPolynomial n
        (paperGeneralCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n v)) u := rfl

/-- Frequency feature for an unrestricted degree-`n` numerator. -/
noncomputable def paperCompactFeature
    (n : ℕ) (a : ℕ → ℝ) (u : ℝ) : Fin (n+1) → ℝ :=
  Fin.cons
    (paperHomogenizedPolynomial n (paperRaiseCorrection n a) u)
    (fun i => paperFiniteCompactCrossLinear n a u
      (fun j => if i = j then 1 else 0))

def paperFeatureDot {n : ℕ}
    (v f : Fin (n+1) → ℝ) : ℝ :=
  ∑ i, v i * f i

theorem paperFeatureDot_compactFeature
    (n : ℕ) (a : ℕ → ℝ) (u : ℝ)
    (v : Fin (n+1) → ℝ) :
    paperFeatureDot v (paperCompactFeature n a u) =
      paperHomogenizedPolynomial n
        (paperRaisedCrossPolynomial n a
          (paperFiniteNumeratorCoeffs n (fun i => v i.succ))
          (v 0)) u := by
  have hlinear := LinearMap.pi_apply_eq_sum_univ
    (paperFiniteCompactCrossLinear n a u) (fun i : Fin n => v i.succ)
  simp only [smul_eq_mul] at hlinear
  rw [paperFeatureDot, Fin.sum_univ_succ]
  simp only [paperCompactFeature, Fin.cons_zero, Fin.cons_succ]
  rw [← hlinear, paperFiniteCompactCrossLinear_apply]
  rw [paperRaisedCrossPolynomial, paperHomogenizedPolynomial_add]
  rw [← Polynomial.smul_eq_C_mul,
    paperHomogenizedPolynomial_smul]
  ring

theorem paperCompactFeature_continuous
    (n : ℕ) (a : ℕ → ℝ) :
    Continuous (paperCompactFeature n a) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa [paperCompactFeature] using
      paperHomogenizedPolynomial_continuous n (paperRaiseCorrection n a)
  · intro j
    simpa [paperCompactFeature, paperFiniteCompactCrossLinear_apply,
      paperFiniteCrossLinear] using
      paperHomogenizedPolynomial_continuous n
        (paperGeneralCrossPolynomial n a
          (paperFiniteNumeratorCoeffs n
            (fun k => if j = k then 1 else 0)))

def paperEndpointFeatureSet
    (n : ℕ) (a b : ℕ → ℝ) : Set (Fin (n+1) → ℝ) :=
  paperCompactFeature n a '' Set.Icc (0 : ℝ) 1 ∪
    paperCompactFeature n b '' Set.Icc (0 : ℝ) 1

theorem paperEndpointFeatureSet_compact
    (n : ℕ) (a b : ℕ → ℝ) :
    IsCompact (paperEndpointFeatureSet n a b) :=
  (isCompact_Icc.image (paperCompactFeature_continuous n a)).union
    (isCompact_Icc.image (paperCompactFeature_continuous n b))

theorem paperEndpointFeatureSet_nonempty
    (n : ℕ) (a b : ℕ → ℝ) :
    (paperEndpointFeatureSet n a b).Nonempty := by
  refine ⟨paperCompactFeature n a 0, Or.inl ?_⟩
  exact Set.mem_image_of_mem _ (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)

noncomputable def paperFeatureDotCLM {n : ℕ}
    (v : Fin (n+1) → ℝ) :
    (Fin (n+1) → ℝ) →L[ℝ] ℝ :=
  ∑ i, v i • ContinuousLinearMap.proj i

theorem paperFeatureDotCLM_apply {n : ℕ}
    (v f : Fin (n+1) → ℝ) :
    paperFeatureDotCLM v f = paperFeatureDot v f := by
  simp [paperFeatureDotCLM, paperFeatureDot,
    ContinuousLinearMap.sum_apply]

theorem paperFeatureDual_eq_dot {n : ℕ}
    (f : (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (v : Fin (n+1) → ℝ) :
    f v = paperFeatureDot
      (fun i => f (Pi.single i 1)) v := by
  have hbasis (i : Fin (n+1)) :
      (fun j => if i = j then (1 : ℝ) else 0) =
        Pi.single i 1 := by
    ext j
    by_cases h : i = j
    · subst j
      simp
    · simp [h]
  calc
    f v = f (∑ i, (v i) •
        fun j => if i = j then (1 : ℝ) else 0) := by
      rw [← pi_eq_sum_univ v]
    _ = ∑ i, (v i) • f (Pi.single i 1) := by
      simp only [map_sum, map_smul, hbasis]
    _ = paperFeatureDot (fun i => f (Pi.single i 1)) v := by
      simp only [paperFeatureDot, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- General-order dual certificate: a strict common cross witness exists
exactly when the origin is outside the closed convex hull of both compact
frequency-feature curves. -/
theorem paperEndpointFeature_separator_iff
    (n : ℕ) (a b : ℕ → ℝ) :
    (∃ v : Fin (n+1) → ℝ,
      ∀ f ∈ paperEndpointFeatureSet n a b,
        0 < paperFeatureDot v f) ↔
      (0 : Fin (n+1) → ℝ) ∉
        closedConvexHull ℝ (paperEndpointFeatureSet n a b) := by
  let S := paperEndpointFeatureSet n a b
  have hcompact : IsCompact S := paperEndpointFeatureSet_compact n a b
  have hnonempty : S.Nonempty := paperEndpointFeatureSet_nonempty n a b
  constructor
  · rintro ⟨v, hv⟩ hzero
    obtain ⟨f, hf, hmin⟩ := hcompact.exists_isMinOn hnonempty
      (paperFeatureDotCLM v).continuous.continuousOn
    have hpos : 0 < paperFeatureDotCLM v f := by
      simpa only [paperFeatureDotCLM_apply] using hv f hf
    have hsub : closedConvexHull ℝ S ⊆
        {w | paperFeatureDotCLM v f ≤ paperFeatureDotCLM v w} := by
      apply closedConvexHull_min
      · intro w hw
        exact hmin hw
      · exact convex_halfSpace_ge
          (paperFeatureDotCLM v).toLinearMap.isLinear _
      · exact isClosed_le continuous_const (paperFeatureDotCLM v).continuous
    have hz := hsub hzero
    simp only [Set.mem_setOf_eq, map_zero] at hz
    exact (not_le_of_gt hpos) hz
  · intro hzero
    obtain ⟨f, u, hu, hf⟩ := geometric_hahn_banach_point_closed
      (convex_closedConvexHull (𝕜 := ℝ) (s := S))
      isClosed_closedConvexHull hzero
    refine ⟨fun i => f (Pi.single i 1), ?_⟩
    intro v hv
    rw [← paperFeatureDual_eq_dot]
    have hstrict := hu.trans (hf v (subset_closedConvexHull hv))
    simpa only [map_zero] using hstrict

/-- The arbitrary-order common SPR problem is exactly a finite-dimensional
closed-convex-hull exclusion problem. -/
theorem paperCommonSPR_iff_feature_exclusion
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    (∃ p : Polynomial ℝ,
      paperPolynomialSPR n p
        (paperDescendingDenominator n a) ∧
      paperPolynomialSPR n p
        (paperDescendingDenominator n b)) ↔
      (0 : Fin (n+1) → ℝ) ∉
        closedConvexHull ℝ (paperEndpointFeatureSet n a b) := by
  rw [← paperEndpointFeature_separator_iff]
  constructor
  · rintro ⟨p, hpA, hpB⟩
    obtain ⟨x, hA, hB⟩ :=
      (paperCommonSPR_exists_iff_monic_cross_feasible
        n hn a b ha0 hb0 hstableA hstableB).mp
        ⟨p, hpA, hpB⟩
    let v : Fin (n+1) → ℝ := Fin.cons 1 (fun i => x i)
    refine ⟨v, ?_⟩
    intro f hf
    rcases hf with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · have hcomp :=
        (paperRaisedCross_positive_iff_compact n a x ha0).mp hA u hu.1 hu.2
      rw [paperFeatureDot_compactFeature]
      have htail : paperGeneralCrossPolynomial n a
          (paperFiniteNumeratorCoeffs n (fun i => v i.succ)) =
          paperGeneralCrossPolynomial n a x := by
        apply paperGeneralCrossPolynomial_eq_of_below
        intro i hi
        simp only [paperFiniteNumeratorCoeffs, dif_pos hi]
        exact Fin.cons_succ (α := fun _ : Fin (n+1) => ℝ)
          (x := (1 : ℝ))
          (p := fun j : Fin n => x j) (i := ⟨i, hi⟩)
      simp only [v, Fin.cons_zero, Fin.cons_succ] at htail ⊢
      simpa [paperCompactRaisedCross, paperRaisedCrossPolynomial,
        htail] using hcomp
    · have hcomp :=
        (paperRaisedCross_positive_iff_compact n b x hb0).mp hB u hu.1 hu.2
      rw [paperFeatureDot_compactFeature]
      have htail : paperGeneralCrossPolynomial n b
          (paperFiniteNumeratorCoeffs n (fun i => v i.succ)) =
          paperGeneralCrossPolynomial n b x := by
        apply paperGeneralCrossPolynomial_eq_of_below
        intro i hi
        simp only [paperFiniteNumeratorCoeffs, dif_pos hi]
        exact Fin.cons_succ (α := fun _ : Fin (n+1) => ℝ)
          (x := (1 : ℝ))
          (p := fun j : Fin n => x j) (i := ⟨i, hi⟩)
      simp only [v, Fin.cons_zero, Fin.cons_succ] at htail ⊢
      simpa [paperCompactRaisedCross, paperRaisedCrossPolynomial,
        htail] using hcomp
  · rintro ⟨v, hv⟩
    let x : ℕ → ℝ := paperFiniteNumeratorCoeffs n (fun i => v i.succ)
    let ε : ℝ := v 0
    have hε : 0 < ε := by
      have h := hv (paperCompactFeature n a 1)
        (Or.inl (Set.mem_image_of_mem _ (by norm_num :
          (1 : ℝ) ∈ Set.Icc 0 1)))
      rw [paperFeatureDot_compactFeature,
        paperHomogenizedPolynomial_one,
        paperRaisedCrossPolynomial_top_coeff n a x ε ha0] at h
      exact h
    have hAcompact : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        0 < paperHomogenizedPolynomial n
          (paperRaisedCrossPolynomial n a x ε) u := by
      intro u hu0 hu1
      have h := hv (paperCompactFeature n a u)
        (Or.inl (Set.mem_image_of_mem _ ⟨hu0, hu1⟩))
      simpa [x, ε, paperFeatureDot_compactFeature] using h
    have hBcompact : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        0 < paperHomogenizedPolynomial n
          (paperRaisedCrossPolynomial n b x ε) u := by
      intro u hu0 hu1
      have h := hv (paperCompactFeature n b u)
        (Or.inr (Set.mem_image_of_mem _ ⟨hu0, hu1⟩))
      simpa [x, ε, paperFeatureDot_compactFeature] using h
    have hA := (paperHomogenizedPolynomial_pos_iff n
      (paperRaisedCrossPolynomial n a x ε)
      (paperRaisedCrossPolynomial_natDegree_le n a x ε)
      (by rw [paperRaisedCrossPolynomial_top_coeff n a x ε ha0];
          exact hε)).mpr hAcompact
    have hB := (paperHomogenizedPolynomial_pos_iff n
      (paperRaisedCrossPolynomial n b x ε)
      (paperRaisedCrossPolynomial_natDegree_le n b x ε)
      (by rw [paperRaisedCrossPolynomial_top_coeff n b x ε hb0];
          exact hε)).mpr hBcompact
    apply (paperCommonSPR_exists_iff_cross_feasible
      n hn a b ha0 hb0 hstableA hstableB).mpr
    refine ⟨x, ε, hε, ?_, ?_⟩
    · simpa [paperRaisedCrossPolynomial] using hA
    · simpa [paperRaisedCrossPolynomial] using hB



/-- Feature exclusion is sufficient for a stable segment in every order. -/
theorem paperFeature_exclusion_imp_stable_segment
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hfeature : (0 : Fin (n+1) → ℝ) ∉
      closedConvexHull ℝ (paperEndpointFeatureSet n a b)) :
    ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i)) := by
  obtain ⟨p, hpA, hpB⟩ :=
    (paperCommonSPR_iff_feature_exclusion
      n hn a b ha0 hb0 hstableA hstableB).mpr hfeature
  exact paperTheorem2_necessity n a b p ha0 hb0 hpA hpB

/-- For degree six, stability of the segment is equivalent to the compact
frequency-feature convex hull excluding the origin, with Hurwitz endpoints. -/
theorem sixth_order_stable_segment_iff_feature_exclusion
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator 6
          (fun i => (1-r)*a i+r*b i))) ↔
    paperPolynomialHurwitz (paperDescendingDenominator 6 a) ∧
    paperPolynomialHurwitz (paperDescendingDenominator 6 b) ∧
      (0 : Fin 7 → ℝ) ∉
        closedConvexHull ℝ (paperEndpointFeatureSet 6 a b) := by
  rw [sixth_order_stable_segment_iff_fin_compact_feasible a b ha0 hb0]
  apply and_congr_right
  intro hstableA
  apply and_congr_right
  intro hstableB
  rw [paperFiniteCompactFeasibleSet_nonempty_iff_commonSPR
    6 (by norm_num) a b ha0 hb0 hstableA hstableB]
  exact paperCommonSPR_iff_feature_exclusion
    6 (by norm_num) a b ha0 hb0 hstableA hstableB



theorem paperFeature_affineIndependent_card_le
    (n : ℕ) {ι : Type*} [Fintype ι]
    {z : ι → Fin (n+1) → ℝ}
    (hz : AffineIndependent ℝ z) :
    Fintype.card ι ≤ n+2 := by
  have hcard := hz.card_le_finrank_succ
  have hdim : Module.finrank ℝ
      (vectorSpan ℝ (Set.range z)) ≤ n+1 := by
    simpa using Submodule.finrank_le (vectorSpan ℝ (Set.range z))
  omega

theorem paperFeature_finite_convex_representation
    (n : ℕ) {S : Set (Fin (n+1) → ℝ)}
    {y : Fin (n+1) → ℝ}
    (hy : y ∈ convexHull ℝ S) :
    ∃ m : ℕ, m ≤ n+2 ∧
      ∃ (z : Fin m → Fin (n+1) → ℝ) (w : Fin m → ℝ),
        (∀ i, z i ∈ S) ∧ AffineIndependent ℝ z ∧
          (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
            (∑ i, w i • z i) = y := by
  obtain ⟨ι, inst, z, w, hz, hind, hw, hsum, hcomb⟩ :=
    eq_pos_convex_span_of_mem_convexHull hy
  let e := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι,
    paperFeature_affineIndependent_card_le n hind,
    z ∘ e, w ∘ e, (fun i => hz ⟨e i, rfl⟩),
    hind.comp_embedding e.toEmbedding, (fun i => hw (e i)), ?_, ?_⟩
  · exact (e.sum_comp w).trans hsum
  · exact (e.sum_comp (fun i => w i • z i)).trans hcomb

def paperFeatureCombinationMap (n m : ℕ)
    (v : (Fin m → ℝ) × (Fin m → Fin (n+1) → ℝ)) :
    Fin (n+1) → ℝ :=
  ∑ i, v.1 i • v.2 i

def paperFeatureCombinationDomain (n m : ℕ)
    (S : Set (Fin (n+1) → ℝ)) :
    Set ((Fin m → ℝ) × (Fin m → Fin (n+1) → ℝ)) :=
  stdSimplex ℝ (Fin m) ×ˢ Set.univ.pi (fun _ => S)

def paperFeatureCombinationImage (n m : ℕ)
    (S : Set (Fin (n+1) → ℝ)) :
    Set (Fin (n+1) → ℝ) :=
  paperFeatureCombinationMap n m '' paperFeatureCombinationDomain n m S

theorem compact_paperFeatureCombinationImage
    (n m : ℕ) {S : Set (Fin (n+1) → ℝ)}
    (hS : IsCompact S) :
    IsCompact (paperFeatureCombinationImage n m S) := by
  have hdomain : IsCompact (paperFeatureCombinationDomain n m S) :=
    (isCompact_stdSimplex (Fin m)).prod
      (isCompact_univ_pi fun _ => hS)
  exact hdomain.image (by
    unfold paperFeatureCombinationMap
    fun_prop)

theorem paperFeatureCombinationImage_subset_convexHull
    (n m : ℕ) (S : Set (Fin (n+1) → ℝ)) :
    paperFeatureCombinationImage n m S ⊆ convexHull ℝ S := by
  rintro y ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
  exact (convex_convexHull ℝ S).sum_mem
    (fun i _ => hw.1 i) hw.2
    (fun i _ => subset_convexHull ℝ S (hz i (Set.mem_univ i)))

theorem paperFeature_convexHull_eq_finite_union
    (n : ℕ) (S : Set (Fin (n+1) → ℝ)) :
    convexHull ℝ S =
      ⋃ m : Fin (n+3), paperFeatureCombinationImage n m.val S := by
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨m, hm, z, w, hz, _, hw, hsum, hcomb⟩ :=
      paperFeature_finite_convex_representation n hy
    refine Set.mem_iUnion.mpr
      ⟨⟨m, by omega⟩, (w, z), ?_, hcomb⟩
    exact ⟨⟨fun i => (hw i).le, hsum⟩,
      fun i _ => hz i⟩
  · intro y hy
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
    exact paperFeatureCombinationImage_subset_convexHull
      n m.val S hm

theorem compact_paperFeatureConvexHull
    (n : ℕ) {S : Set (Fin (n+1) → ℝ)}
    (hS : IsCompact S) :
    IsCompact (convexHull ℝ S) := by
  rw [paperFeature_convexHull_eq_finite_union n]
  exact isCompact_iUnion fun m =>
    compact_paperFeatureCombinationImage n m.val hS

theorem closedConvexHull_eq_paperFeatureConvexHull
    (n : ℕ) {S : Set (Fin (n+1) → ℝ)}
    (hS : IsCompact S) :
    closedConvexHull ℝ S = convexHull ℝ S := by
  rw [closedConvexHull_eq_closure_convexHull,
    (compact_paperFeatureConvexHull n hS).isClosed.closure_eq]

/-- Failure of common SPR synthesis has a positive barycentric balance of
at most `n+2` compact endpoint-frequency features. -/
theorem zero_mem_paperEndpointFeature_closedConvexHull_iff_atom
    (n : ℕ) (a b : ℕ → ℝ) :
    (0 : Fin (n+1) → ℝ) ∈
        closedConvexHull ℝ (paperEndpointFeatureSet n a b) ↔
      ∃ m : ℕ, m ≤ n+2 ∧
        ∃ (right : Fin m → Bool) (u w : Fin m → ℝ),
          (∀ i, u i ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
          (∑ i, w i • paperCompactFeature n
            (if right i then b else a) (u i)) = 0 := by
  rw [closedConvexHull_eq_paperFeatureConvexHull n
    (paperEndpointFeatureSet_compact n a b)]
  constructor
  · intro hzero
    obtain ⟨m, hm, z, w, hz, _, hw, hsum, hbalance⟩ :=
      paperFeature_finite_convex_representation n hzero
    have hchoice : ∀ i, ∃ right : Bool, ∃ u ∈ Set.Icc (0 : ℝ) 1,
        z i = paperCompactFeature n (if right then b else a) u := by
      intro i
      rcases hz i with ⟨u, hu, hzu⟩ | ⟨u, hu, hzu⟩
      · exact ⟨false, u, hu, hzu.symm⟩
      · exact ⟨true, u, hu, hzu.symm⟩
    choose right u hu heq using hchoice
    refine ⟨m, hm, right, u, w, hu, hw, hsum, ?_⟩
    simpa only [heq] using hbalance
  · rintro ⟨m, _, right, u, w, hu, hw, hsum, hbalance⟩
    rw [← hbalance]
    exact (convex_convexHull ℝ _).sum_mem
      (fun i _ => (hw i).le) hsum
      (fun i _ => subset_convexHull ℝ _ (by
        cases h : right i
        · exact Or.inl (Set.mem_image_of_mem _ (hu i))
        · exact Or.inr (Set.mem_image_of_mem _ (hu i))))

def PaperGeneralAtomContact
    (n : ℕ) (a b : ℕ → ℝ) : Prop :=
  ∃ m : ℕ, m ≤ n+2 ∧
    ∃ (right : Fin m → Bool) (u w : Fin m → ℝ),
      (∀ i, u i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
      (∑ i, w i • paperCompactFeature n
        (if right i then b else a) (u i)) = 0

theorem paperCommonSPR_iff_no_atomContact
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    (∃ p : Polynomial ℝ,
      paperPolynomialSPR n p
        (paperDescendingDenominator n a) ∧
      paperPolynomialSPR n p
        (paperDescendingDenominator n b)) ↔
      ¬ PaperGeneralAtomContact n a b := by
  rw [paperCommonSPR_iff_feature_exclusion
    n hn a b ha0 hb0 hstableA hstableB]
  exact not_congr (zero_mem_paperEndpointFeature_closedConvexHull_iff_atom n a b)



/-- The alternative arbitrary-order sufficiency route, with its sole
unproved geometric step stated as exclusion of the finite atom balance. -/
theorem paperTheorem2_sufficiency_of_no_atomContact
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i)))
    (hno : ¬ PaperGeneralAtomContact n a b) :
    ∃ p : Polynomial ℝ,
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        paperPolynomialSPR n p
          (paperDescendingDenominator n
            (fun i => (1-r)*a i+r*b i)) := by
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa using hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa using hsegment 1 (by norm_num) (by norm_num)
  obtain ⟨p, hpA, hpB⟩ :=
    (paperCommonSPR_iff_no_atomContact
      n hn a b ha0 hb0 hstableA hstableB).mpr hno
  exact ⟨p, paperTheorem2_commonSPR_on_segment
    n a b p ha0 hb0 hpA hpB⟩

theorem sixth_order_stable_segment_excludes_general_atom
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator 6
          (fun i => (1-r)*a i+r*b i))) :
    ¬ PaperGeneralAtomContact 6 a b := by
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator 6 a) := by
    simpa using hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator 6 b) := by
    simpa using hsegment 1 (by norm_num) (by norm_num)
  obtain ⟨p, hp⟩ :=
    (sixth_order_paper_coefficient_sequence a b ha0 hb0).mp hsegment
  apply (paperCommonSPR_iff_no_atomContact
    6 (by norm_num) a b ha0 hb0 hstableA hstableB).mp
  exact ⟨p,
    by simpa using hp 0 (by norm_num) (by norm_num),
    by simpa using hp 1 (by norm_num) (by norm_num)⟩



/-- An affinely independent positive balance with the maximum possible
number of features is an interior point of its simplex. -/
theorem paperFeature_full_simplex_balance_interior
    (n : ℕ)
    (z : Fin (n+2) → Fin (n+1) → ℝ)
    (w : Fin (n+2) → ℝ)
    (hz : AffineIndependent ℝ z)
    (hw : ∀ i, 0 < w i)
    (hsum : (∑ i, w i) = 1)
    (hbalance : (∑ i, w i • z i) = 0) :
    (0 : Fin (n+1) → ℝ) ∈
      interior (convexHull ℝ (Set.range z)) := by
  have hcard : Fintype.card (Fin (n+2)) =
      Module.finrank ℝ (Fin (n+1) → ℝ) + 1 := by
    simp
  have hvectorSpan : vectorSpan ℝ (Set.range z) = ⊤ :=
    hz.vectorSpan_eq_top_of_card_eq_finrank_add_one hcard
  have hspan_nonempty :
      ((affineSpan ℝ (Set.range z) : AffineSubspace ℝ
        (Fin (n+1) → ℝ)) : Set (Fin (n+1) → ℝ)).Nonempty := by
    exact ⟨z 0, (subset_affineSpan ℝ (Set.range z))
      (Set.mem_range_self 0)⟩
  have hspan : affineSpan ℝ (Set.range z) = ⊤ := by
    apply (AffineSubspace.direction_eq_top_iff_of_nonempty
      hspan_nonempty).mp
    simpa only [direction_affineSpan] using hvectorSpan
  let basis : AffineBasis (Fin (n+2)) ℝ (Fin (n+1) → ℝ) :=
    ⟨z, hz, hspan⟩
  change (0 : Fin (n+1) → ℝ) ∈
    interior (convexHull ℝ (Set.range basis))
  rw [basis.interior_convexHull]
  intro i
  have hcomb : Finset.univ.affineCombination ℝ z w = 0 := by
    rw [Finset.affineCombination_eq_linear_combination _ z w hsum]
    exact hbalance
  have hcombB : Finset.univ.affineCombination ℝ basis w = 0 := by
    simpa [basis] using hcomb
  have hcoord := basis.coord_apply_combination_of_mem
    (Finset.mem_univ i) hsum
  change 0 < basis.coord i 0
  rw [← hcombB, hcoord]
  exact hw i

/-- At a boundary contact in order `n`, at most `n+1` atoms suffice. -/
theorem paperFeature_boundary_convex_representation
    (n : ℕ) {S : Set (Fin (n+1) → ℝ)}
    (hzero : (0 : Fin (n+1) → ℝ) ∈ convexHull ℝ S)
    (hboundary : (0 : Fin (n+1) → ℝ) ∉
      interior (convexHull ℝ S)) :
    ∃ m : ℕ, m ≤ n+1 ∧
      ∃ (z : Fin m → Fin (n+1) → ℝ) (w : Fin m → ℝ),
        (∀ i, z i ∈ S) ∧ AffineIndependent ℝ z ∧
          (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
            (∑ i, w i • z i) = 0 := by
  obtain ⟨m, hm, z, w, hz, hind, hw, hsum, hbalance⟩ :=
    paperFeature_finite_convex_representation n hzero
  by_cases hsmall : m ≤ n+1
  · exact ⟨m, hsmall, z, w, hz, hind, hw, hsum, hbalance⟩
  · have hfull : m = n+2 := by omega
    subst m
    have hinterior := paperFeature_full_simplex_balance_interior
      n z w hind hw hsum hbalance
    have hrange : Set.range z ⊆ S := by
      rintro v ⟨i, rfl⟩
      exact hz i
    exact False.elim (hboundary
      (interior_mono (convexHull_mono hrange) hinterior))

theorem zero_boundary_paperEndpointFeature_iff_small_atom
    (n : ℕ) (a b : ℕ → ℝ)
    (hboundary : (0 : Fin (n+1) → ℝ) ∉
      interior (convexHull ℝ (paperEndpointFeatureSet n a b))) :
    (0 : Fin (n+1) → ℝ) ∈
        closedConvexHull ℝ (paperEndpointFeatureSet n a b) ↔
      ∃ m : ℕ, m ≤ n+1 ∧
        ∃ (right : Fin m → Bool) (u w : Fin m → ℝ),
          (∀ i, u i ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
          (∑ i, w i • paperCompactFeature n
            (if right i then b else a) (u i)) = 0 := by
  rw [closedConvexHull_eq_paperFeatureConvexHull n
    (paperEndpointFeatureSet_compact n a b)]
  constructor
  · intro hzero
    obtain ⟨m, hm, z, w, hz, _, hw, hsum, hbalance⟩ :=
      paperFeature_boundary_convex_representation
        n hzero hboundary
    have hchoice : ∀ i, ∃ right : Bool, ∃ u ∈ Set.Icc (0 : ℝ) 1,
        z i = paperCompactFeature n (if right then b else a) u := by
      intro i
      rcases hz i with ⟨u, hu, hzu⟩ | ⟨u, hu, hzu⟩
      · exact ⟨false, u, hu, hzu.symm⟩
      · exact ⟨true, u, hu, hzu.symm⟩
    choose right u hu heq using hchoice
    refine ⟨m, hm, right, u, w, hu, hw, hsum, ?_⟩
    simpa only [heq] using hbalance
  · rintro ⟨m, _, right, u, w, hu, hw, hsum, hbalance⟩
    rw [← hbalance]
    exact (convex_convexHull ℝ _).sum_mem
      (fun i _ => (hw i).le) hsum
      (fun i _ => subset_convexHull ℝ _ (by
        cases h : right i
        · exact Or.inl (Set.mem_image_of_mem _ (hu i))
        · exact Or.inr (Set.mem_image_of_mem _ (hu i))))



theorem paperGeneralCrossPolynomial_affine_denominator
    (n : ℕ) (a b x : ℕ → ℝ) (r : ℝ) :
    paperGeneralCrossPolynomial n
        (fun i => (1-r)*a i+r*b i) x =
      Polynomial.C (1-r) * paperGeneralCrossPolynomial n a x +
        Polynomial.C r * paperGeneralCrossPolynomial n b x := by
  ext j
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul]
  simp only [paperGeneralCrossPolynomial_coeff]
  by_cases hj : j < n
  · rw [if_pos hj, if_pos hj, if_pos hj]
    rw [paperGeneralCoefficient_affine]
  · rw [if_neg hj, if_neg hj, if_neg hj]
    ring

theorem paperRaiseProduct_affine_denominator
    (n : ℕ) (a b : ℕ → ℝ) (r : ℝ) :
    paperRaiseProduct n (fun i => (1-r)*a i+r*b i) =
      Polynomial.C (1-r) * paperRaiseProduct n a +
        Polynomial.C r * paperRaiseProduct n b := by
  unfold paperRaiseProduct
  rw [paperDescendingDenominator_affine]
  simp only [Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.C_comp]
  ring

theorem paperRaiseCorrection_affine_denominator
    (n : ℕ) (a b : ℕ → ℝ) (r : ℝ) :
    paperRaiseCorrection n (fun i => (1-r)*a i+r*b i) =
      Polynomial.C (1-r) * paperRaiseCorrection n a +
        Polynomial.C r * paperRaiseCorrection n b := by
  ext j
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul]
  simp only [paperRaiseCorrection_coeff]
  by_cases hj : j ≤ n
  · rw [if_pos hj, if_pos hj, if_pos hj]
    rw [paperRaiseProduct_affine_denominator,
      Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_C_mul]
    ring
  · rw [if_neg hj, if_neg hj, if_neg hj]
    ring

theorem paperRaisedCrossPolynomial_affine_denominator
    (n : ℕ) (a b x : ℕ → ℝ) (ε r : ℝ) :
    paperRaisedCrossPolynomial n
        (fun i => (1-r)*a i+r*b i) x ε =
      Polynomial.C (1-r) * paperRaisedCrossPolynomial n a x ε +
        Polynomial.C r * paperRaisedCrossPolynomial n b x ε := by
  simp only [paperRaisedCrossPolynomial,
    paperGeneralCrossPolynomial_affine_denominator,
    paperRaiseCorrection_affine_denominator]
  ring

theorem paperCompactFeature_affine_denominator
    (n : ℕ) (a b : ℕ → ℝ) (r u : ℝ) :
    paperCompactFeature n
        (fun i => (1-r)*a i+r*b i) u =
      (1-r) • paperCompactFeature n a u +
        r • paperCompactFeature n b u := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp only [paperCompactFeature, Fin.cons_zero,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [paperRaiseCorrection_affine_denominator,
      paperHomogenizedPolynomial_add,
      ← Polynomial.smul_eq_C_mul,
      ← Polynomial.smul_eq_C_mul,
      paperHomogenizedPolynomial_smul,
      paperHomogenizedPolynomial_smul]
  · intro k
    simp only [paperCompactFeature, Fin.cons_succ,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      paperFiniteCompactCrossLinear_apply]
    rw [paperGeneralCrossPolynomial_affine_denominator,
      paperHomogenizedPolynomial_add,
      ← Polynomial.smul_eq_C_mul,
      ← Polynomial.smul_eq_C_mul,
      paperHomogenizedPolynomial_smul,
      paperHomogenizedPolynomial_smul]



theorem paperCompactFeature_convex_ratio
    (n : ℕ) (a b : ℕ → ℝ) (u v x : ℝ)
    (hv : v ≠ 0) :
    paperCompactFeature n
        (fun i => (1-u)*a i+u*b i) x =
      (1-u/v) • paperCompactFeature n a x +
        (u/v) • paperCompactFeature n
          (fun i => (1-v)*a i+v*b i) x := by
  have hcoeff : (fun i => (1-u)*a i+u*b i) =
      (fun i => (1-u/v)*a i +
        (u/v)*((1-v)*a i+v*b i)) := by
    funext i
    field_simp [hv]
    ring
  rw [hcoeff, paperCompactFeature_affine_denominator]

theorem paperFeature_convexHull_initial_mono
    (n : ℕ) (a b : ℕ → ℝ) {u v : ℝ}
    (hu0 : 0 ≤ u) (huv : u ≤ v) :
    convexHull ℝ (paperEndpointFeatureSet n a
      (fun i => (1-u)*a i+u*b i)) ⊆
    convexHull ℝ (paperEndpointFeatureSet n a
      (fun i => (1-v)*a i+v*b i)) := by
  by_cases hv0 : v = 0
  · have hu : u = 0 := by linarith
    subst u
    subst v
    exact Set.Subset.rfl
  · have hv : 0 < v := lt_of_le_of_ne (hu0.trans huv) (Ne.symm hv0)
    apply convexHull_min
    · rintro y (hy | hy)
      · exact subset_convexHull ℝ _ (Or.inl hy)
      · obtain ⟨x, hx, rfl⟩ := hy
        have haMem : paperCompactFeature n a x ∈
            convexHull ℝ (paperEndpointFeatureSet n a
              (fun i => (1-v)*a i+v*b i)) :=
          subset_convexHull ℝ _
            (Or.inl (Set.mem_image_of_mem _ hx))
        have hvMem : paperCompactFeature n
            (fun i => (1-v)*a i+v*b i) x ∈
            convexHull ℝ (paperEndpointFeatureSet n a
              (fun i => (1-v)*a i+v*b i)) :=
          subset_convexHull ℝ _
            (Or.inr (Set.mem_image_of_mem _ hx))
        have hratio : u/v ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨div_nonneg hu0 hv.le, (div_le_one hv).2 huv⟩
        rw [paperCompactFeature_convex_ratio n a b u v x hv0]
        simpa only [AffineMap.lineMap_apply_module] using
          (convex_convexHull ℝ _).lineMap_mem haMem hvMem hratio
    · exact convex_convexHull ℝ _

theorem paperCompactFeature_segment_joint_continuous
    (n : ℕ) (a b : ℕ → ℝ) :
    Continuous (fun p : ℝ × ℝ =>
      paperCompactFeature n
        (fun i => (1-p.1)*a i+p.1*b i) p.2) := by
  have heq : (fun p : ℝ × ℝ =>
      paperCompactFeature n
        (fun i => (1-p.1)*a i+p.1*b i) p.2) =
      (fun p : ℝ × ℝ =>
        (1-p.1) • paperCompactFeature n a p.2 +
          p.1 • paperCompactFeature n b p.2) := by
    funext p
    exact paperCompactFeature_affine_denominator n a b p.1 p.2
  rw [heq]
  exact ((continuous_const.sub continuous_fst).smul
    ((paperCompactFeature_continuous n a).comp continuous_snd)).add
    (continuous_fst.smul
      ((paperCompactFeature_continuous n b).comp continuous_snd))


set_option maxHeartbeats 800000


def paperFeatureFailureParameters
    (n : ℕ) (a b : ℕ → ℝ) : Set ℝ :=
  {r | r ∈ Set.Icc (0 : ℝ) 1 ∧
    (0 : Fin (n+1) → ℝ) ∈
      convexHull ℝ (paperEndpointFeatureSet n a
        (fun i => (1-r)*a i+r*b i))}

abbrev PaperFeatureFailureWitnessSpace (m : ℕ) :=
  ℝ × ((Fin m → ℝ) × (Fin m → ℝ))

noncomputable def parametricPaperEndpointCombination
    (n : ℕ) (a b : ℕ → ℝ) (m : ℕ)
    (right : Fin m → Bool)
    (v : PaperFeatureFailureWitnessSpace m) :
    Fin (n+1) → ℝ :=
  ∑ i, v.2.2 i • paperCompactFeature n
    (if right i then (fun j => (1-v.1)*a j+v.1*b j) else a)
    (v.2.1 i)

def paperFeatureFailureWitnessBase (m : ℕ) :
    Set (PaperFeatureFailureWitnessSpace m) :=
  Set.Icc (0 : ℝ) 1 ×ˢ
    (Set.univ.pi (fun _ : Fin m => Set.Icc (0 : ℝ) 1) ×ˢ
      stdSimplex ℝ (Fin m))

def paperFeatureFailureWitnessDomain
    (n : ℕ) (a b : ℕ → ℝ) (m : ℕ)
    (right : Fin m → Bool) :
    Set (PaperFeatureFailureWitnessSpace m) :=
  paperFeatureFailureWitnessBase m ∩
    parametricPaperEndpointCombination n a b m right ⁻¹' {0}

def paperFeatureFailureWitnessParameters
    (n : ℕ) (a b : ℕ → ℝ) (m : ℕ)
    (right : Fin m → Bool) : Set ℝ :=
  Prod.fst '' paperFeatureFailureWitnessDomain n a b m right

theorem continuous_parametricPaperEndpointCombination
    (n : ℕ) (a b : ℕ → ℝ) (m : ℕ)
    (right : Fin m → Bool) :
    Continuous (parametricPaperEndpointCombination n a b m right) := by
  unfold parametricPaperEndpointCombination
  apply continuous_finset_sum
  intro i _
  apply Continuous.smul
  · exact (continuous_apply i).comp (continuous_snd.comp continuous_snd)
  · have hx : Continuous
        (fun v : PaperFeatureFailureWitnessSpace m => v.2.1 i) :=
      (continuous_apply i).comp (continuous_fst.comp continuous_snd)
    cases hright : right i
    · simp only [hright, Bool.false_eq_true, if_false]
      exact (paperCompactFeature_continuous n a).comp hx
    · simp only [hright, if_true]
      have heq : (fun v : PaperFeatureFailureWitnessSpace m =>
          paperCompactFeature n
            (fun j => (1-v.1)*a j+v.1*b j) (v.2.1 i)) =
          (fun v : PaperFeatureFailureWitnessSpace m =>
            (1-v.1) • paperCompactFeature n a (v.2.1 i) +
              v.1 • paperCompactFeature n b (v.2.1 i)) := by
        funext v
        exact paperCompactFeature_affine_denominator n a b v.1 (v.2.1 i)
      rw [heq]
      exact ((continuous_const.sub continuous_fst).smul
        ((paperCompactFeature_continuous n a).comp hx)).add
        (continuous_fst.smul
          ((paperCompactFeature_continuous n b).comp hx))

theorem paperFeatureFailureWitnessBase_compact
    (m : ℕ) :
    IsCompact (paperFeatureFailureWitnessBase m) := by
  exact isCompact_Icc.prod
    ((isCompact_univ_pi fun _ : Fin m => isCompact_Icc).prod
      (isCompact_stdSimplex (Fin m)))

theorem paperFeatureFailureWitnessParameters_compact
    (n : ℕ) (a b : ℕ → ℝ) (m : ℕ)
    (right : Fin m → Bool) :
    IsCompact (paperFeatureFailureWitnessParameters n a b m right) := by
  have hdomain : IsCompact
      (paperFeatureFailureWitnessDomain n a b m right) :=
    (paperFeatureFailureWitnessBase_compact m).inter_right
      (isClosed_singleton.preimage
        (continuous_parametricPaperEndpointCombination
          n a b m right))
  exact hdomain.image continuous_fst

theorem paperFeatureFailureParameters_eq_witness_union
    (n : ℕ) (a b : ℕ → ℝ) :
    paperFeatureFailureParameters n a b =
      ⋃ m : Fin (n+3), ⋃ right : Fin m.val → Bool,
        paperFeatureFailureWitnessParameters n a b m.val right := by
  apply Set.Subset.antisymm
  · intro r hr
    obtain ⟨m, hm, z, w, hz, _haff, hw, hsum, hbalance⟩ :=
      paperFeature_finite_convex_representation n hr.2
    have hchoice : ∀ i, ∃ right : Bool, ∃ u ∈ Set.Icc (0 : ℝ) 1,
        z i = paperCompactFeature n
          (if right then (fun j => (1-r)*a j+r*b j) else a) u := by
      intro i
      rcases hz i with ⟨u, hu, hzu⟩ | ⟨u, hu, hzu⟩
      · exact ⟨false, u, hu, hzu.symm⟩
      · exact ⟨true, u, hu, hzu.symm⟩
    choose right u hu heq using hchoice
    apply Set.mem_iUnion.mpr
    refine ⟨⟨m, by omega⟩, Set.mem_iUnion.mpr ⟨right, ?_⟩⟩
    refine ⟨(r, (u, w)), ?_, rfl⟩
    constructor
    · refine ⟨hr.1, ?_, ⟨(fun i => (hw i).le), hsum⟩⟩
      intro i _
      exact hu i
    · change parametricPaperEndpointCombination n a b m right
        (r, (u, w)) = 0
      simpa only [parametricPaperEndpointCombination, heq] using hbalance
  · intro r hr
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hr
    obtain ⟨right, hr⟩ := Set.mem_iUnion.mp hm
    obtain ⟨⟨v, u, w⟩, hdomain, hvr⟩ := hr
    subst r
    rcases hdomain.1 with ⟨hvIcc, hu, hw⟩
    have hbalance :
        parametricPaperEndpointCombination n a b m.val right
          (v, (u, w)) = 0 := by
      simpa only [Set.mem_singleton_iff] using hdomain.2
    refine ⟨hvIcc, ?_⟩
    rw [← hbalance]
    exact (convex_convexHull ℝ _).sum_mem
      (fun i _ => hw.1 i) hw.2
      (fun i _ => subset_convexHull ℝ _ (by
        cases h : right i
        · exact Or.inl (Set.mem_image_of_mem _
            (hu i (Set.mem_univ i)))
        · exact Or.inr (Set.mem_image_of_mem _
            (hu i (Set.mem_univ i)))))

theorem paperFeatureFailureParameters_compact
    (n : ℕ) (a b : ℕ → ℝ) :
    IsCompact (paperFeatureFailureParameters n a b) := by
  rw [paperFeatureFailureParameters_eq_witness_union]
  exact isCompact_iUnion fun m => isCompact_iUnion fun right =>
    paperFeatureFailureWitnessParameters_compact
      n a b m.val right

def paperFeaturePrecriticalUnion
    (n : ℕ) (a b : ℕ → ℝ) (u : ℝ) :
    Set (Fin (n+1) → ℝ) :=
  {z | ∃ v ∈ Set.Ico (0 : ℝ) u,
    z ∈ convexHull ℝ (paperEndpointFeatureSet n a
      (fun i => (1-v)*a i+v*b i))}

theorem paperFeaturePrecriticalUnion_convex
    (n : ℕ) (a b : ℕ → ℝ) (u : ℝ) :
    Convex ℝ (paperFeaturePrecriticalUnion n a b u) := by
  rw [convex_iff_segment_subset]
  intro x hx y hy z hz
  obtain ⟨v, hv, hx⟩ := hx
  obtain ⟨w, hw, hy⟩ := hy
  let m := max v w
  have hm : m ∈ Set.Ico (0 : ℝ) u :=
    ⟨le_trans hv.1 (le_max_left _ _), max_lt hv.2 hw.2⟩
  refine ⟨m, hm, ?_⟩
  apply (convex_convexHull ℝ _).segment_subset
  · exact paperFeature_convexHull_initial_mono n a b
      hv.1 (le_max_left _ _) hx
  · exact paperFeature_convexHull_initial_mono n a b
      hw.1 (le_max_right _ _) hy
  · exact hz

theorem closure_paperFeaturePrecriticalUnion
    (n : ℕ) (a b : ℕ → ℝ) {u : ℝ} (hu : 0 < u) :
    closure (paperFeaturePrecriticalUnion n a b u) =
      convexHull ℝ (paperEndpointFeatureSet n a
        (fun i => (1-u)*a i+u*b i)) := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro z ⟨v, hv, hz⟩
      exact paperFeature_convexHull_initial_mono n a b
        hv.1 hv.2.le hz
    · exact (compact_paperFeatureConvexHull n
        (paperEndpointFeatureSet_compact n a
          (fun i => (1-u)*a i+u*b i))).isClosed
  · apply convexHull_min
    · rintro z (hz | hz)
      · obtain ⟨x, hx, rfl⟩ := hz
        apply subset_closure
        refine ⟨u / 2, ⟨by linarith, by linarith⟩, ?_⟩
        exact subset_convexHull ℝ _
          (Or.inl (Set.mem_image_of_mem _ hx))
      · obtain ⟨x, hx, rfl⟩ := hz
        let f : ℝ → Fin (n+1) → ℝ := fun v =>
          paperCompactFeature n
            (fun i => (1-v)*a i+v*b i) x
        have hf : Continuous f := by
          have heq : f = (fun v : ℝ =>
              (1-v) • paperCompactFeature n a x +
                v • paperCompactFeature n b x) := by
            funext v
            exact paperCompactFeature_affine_denominator n a b v x
          rw [heq]
          exact ((continuous_const.sub continuous_id).smul
            continuous_const).add
            (continuous_id.smul continuous_const)
        have huClosure : u ∈ closure (Set.Ico (0 : ℝ) u) := by
          rw [closure_Ico hu.ne]
          exact ⟨hu.le, le_rfl⟩
        have hmap : Set.MapsTo f (Set.Ico (0 : ℝ) u)
            (paperFeaturePrecriticalUnion n a b u) := by
          intro v hv
          exact ⟨v, hv, subset_convexHull ℝ _
            (Or.inr (Set.mem_image_of_mem _ hx))⟩
        change f u ∈ closure (paperFeaturePrecriticalUnion n a b u)
        exact map_mem_closure (f := f) hf huClosure hmap
    · exact (paperFeaturePrecriticalUnion_convex n a b u).closure

theorem zero_mem_paperFeaturePrecriticalUnion_of_interior
    (n : ℕ) (a b : ℕ → ℝ) {u : ℝ} (hu : 0 < u)
    (hinterior : (0 : Fin (n+1) → ℝ) ∈
      interior (convexHull ℝ
        (paperEndpointFeatureSet n a
          (fun i => (1-u)*a i+u*b i)))) :
    (0 : Fin (n+1) → ℝ) ∈
      paperFeaturePrecriticalUnion n a b u := by
  let C := paperFeaturePrecriticalUnion n a b u
  let K := convexHull ℝ (paperEndpointFeatureSet n a
    (fun i => (1-u)*a i+u*b i))
  have hclosure : closure C = K :=
    closure_paperFeaturePrecriticalUnion n a b hu
  have hKconv : Convex ℝ K := convex_convexHull ℝ _
  have hKint : (interior K).Nonempty := ⟨0, hinterior⟩
  have hspanK : affineSpan ℝ K = ⊤ :=
    (hKconv.interior_nonempty_iff_affineSpan_eq_top).mp hKint
  have hCclosed : IsClosed
      ((affineSpan ℝ C : AffineSubspace ℝ (Fin (n+1) → ℝ)) :
        Set (Fin (n+1) → ℝ)) :=
    (affineSpan ℝ C).closed_of_finiteDimensional
  have hclosure_subset : closure C ⊆ affineSpan ℝ C :=
    closure_minimal (subset_affineSpan ℝ C) hCclosed
  have hspanC : affineSpan ℝ C = ⊤ := by
    apply top_unique
    rw [← hspanK, ← hclosure]
    exact affineSpan_le.2 hclosure_subset
  have hCconv : Convex ℝ C :=
    paperFeaturePrecriticalUnion_convex n a b u
  have hCint : (interior C).Nonempty :=
    (hCconv.interior_nonempty_iff_affineSpan_eq_top).2 hspanC
  have hinteriorEq :=
    hCconv.interior_closure_eq_interior_of_nonempty_interior hCint
  have hzeroClosure : (0 : Fin (n+1) → ℝ) ∈
      interior (closure C) := by
    rw [hclosure]
    exact hinterior
  rw [hinteriorEq] at hzeroClosure
  exact interior_subset hzeroClosure

theorem paperPolynomialSPR_self
    (n : ℕ) (a : ℕ → ℝ) (ha0 : a 0 = 1)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a)) :
    paperPolynomialSPR n
      (paperDescendingDenominator n a)
      (paperDescendingDenominator n a) := by
  have hdegree := paperDescendingDenominator_natDegree_eq n a ha0
  refine ⟨hdegree, hdegree, hstable, ?_⟩
  intro ω
  have hne := paperPolynomialHurwitz_imag_ne_zero _ hstable ω
  simp [div_self hne]

theorem zero_not_mem_paperFeatureFailureParameters
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ) (ha0 : a 0 = 1)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a)) :
    0 ∉ paperFeatureFailureParameters n a b := by
  intro hzero
  have hself : ∃ p : Polynomial ℝ,
      paperPolynomialSPR n p (paperDescendingDenominator n a) ∧
      paperPolynomialSPR n p (paperDescendingDenominator n a) := by
    exact ⟨paperDescendingDenominator n a,
      paperPolynomialSPR_self n a ha0 hstable,
      paperPolynomialSPR_self n a ha0 hstable⟩
  have hout := (paperCommonSPR_iff_feature_exclusion
    n hn a a ha0 ha0 hstable hstable).mp hself
  apply hout
  rw [closedConvexHull_eq_paperFeatureConvexHull n
    (paperEndpointFeatureSet_compact n a a)]
  simpa [paperFeatureFailureParameters] using hzero.2

theorem one_mem_paperFeatureFailureParameters_of_no_commonSPR
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hno : ¬ ∃ p : Polynomial ℝ,
      paperPolynomialSPR n p (paperDescendingDenominator n a) ∧
      paperPolynomialSPR n p (paperDescendingDenominator n b)) :
    1 ∈ paperFeatureFailureParameters n a b := by
  refine ⟨⟨zero_le_one, le_rfl⟩, ?_⟩
  have hclosed : (0 : Fin (n+1) → ℝ) ∈
      closedConvexHull ℝ (paperEndpointFeatureSet n a b) := by
    by_contra hzero
    exact hno ((paperCommonSPR_iff_feature_exclusion
      n hn a b ha0 hb0 hstableA hstableB).mpr hzero)
  rw [closedConvexHull_eq_paperFeatureConvexHull n
    (paperEndpointFeatureSet_compact n a b)] at hclosed
  simpa [paperFeatureFailureParameters] using hclosed

/-- A failed arbitrary-order synthesis problem has a first boundary contact
along the stable denominator segment. -/
theorem exists_first_paperFeature_failure
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hno : ¬ ∃ p : Polynomial ℝ,
      paperPolynomialSPR n p (paperDescendingDenominator n a) ∧
      paperPolynomialSPR n p (paperDescendingDenominator n b)) :
    ∃ u ∈ Set.Ioc (0 : ℝ) 1,
      (0 : Fin (n+1) → ℝ) ∈
        convexHull ℝ (paperEndpointFeatureSet n a
          (fun i => (1-u)*a i+u*b i)) ∧
      (0 : Fin (n+1) → ℝ) ∉
        interior (convexHull ℝ (paperEndpointFeatureSet n a
          (fun i => (1-u)*a i+u*b i))) := by
  have hnonempty : (paperFeatureFailureParameters n a b).Nonempty :=
    ⟨1, one_mem_paperFeatureFailureParameters_of_no_commonSPR
      n hn a b ha0 hb0 hstableA hstableB hno⟩
  obtain ⟨u, hu, hmin⟩ :=
    (paperFeatureFailureParameters_compact n a b).exists_isMinOn
      hnonempty continuous_id.continuousOn
  have hu_ne : u ≠ 0 := by
    intro huz
    subst u
    exact zero_not_mem_paperFeatureFailureParameters
      n hn a b ha0 hstableA hu
  have hu_pos : 0 < u := lt_of_le_of_ne hu.1.1 hu_ne.symm
  refine ⟨u, ⟨hu_pos, hu.1.2⟩, hu.2, ?_⟩
  intro hinterior
  obtain ⟨v, hv, hvzero⟩ :=
    zero_mem_paperFeaturePrecriticalUnion_of_interior
      n a b hu_pos hinterior
  have hvfail : v ∈ paperFeatureFailureParameters n a b :=
    ⟨⟨hv.1, hv.2.le.trans hu.1.2⟩, hvzero⟩
  have huv : u ≤ v := hmin hvfail
  exact (not_le_of_gt hv.2) huv

/-- If a positive-order common SPR numerator fails to exist, its first
failure along the denominator segment has at most `n+1` frequency atoms. -/
theorem paperFirstFailure_small_atom
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hno : ¬ ∃ p : Polynomial ℝ,
      paperPolynomialSPR n p (paperDescendingDenominator n a) ∧
      paperPolynomialSPR n p (paperDescendingDenominator n b)) :
    ∃ r ∈ Set.Ioc (0 : ℝ) 1,
      ∃ m : ℕ, m ≤ n+1 ∧
        ∃ (right : Fin m → Bool) (u w : Fin m → ℝ),
          (∀ i, u i ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
          (∑ i, w i • paperCompactFeature n
            (if right i then
              (fun j => (1-r)*a j+r*b j) else a) (u i)) = 0 := by
  obtain ⟨r, hr, hzero, hboundary⟩ :=
    exists_first_paperFeature_failure
      n hn a b ha0 hb0 hstableA hstableB hno
  have hclosed : (0 : Fin (n+1) → ℝ) ∈
      closedConvexHull ℝ
        (paperEndpointFeatureSet n a
          (fun j => (1-r)*a j+r*b j)) := by
    rw [closedConvexHull_eq_paperFeatureConvexHull n
      (paperEndpointFeatureSet_compact n a
        (fun j => (1-r)*a j+r*b j))]
    exact hzero
  obtain ⟨m, hm, right, u, w, hu, hw, hsum, hbalance⟩ :=
    (zero_boundary_paperEndpointFeature_iff_small_atom
      n a (fun j => (1-r)*a j+r*b j) hboundary).mp hclosed
  exact ⟨r, hr, m, hm, right, u, w, hu, hw, hsum, hbalance⟩



/-- A boundary contact of arbitrary order admits a nonzero supporting
numerator vector, nonnegative on both compact endpoint-frequency curves. -/
theorem paperEndpointFeature_boundary_support
    (n : ℕ) (a b : ℕ → ℝ)
    (hzero : (0 : Fin (n+1) → ℝ) ∈
      convexHull ℝ (paperEndpointFeatureSet n a b))
    (hboundary : (0 : Fin (n+1) → ℝ) ∉
      interior (convexHull ℝ (paperEndpointFeatureSet n a b))) :
    ∃ v : Fin (n+1) → ℝ, v ≠ 0 ∧
      ∀ z ∈ paperEndpointFeatureSet n a b,
        0 ≤ paperFeatureDot v z := by
  let K := convexHull ℝ (paperEndpointFeatureSet n a b)
  have hKconv : Convex ℝ K := convex_convexHull ℝ _
  have hKclosed : IsClosed K :=
    (compact_paperFeatureConvexHull n
      (paperEndpointFeatureSet_compact n a b)).isClosed
  by_cases hKint : (interior K).Nonempty
  · obtain ⟨f, hf⟩ := geometric_hahn_banach_point_open
      hKconv.interior isOpen_interior hboundary
    let v : Fin (n+1) → ℝ := fun i => f (Pi.single i 1)
    have hpos : ∀ z ∈ interior K, 0 < f z := by
      intro z hz
      simpa only [map_zero] using hf z hz
    have hclosureInterior : closure (interior K) = K := by
      rw [hKconv.closure_interior_eq_closure_of_nonempty_interior hKint,
        hKclosed.closure_eq]
    have hnonneg : ∀ z ∈ K, 0 ≤ f z := by
      have hclosedHalf : IsClosed
          {z : Fin (n+1) → ℝ | 0 ≤ f z} :=
        isClosed_le continuous_const f.continuous
      have hsub : closure (interior K) ⊆
          {z : Fin (n+1) → ℝ | 0 ≤ f z} :=
        closure_minimal (fun z hz => (hpos z hz).le) hclosedHalf
      intro z hz
      exact hsub (hclosureInterior.symm ▸ hz)
    refine ⟨v, ?_, ?_⟩
    · intro hv
      obtain ⟨z, hz⟩ := hKint
      have hfz : f z = 0 := by
        rw [paperFeatureDual_eq_dot]
        change paperFeatureDot v z = 0
        rw [hv]
        simp [paperFeatureDot]
      have := hpos z hz
      linarith
    · intro z hz
      rw [← paperFeatureDual_eq_dot]
      exact hnonneg z (subset_convexHull ℝ _ hz)
  · have hspan_ne : affineSpan ℝ K ≠ ⊤ := by
      intro hspan
      exact hKint ((hKconv.interior_nonempty_iff_affineSpan_eq_top).2 hspan)
    obtain ⟨y, hy⟩ : ∃ y : Fin (n+1) → ℝ,
        y ∉ affineSpan ℝ K := by
      apply (Set.ne_univ_iff_exists_not_mem
        ((affineSpan ℝ K : AffineSubspace ℝ (Fin (n+1) → ℝ)) :
          Set (Fin (n+1) → ℝ))).mp
      intro hcoe
      apply hspan_ne
      exact SetLike.coe_injective (by simpa using hcoe)
    obtain ⟨f, s, hfs, hsy⟩ := geometric_hahn_banach_closed_point
      (affineSpan ℝ K).convex
      (affineSpan ℝ K).closed_of_finiteDimensional hy
    have hzeroSpan : (0 : Fin (n+1) → ℝ) ∈ affineSpan ℝ K :=
      subset_affineSpan ℝ K hzero
    have hspos : 0 < s := by
      simpa only [map_zero] using hfs 0 hzeroSpan
    have fzero : ∀ z ∈ affineSpan ℝ K, f z = 0 := by
      intro z hz
      by_contra hfz
      let r : ℝ := (s + 1) / f z
      have hzdir : z ∈ (affineSpan ℝ K).direction := by
        simpa only [vsub_eq_sub, sub_zero] using
          (affineSpan ℝ K).vsub_mem_direction hz hzeroSpan
      have hrz : r • z ∈ affineSpan ℝ K := by
        have := (affineSpan ℝ K).vadd_mem_of_mem_direction
          ((affineSpan ℝ K).direction.smul_mem r hzdir) hzeroSpan
        simpa only [vadd_eq_add, add_zero] using this
      have hlt := hfs (r • z) hrz
      have hr : r * f z = s + 1 := by
        dsimp [r]
        exact div_mul_cancel₀ (s + 1) hfz
      rw [map_smul, smul_eq_mul, hr] at hlt
      linarith
    let v : Fin (n+1) → ℝ := fun i => f (Pi.single i 1)
    refine ⟨v, ?_, ?_⟩
    · intro hv
      have hfy : f y = 0 := by
        rw [paperFeatureDual_eq_dot]
        change paperFeatureDot v y = 0
        rw [hv]
        simp [paperFeatureDot]
      linarith
    · intro z hz
      have hzSpan : z ∈ affineSpan ℝ K :=
        subset_affineSpan ℝ K (subset_convexHull ℝ _ hz)
      rw [← paperFeatureDual_eq_dot, fzero z hzSpan]

/-- A finite boundary certificate for arbitrary polynomial degree. -/
structure PaperCriticalCertificate (n : ℕ) (a b : ℕ → ℝ) where
  atomCount : ℕ
  atomCount_le : atomCount ≤ n+1
  rightEndpoint : Fin atomCount → Bool
  compactFrequency : Fin atomCount → ℝ
  weight : Fin atomCount → ℝ
  support : Fin (n+1) → ℝ
  support_ne : support ≠ 0
  frequency_mem : ∀ i, compactFrequency i ∈ Set.Icc (0 : ℝ) 1
  weight_pos : ∀ i, 0 < weight i
  weight_sum : (∑ i, weight i) = 1
  balance : (∑ i, weight i •
    paperCompactFeature n (if rightEndpoint i then b else a)
      (compactFrequency i)) = 0
  support_nonneg_left : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    0 ≤ paperFeatureDot support (paperCompactFeature n a x)
  support_nonneg_right : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    0 ≤ paperFeatureDot support (paperCompactFeature n b x)
  support_zero_atom : ∀ i, paperFeatureDot support
    (paperCompactFeature n (if rightEndpoint i then b else a)
      (compactFrequency i)) = 0

theorem paperCriticalCertificate_of_boundary
    (n : ℕ) (a b : ℕ → ℝ)
    (hzero : (0 : Fin (n+1) → ℝ) ∈
      convexHull ℝ (paperEndpointFeatureSet n a b))
    (hboundary : (0 : Fin (n+1) → ℝ) ∉
      interior (convexHull ℝ (paperEndpointFeatureSet n a b))) :
    Nonempty (PaperCriticalCertificate n a b) := by
  have hclosed : (0 : Fin (n+1) → ℝ) ∈
      closedConvexHull ℝ (paperEndpointFeatureSet n a b) := by
    rw [closedConvexHull_eq_paperFeatureConvexHull n
      (paperEndpointFeatureSet_compact n a b)]
    exact hzero
  obtain ⟨m, hm, right, u, w, hu, hw, hsum, hbalance⟩ :=
    (zero_boundary_paperEndpointFeature_iff_small_atom
      n a b hboundary).mp hclosed
  obtain ⟨v, hv, hnonneg⟩ :=
    paperEndpointFeature_boundary_support n a b hzero hboundary
  have hatom : ∀ i, paperCompactFeature n
      (if right i then b else a) (u i) ∈
        paperEndpointFeatureSet n a b := by
    intro i
    cases h : right i
    · exact Or.inl (Set.mem_image_of_mem _ (hu i))
    · exact Or.inr (Set.mem_image_of_mem _ (hu i))
  have hnonneg' : ∀ i, 0 ≤ paperFeatureDot v
      (paperCompactFeature n (if right i then b else a) (u i)) := by
    intro i
    exact hnonneg _ (hatom i)
  have hsumdot :
      (∑ i, w i * paperFeatureDot v
        (paperCompactFeature n (if right i then b else a) (u i))) = 0 := by
    have h := congrArg (paperFeatureDotCLM v) hbalance
    simpa only [map_sum, map_smul, smul_eq_mul,
      paperFeatureDotCLM_apply, map_zero] using h
  have hzeroatom : ∀ i, paperFeatureDot v
      (paperCompactFeature n (if right i then b else a) (u i)) = 0 := by
    intro i
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hw j).le (hnonneg' j))).1 hsumdot i
        (Finset.mem_univ i)
    exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hw i))
  refine ⟨⟨m, hm, right, u, w, v, hv, hu, hw, hsum,
    hbalance, ?_, ?_, hzeroatom⟩⟩
  · intro x hx
    exact hnonneg _ (Or.inl (Set.mem_image_of_mem _ hx))
  · intro x hx
    exact hnonneg _ (Or.inr (Set.mem_image_of_mem _ hx))

theorem paperCriticalCertificate_at_first_failure
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hno : ¬ ∃ p : Polynomial ℝ,
      paperPolynomialSPR n p (paperDescendingDenominator n a) ∧
      paperPolynomialSPR n p (paperDescendingDenominator n b)) :
    ∃ r ∈ Set.Ioc (0 : ℝ) 1,
      Nonempty (PaperCriticalCertificate n a
        (fun j => (1-r)*a j+r*b j)) := by
  obtain ⟨r, hr, hzero, hboundary⟩ :=
    exists_first_paperFeature_failure
      n hn a b ha0 hb0 hstableA hstableB hno
  exact ⟨r, hr,
    paperCriticalCertificate_of_boundary n a
      (fun j => (1-r)*a j+r*b j) hzero hboundary⟩

lemma PaperCriticalCertificate.support_nonneg_selected
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (i : Fin C.atomCount) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ paperFeatureDot C.support
        (paperCompactFeature n
          (if C.rightEndpoint i then b else a) x) := by
  cases h : C.rightEndpoint i
  · simpa [h] using C.support_nonneg_left
  · simpa [h] using C.support_nonneg_right

/-- At every strictly positive finite contact, the ordinary cross polynomial
has a zero of multiplicity at least two. -/
theorem PaperCriticalCertificate.positive_contact_root_and_deriv
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (i : Fin C.atomCount)
    (hx0 : 0 < C.compactFrequency i)
    (hx1 : C.compactFrequency i < 1) :
    let d := if C.rightEndpoint i then b else a
    let p := paperRaisedCrossPolynomial n d
      (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
      (C.support 0)
    p.eval (C.compactFrequency i / (1 - C.compactFrequency i)) = 0 ∧
      deriv (fun t : ℝ => p.eval t)
        (C.compactFrequency i / (1 - C.compactFrequency i)) = 0 := by
  dsimp
  let d := if C.rightEndpoint i then b else a
  let p := paperRaisedCrossPolynomial n d
    (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
    (C.support 0)
  let x := C.compactFrequency i
  let t := x / (1-x)
  have hp : p.natDegree ≤ n :=
    paperRaisedCrossPolynomial_natDegree_le n d _ _
  have hcurve : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ paperHomogenizedPolynomial n p u := by
    intro u hu
    simpa [p, d, paperFeatureDot_compactFeature] using
      C.support_nonneg_selected i u hu
  have hzero : paperHomogenizedPolynomial n p x = 0 := by
    simpa [p, d, x, paperFeatureDot_compactFeature] using
      C.support_zero_atom i
  have hfactor : 0 < (1-x)^n := pow_pos (sub_pos.mpr hx1) n
  have hroot : p.eval t = 0 := by
    have heq := paperHomogenizedPolynomial_eq n p hp x (ne_of_lt hx1)
    rw [hzero] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_left (ne_of_gt hfactor)
  have hnonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ p.eval y := by
    intro y hy
    have hden : 0 < 1+y := by linarith
    have hu1 : y / (1+y) < 1 :=
      (div_lt_one hden).mpr (by linarith)
    have hu0 : 0 ≤ y / (1+y) := div_nonneg hy hden.le
    have hc := hcurve (y / (1+y)) ⟨hu0, hu1.le⟩
    rw [paperHomogenizedPolynomial_eq n p hp _ (ne_of_lt hu1)] at hc
    have hid : y / (1+y) / (1-y/(1+y)) = y := by
      field_simp
    rw [hid] at hc
    exact (mul_nonneg_iff_of_pos_left
      (pow_pos (sub_pos.mpr hu1) n)).mp hc
  have ht : 0 < t := div_pos hx0 (sub_pos.mpr hx1)
  have hmin : IsMinOn (fun y : ℝ => p.eval y) (Set.Ici (0 : ℝ)) t := by
    intro y hy
    simpa [hroot] using hnonneg y hy
  have hnhds : Set.Ici (0 : ℝ) ∈ nhds t :=
    Filter.mem_of_superset (Ioi_mem_nhds ht)
      (fun _ hy => Set.mem_Ici.mpr hy.le)
  exact ⟨hroot, (hmin.isLocalMin hnhds).deriv_eq_zero⟩



/-- For stable endpoints, failure of common synthesis is equivalent to a
finite critical certificate somewhere on the denominator segment. -/
theorem paperCommonSPR_iff_no_segment_critical_certificate
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    (∃ p : Polynomial ℝ,
      paperPolynomialSPR n p (paperDescendingDenominator n a) ∧
      paperPolynomialSPR n p (paperDescendingDenominator n b)) ↔
      ¬ ∃ r ∈ Set.Ioc (0 : ℝ) 1,
        Nonempty (PaperCriticalCertificate n a
          (fun j => (1-r)*a j+r*b j)) := by
  constructor
  · rintro ⟨p, hpA, hpB⟩ ⟨r, hr, ⟨C⟩⟩
    let d : ℕ → ℝ := fun j => (1-r)*a j+r*b j
    have hd0 : d 0 = 1 := by
      dsimp [d]
      rw [ha0, hb0]
      ring
    have hpD : paperPolynomialSPR n p
        (paperDescendingDenominator n d) :=
      paperTheorem2_commonSPR_on_segment n a b p ha0 hb0 hpA hpB
        r hr.1.le hr.2
    have hno := (paperCommonSPR_iff_no_atomContact
      n hn a d ha0 hd0 hpA.2.2.1 hpD.2.2.1).mp
        ⟨p, hpA, hpD⟩
    have hcontact : PaperGeneralAtomContact n a d := by
      refine ⟨C.atomCount, ?_, C.rightEndpoint,
        C.compactFrequency, C.weight,
        C.frequency_mem, C.weight_pos, C.weight_sum, ?_⟩
      · exact Nat.le_trans C.atomCount_le (by omega)
      · exact C.balance
    exact hno hcontact
  · intro hnone
    by_contra hno
    exact hnone (paperCriticalCertificate_at_first_failure
      n hn a b ha0 hb0 hstableA hstableB hno)



/-- A certificate formulation of the arbitrary-order robust synthesis goal.
Its remaining algebraic task is exclusion of the certificates. -/
theorem paperTheorem2_iff_no_segment_critical_certificate
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun i => (1-r)*a i+r*b i))) :
    (∃ p : Polynomial ℝ,
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        paperPolynomialSPR n p
          (paperDescendingDenominator n
            (fun i => (1-r)*a i+r*b i))) ↔
      ¬ ∃ r ∈ Set.Ioc (0 : ℝ) 1,
        Nonempty (PaperCriticalCertificate n a
          (fun j => (1-r)*a j+r*b j)) := by
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa using hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa using hsegment 1 (by norm_num) (by norm_num)
  rw [← paperCommonSPR_iff_no_segment_critical_certificate
    n hn a b ha0 hb0 hstableA hstableB]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_, ?_⟩
    · simpa using hp 0 (by norm_num) (by norm_num)
    · simpa using hp 1 (by norm_num) (by norm_num)
  · rintro ⟨p, hpA, hpB⟩
    exact ⟨p, paperTheorem2_commonSPR_on_segment
      n a b p ha0 hb0 hpA hpB⟩



/-- Every nonzero support cross polynomial has at most `n/2` distinct
positive real zeros.  The bound follows from nonnegativity on the half-line,
which makes each positive zero a multiple zero. -/
theorem PaperCriticalCertificate.positive_contact_card_bound
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (i : Fin C.atomCount)
    (hne : paperRaisedCrossPolynomial n
        (if C.rightEndpoint i then b else a)
        (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
        (C.support 0) ≠ 0) :
    2 * (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n
        (if C.rightEndpoint i then b else a)
        (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
        (C.support 0))).card ≤ n := by
  let d := if C.rightEndpoint i then b else a
  let p := paperRaisedCrossPolynomial n d
    (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
    (C.support 0)
  have hp : p.natDegree ≤ n :=
    paperRaisedCrossPolynomial_natDegree_le n d _ _
  have hcurve : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ paperHomogenizedPolynomial n p u := by
    intro u hu
    simpa [p, d, paperFeatureDot_compactFeature] using
      C.support_nonneg_selected i u hu
  have hnonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ p.eval y := by
    intro y hy
    have hden : 0 < 1+y := by linarith
    have hu1 : y / (1+y) < 1 :=
      (div_lt_one hden).mpr (by linarith)
    have hu0 : 0 ≤ y / (1+y) := div_nonneg hy hden.le
    have hc := hcurve (y / (1+y)) ⟨hu0, hu1.le⟩
    rw [paperHomogenizedPolynomial_eq n p hp _ (ne_of_lt hu1)] at hc
    have hid : y / (1+y) / (1-y/(1+y)) = y := by
      field_simp
    rw [hid] at hc
    exact (mul_nonneg_iff_of_pos_left
      (pow_pos (sub_pos.mpr hu1) n)).mp hc
  have hbound := MonicQuinticCoeff.twice_card_positiveRealRoots_le_natDegree
    p hne hnonneg
  exact hbound.trans hp

/-- The proved sixth-order synthesis theorem excludes every critical
certificate on a Hurwitz-stable sixth-order segment. -/
theorem sixth_order_stable_segment_excludes_critical_certificate
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator 6
          (fun i => (1-r)*a i+r*b i))) :
    ¬ ∃ r ∈ Set.Ioc (0 : ℝ) 1,
      Nonempty (PaperCriticalCertificate 6 a
        (fun j => (1-r)*a j+r*b j)) := by
  apply (paperTheorem2_iff_no_segment_critical_certificate
    6 (by norm_num) a b ha0 hb0 hsegment).mp
  exact (sixth_order_paper_coefficient_sequence a b ha0 hb0).mp hsegment



theorem paperCompactFeature_one
    (n : ℕ) (a : ℕ → ℝ) (ha0 : a 0 = 1) :
    paperCompactFeature n a 1 = Pi.single 0 1 := by
  ext i
  refine Fin.cases ?_ ?_ i
  · change paperHomogenizedPolynomial n (paperRaiseCorrection n a) 1 = 1
    rw [paperHomogenizedPolynomial_one,
      paperRaiseCorrection_coeff, if_pos le_rfl,
      paperRaiseProduct_top_coeff n a ha0, ← pow_add]
    simp
  · intro j
    change paperFiniteCompactCrossLinear n a 1
        (fun k => if j = k then 1 else 0) = 0
    rw [paperFiniteCompactCrossLinear_apply,
      paperHomogenizedPolynomial_one,
      paperGeneralCrossPolynomial_coeff, if_neg (by omega : ¬ n < n)]

lemma PaperCriticalCertificate.support_leading_nonneg
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (ha0 : a 0 = 1) :
    0 ≤ C.support 0 := by
  have h := C.support_nonneg_left 1 ⟨zero_le_one, le_rfl⟩
  rw [paperCompactFeature_one n a ha0] at h
  simpa [paperFeatureDot, Fin.sum_univ_succ, Pi.single_apply] using h

lemma PaperCriticalCertificate.exists_finite_frequency
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    ∃ i, C.compactFrequency i < 1 := by
  by_contra h
  push_neg at h
  have hx1 : ∀ i, C.compactFrequency i = 1 := by
    intro i
    exact le_antisymm (C.frequency_mem i).2 (h i)
  have hfeature : ∀ i,
      paperCompactFeature n
        (if C.rightEndpoint i then b else a)
        (C.compactFrequency i) = Pi.single 0 1 := by
    intro i
    rw [hx1]
    cases hright : C.rightEndpoint i
    · simpa [hright] using paperCompactFeature_one n a ha0
    · simpa [hright] using paperCompactFeature_one n b hb0
  have hcoord := congrFun C.balance 0
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply, hfeature, Pi.single_apply, Fin.isValue,
    if_pos, mul_one] at hcoord
  rw [C.weight_sum] at hcoord
  norm_num at hcoord



theorem paperHomogenizedPolynomial_zero
    (n : ℕ) (p : Polynomial ℝ) :
    paperHomogenizedPolynomial n p 0 = p.coeff 0 := by
  rw [paperHomogenizedPolynomial]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hne
    have hjpos : 0 < j := Nat.pos_of_ne_zero hne
    simp [Nat.ne_of_gt hjpos]
  · simp

theorem paperGeneralCoefficient_last
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) :
    paperGeneralCoefficient n a (paperPaddedNumerator n x) n =
      a n * x (n-1) := by
  unfold paperGeneralCoefficient
  rw [Finset.sum_eq_single_of_mem n (by simp)]
  · have hidx : 2*(n:ℤ)-(n:ℤ)-1 = (n-1:ℕ) := by omega
    rw [hidx]
    simp [paperPaddedNumerator, show n-1<n by omega,
      show n+n=2*n by omega, pow_mul]
  · intro j hj hne
    have hjlt : j < n := by
      have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      omega
    have hout : ¬ (2*(n:ℤ)-(j:ℤ)-1 < n) := by omega
    simp [paperPaddedNumerator, hout]

theorem paperRaiseCorrection_coeff_zero
    (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ) :
    (paperRaiseCorrection n a).coeff 0 = 0 := by
  rw [paperRaiseCorrection_coeff, if_pos (Nat.zero_le n)]
  simp only [pow_zero, one_mul]
  unfold paperRaiseProduct
  rw [Polynomial.coeff_X_pow_mul']
  simp [show ¬ n ≤ 0 by omega]

theorem paperFiniteCompactCrossLinear_zero
    (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ) (v : Fin n → ℝ) :
    paperFiniteCompactCrossLinear n a 0 v =
      a n * v ⟨n-1, by omega⟩ := by
  rw [paperFiniteCompactCrossLinear_apply,
    paperHomogenizedPolynomial_zero,
    paperGeneralCrossPolynomial_coeff,
    if_pos hn, Nat.sub_zero,
    paperGeneralCoefficient_last n hn]
  simp [paperFiniteNumeratorCoeffs, show n-1<n by omega]

theorem paperCompactFeature_zero_first
    (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ) :
    paperCompactFeature n a 0 0 = 0 := by
  change paperHomogenizedPolynomial n (paperRaiseCorrection n a) 0 = 0
  rw [paperHomogenizedPolynomial_zero,
    paperRaiseCorrection_coeff_zero n hn]

theorem paperCompactFeature_zero_last
    (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ) :
    paperCompactFeature n a 0 (Fin.last n) = a n := by
  let j : Fin n := ⟨n-1, by omega⟩
  have hidx : Fin.last n = Fin.succ j := by
    ext
    simp [j]
    omega
  rw [hidx]
  change paperFiniteCompactCrossLinear n a 0
    (fun k => if j = k then 1 else 0) = a n
  rw [paperFiniteCompactCrossLinear_zero n hn]
  simp [j]

theorem paperCompactFeature_endpoint_pairing_pos
    (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (ha0 : a 0 = 1)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (u : ℝ) (hu : u = 0 ∨ u = 1) :
    0 < paperCompactFeature n a u 0 +
      paperCompactFeature n a u (Fin.last n) := by
  rcases hu with rfl | rfl
  · rw [paperCompactFeature_zero_first n hn,
      paperCompactFeature_zero_last n hn]
    simpa using paperDescendingDenominator_const_pos_of_hurwitz
      n hn a ha0 hstable
  · rw [paperCompactFeature_one n a ha0]
    have hlast : Fin.last n ≠ (0 : Fin (n+1)) := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    simp [Pi.single_apply, hlast]

theorem PaperCriticalCertificate.exists_interior_frequency
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    ∃ i, 0 < C.compactFrequency i ∧ C.compactFrequency i < 1 := by
  by_contra hnone
  have hend : ∀ i, C.compactFrequency i = 0 ∨
      C.compactFrequency i = 1 := by
    intro i
    by_cases hzero : C.compactFrequency i = 0
    · exact Or.inl hzero
    · have hpos : 0 < C.compactFrequency i :=
        lt_of_le_of_ne (C.frequency_mem i).1 (Ne.symm hzero)
      have hnotlt : ¬ C.compactFrequency i < 1 := by
        intro hlt
        exact hnone ⟨i, hpos, hlt⟩
      exact Or.inr (le_antisymm (C.frequency_mem i).2
        (le_of_not_gt hnotlt))
  let L : (Fin (n+1) → ℝ) → ℝ :=
    fun z => z 0 + z (Fin.last n)
  have hpos : ∀ i, 0 < L
      (paperCompactFeature n
        (if C.rightEndpoint i then b else a)
        (C.compactFrequency i)) := by
    intro i
    cases hright : C.rightEndpoint i
    · exact paperCompactFeature_endpoint_pairing_pos
        n hn a ha0 hstableA _ (hend i)
    · exact paperCompactFeature_endpoint_pairing_pos
        n hn b hb0 hstableB _ (hend i)
  have hsumL :
      (∑ i, C.weight i * L
        (paperCompactFeature n
          (if C.rightEndpoint i then b else a)
          (C.compactFrequency i))) = 0 := by
    have h := congrArg L C.balance
    simpa [L, Finset.sum_add_distrib, mul_add] using h
  have hm : C.atomCount ≠ 0 := by
    intro hm
    have hsum := C.weight_sum
    haveI : IsEmpty (Fin C.atomCount) := by
      rw [hm]
      infer_instance
    simp at hsum
  let i : Fin C.atomCount := ⟨0, Nat.pos_of_ne_zero hm⟩
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_nonneg (C.weight_pos j).le (hpos j).le)).1
      hsumL i (Finset.mem_univ i)
  exact (ne_of_gt (mul_pos (C.weight_pos i) (hpos i))) hterm



/-- A hypothetical failure of arbitrary-order robust synthesis on a stable
segment forces a positive finite multiple contact at the first bad point. -/
theorem paperFirstFailure_positive_multiple_contact
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun j => (1-r)*a j+r*b j)))
    (hno : ¬ ∃ p : Polynomial ℝ,
      paperPolynomialSPR n p (paperDescendingDenominator n a) ∧
      paperPolynomialSPR n p (paperDescendingDenominator n b)) :
    ∃ r ∈ Set.Ioc (0 : ℝ) 1,
      ∃ C : PaperCriticalCertificate n a
          (fun j => (1-r)*a j+r*b j),
      ∃ i : Fin C.atomCount,
        0 < C.compactFrequency i ∧ C.compactFrequency i < 1 ∧
        (let d := if C.rightEndpoint i then
            (fun j => (1-r)*a j+r*b j) else a
         let p := paperRaisedCrossPolynomial n d
           (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
           (C.support 0)
         p.eval (C.compactFrequency i / (1 - C.compactFrequency i)) = 0 ∧
           deriv (fun t : ℝ => p.eval t)
             (C.compactFrequency i / (1 - C.compactFrequency i)) = 0) := by
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa using hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa using hsegment 1 (by norm_num) (by norm_num)
  obtain ⟨r, hr, ⟨C⟩⟩ := paperCriticalCertificate_at_first_failure
    n hn a b ha0 hb0 hstableA hstableB hno
  have hd0 : (fun j => (1-r)*a j+r*b j) 0 = 1 := by
    change (1-r)*a 0+r*b 0=1
    rw [ha0, hb0]
    ring
  have hstableD : paperPolynomialHurwitz
      (paperDescendingDenominator n
        (fun j => (1-r)*a j+r*b j)) :=
    hsegment r hr.1.le hr.2
  obtain ⟨i, hx0, hx1⟩ := C.exists_interior_frequency
    hn ha0 hd0 hstableA hstableD
  exact ⟨r, hr, C, i, hx0, hx1,
    C.positive_contact_root_and_deriv i hx0 hx1⟩



/-- Compact nonnegativity implies nonnegativity of the decompactified
cross polynomial on the real half-line. -/
theorem paperFeature_nonneg_cross_nonneg
    (n : ℕ) (a : ℕ → ℝ) (v : Fin (n+1) → ℝ)
    (hfeature : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ paperFeatureDot v (paperCompactFeature n a u)) :
    ∀ y : ℝ, 0 ≤ y →
      0 ≤ (paperRaisedCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n (fun j => v j.succ))
        (v 0)).eval y := by
  let p := paperRaisedCrossPolynomial n a
    (paperFiniteNumeratorCoeffs n (fun j => v j.succ)) (v 0)
  have hp : p.natDegree ≤ n :=
    paperRaisedCrossPolynomial_natDegree_le n a _ _
  have hcurve : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ paperHomogenizedPolynomial n p u := by
    intro u hu
    simpa [p, paperFeatureDot_compactFeature] using hfeature u hu
  intro y hy
  have hden : 0 < 1+y := by linarith
  have hu1 : y / (1+y) < 1 :=
    (div_lt_one hden).mpr (by linarith)
  have hu0 : 0 ≤ y / (1+y) := div_nonneg hy hden.le
  have hc := hcurve (y / (1+y)) ⟨hu0, hu1.le⟩
  rw [paperHomogenizedPolynomial_eq n p hp _ (ne_of_lt hu1)] at hc
  have hid : y / (1+y) / (1-y/(1+y)) = y := by
    field_simp
  rw [hid] at hc
  exact (mul_nonneg_iff_of_pos_left
    (pow_pos (sub_pos.mpr hu1) n)).mp hc

/-- An arbitrary-order nonnegative feature pairing gives the usual
positive-root multiplicity bound for its raised cross polynomial. -/
theorem paperFeature_nonneg_positiveRoots_bound
    (n : ℕ) (a : ℕ → ℝ) (v : Fin (n+1) → ℝ)
    (hfeature : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ paperFeatureDot v (paperCompactFeature n a u))
    (hne : paperRaisedCrossPolynomial n a
      (paperFiniteNumeratorCoeffs n (fun j => v j.succ)) (v 0) ≠ 0) :
    2 * (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n (fun j => v j.succ))
        (v 0))).card ≤ n := by
  let p := paperRaisedCrossPolynomial n a
    (paperFiniteNumeratorCoeffs n (fun j => v j.succ)) (v 0)
  have hp : p.natDegree ≤ n :=
    paperRaisedCrossPolynomial_natDegree_le n a _ _
  exact (MonicQuinticCoeff.twice_card_positiveRealRoots_le_natDegree
    p hne (paperFeature_nonneg_cross_nonneg n a v hfeature)).trans hp

theorem paperRaisedCrossPolynomial_natDegree_le_pred_of_top_zero
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) (ε : ℝ)
    (ha0 : a 0 = 1) (hε : ε = 0) :
    (paperRaisedCrossPolynomial n a x ε).natDegree ≤ n-1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  by_cases hmn : m = n
  · subst m
    rw [paperRaisedCrossPolynomial_top_coeff n a x ε ha0, hε]
  · have hgt : n < m := by omega
    exact Polynomial.natDegree_le_iff_coeff_eq_zero.mp
      (paperRaisedCrossPolynomial_natDegree_le n a x ε) m hgt

/-- If the highest support coefficient vanishes, a nonzero cross polynomial
has one lower degree and hence one fewer possible positive contact. -/
theorem paperFeature_nonneg_positiveRoots_bound_of_leading_zero
    (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (v : Fin (n+1) → ℝ) (ha0 : a 0 = 1) (hv0 : v 0 = 0)
    (hfeature : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ paperFeatureDot v (paperCompactFeature n a u))
    (hne : paperRaisedCrossPolynomial n a
      (paperFiniteNumeratorCoeffs n (fun j => v j.succ)) (v 0) ≠ 0) :
    2 * (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n (fun j => v j.succ))
        (v 0))).card ≤ n-1 := by
  let p := paperRaisedCrossPolynomial n a
    (paperFiniteNumeratorCoeffs n (fun j => v j.succ)) (v 0)
  have hp : p.natDegree ≤ n-1 :=
    paperRaisedCrossPolynomial_natDegree_le_pred_of_top_zero
      n hn a _ _ ha0 hv0
  exact (MonicQuinticCoeff.twice_card_positiveRealRoots_le_natDegree
    p hne (paperFeature_nonneg_cross_nonneg n a v hfeature)).trans hp

/-- With positive leading support coefficient, both endpoint cross
polynomials are nonzero and each has at most `n/2` positive roots. -/
theorem PaperCriticalCertificate.endpoint_positiveRoots_bounds_of_leading_pos
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hlead : 0 < C.support 0) :
    2 * (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
        (C.support 0))).card ≤ n ∧
    2 * (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n b
        (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
        (C.support 0))).card ≤ n := by
  have hneA : paperRaisedCrossPolynomial n a
      (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
      (C.support 0) ≠ 0 := by
    intro hz
    have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff n) hz
    change (paperRaisedCrossPolynomial n a
      (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
      (C.support 0)).coeff n = 0 at hcoeff
    rw [paperRaisedCrossPolynomial_top_coeff n a _ _ ha0] at hcoeff
    exact (ne_of_gt hlead) (by simpa using hcoeff)
  have hneB : paperRaisedCrossPolynomial n b
      (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
      (C.support 0) ≠ 0 := by
    intro hz
    have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff n) hz
    change (paperRaisedCrossPolynomial n b
      (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
      (C.support 0)).coeff n = 0 at hcoeff
    rw [paperRaisedCrossPolynomial_top_coeff n b _ _ hb0] at hcoeff
    exact (ne_of_gt hlead) (by simpa using hcoeff)
  exact ⟨paperFeature_nonneg_positiveRoots_bound
    n a C.support C.support_nonneg_left hneA,
    paperFeature_nonneg_positiveRoots_bound
      n b C.support C.support_nonneg_right hneB⟩

theorem PaperCriticalCertificate.endpoint_positiveRoots_bounds_of_leading_zero_of_nonzero
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hzero : C.support 0 = 0)
    (hneA : paperRaisedCrossPolynomial n a
      (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
      (C.support 0) ≠ 0)
    (hneB : paperRaisedCrossPolynomial n b
      (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
      (C.support 0) ≠ 0) :
    2 * (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
        (C.support 0))).card ≤ n-1 ∧
    2 * (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n b
        (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
        (C.support 0))).card ≤ n-1 := by
  exact ⟨paperFeature_nonneg_positiveRoots_bound_of_leading_zero
    n hn a C.support ha0 hzero C.support_nonneg_left hneA,
    paperFeature_nonneg_positiveRoots_bound_of_leading_zero
      n hn b C.support hb0 hzero C.support_nonneg_right hneB⟩



/-- A real Hurwitz polynomial is coprime to its reflection across the
imaginary axis.  This is the algebraic ingredient needed to rule out a
zero cross polynomial for a nonzero lower-degree numerator. -/
theorem paperPolynomialHurwitz_isCoprime_comp_neg
    (A : Polynomial ℝ) (hA : paperPolynomialHurwitz A) :
    IsCoprime A (A.comp (-Polynomial.X)) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    ℝ ℂ A (A.comp (-Polynomial.X))).2
  intro z
  by_cases hz : 0 ≤ z.re
  · exact Or.inl (hA z hz)
  · right
    have hneg : 0 ≤ (-z).re := by
      simp only [Complex.neg_re]
      exact (neg_pos.mpr (lt_of_not_ge hz)).le
    simpa [Polynomial.aeval_comp] using hA (-z) hneg



open ComplexConjugate

/-- A real polynomial vanishing at every imaginary-axis point vanishes
identically. -/
theorem paperPolynomial_eq_zero_of_aeval_jw_zero
    (q : Polynomial ℝ)
    (hq : ∀ ω : ℝ, (Polynomial.aeval (jw ω) q : ℂ) = 0) :
    q = 0 := by
  let Q : Polynomial ℂ := q.map (algebraMap ℝ ℂ)
  have hjw : Function.Injective jw := by
    intro x y hxy
    have him := congrArg Complex.im hxy
    simpa [jw] using him
  have hinf : Set.Infinite (Set.range jw) :=
    Set.infinite_range_of_injective hjw
  have hsubset : Set.range jw ⊆ {z : ℂ | Q.IsRoot z} := by
    rintro z ⟨ω, rfl⟩
    change Q.eval (jw ω) = 0
    simpa [Q, Polynomial.eval_map, Polynomial.aeval_def] using hq ω
  have hQ : Q = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot Q (hinf.mono hsubset)
  exact (Polynomial.map_eq_zero_iff
    (FaithfulSMul.algebraMap_injective ℝ ℂ)).mp hQ

noncomputable def paperReflectedEvenCross (P A : Polynomial ℝ) : Polynomial ℝ :=
  P * A.comp (-Polynomial.X) + P.comp (-Polynomial.X) * A

theorem paperRealPolynomial_aeval_comp_neg_jw
    (P : Polynomial ℝ) (ω : ℝ) :
    (Polynomial.aeval (jw ω) (P.comp (-Polynomial.X)) : ℂ) =
      conj (Polynomial.aeval (jw ω) P : ℂ) := by
  rw [← Polynomial.aeval_conj]
  simp only [Polynomial.aeval_comp, Polynomial.aeval_X]
  have hc : conj (jw ω) = -(jw ω) := by simp [jw]
  rw [hc]
  simp

theorem paperReflectedEvenCross_eq_zero_of_re_zero
    (P A : Polynomial ℝ)
    (hcross : ∀ ω : ℝ,
      ((Polynomial.aeval (jw ω) P : ℂ) *
        conj (Polynomial.aeval (jw ω) A : ℂ)).re = 0) :
    paperReflectedEvenCross P A = 0 := by
  apply paperPolynomial_eq_zero_of_aeval_jw_zero
  intro ω
  let z : ℂ := (Polynomial.aeval (jw ω) P : ℂ) *
    conj (Polynomial.aeval (jw ω) A : ℂ)
  have hz : z.re = 0 := hcross ω
  have hsum : z + conj z = 0 := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.conj_re, Complex.zero_re]
      rw [hz]
      norm_num
    · simp only [Complex.add_im, Complex.conj_im, Complex.zero_im]
      ring
  have hconjP := paperRealPolynomial_aeval_comp_neg_jw P ω
  have hconjA := paperRealPolynomial_aeval_comp_neg_jw A ω
  change (Polynomial.aeval (jw ω)
    (P * A.comp (-Polynomial.X) +
      P.comp (-Polynomial.X) * A) : ℂ) = 0
  simp only [Polynomial.aeval_add, Polynomial.aeval_mul]
  rw [hconjP, hconjA]
  simpa [z, mul_comm] using hsum

/-- A lower-degree numerator with identically zero boundary cross pairing
must itself vanish when the denominator is Hurwitz. -/
theorem paperHurwitz_numerator_eq_zero_of_cross_re_zero
    (A P : Polynomial ℝ)
    (hA : paperPolynomialHurwitz A)
    (hdeg : P.degree < A.degree)
    (hcross : ∀ ω : ℝ,
      ((Polynomial.aeval (jw ω) P : ℂ) *
        conj (Polynomial.aeval (jw ω) A : ℂ)).re = 0) :
    P = 0 := by
  have hQ := paperReflectedEvenCross_eq_zero_of_re_zero
    P A hcross
  have hcop := paperPolynomialHurwitz_isCoprime_comp_neg
    A hA
  have hdiv : A ∣ A.comp (-Polynomial.X) * P := by
    refine ⟨-(P.comp (-Polynomial.X)), ?_⟩
    calc
      A.comp (-Polynomial.X) * P =
          (P * A.comp (-Polynomial.X) +
            P.comp (-Polynomial.X) * A) -
              P.comp (-Polynomial.X) * A := by ring
      _ = A * -(P.comp (-Polynomial.X)) := by
        change paperReflectedEvenCross P A -
          P.comp (-Polynomial.X) * A = _
        rw [hQ]
        ring
  have hAP : A ∣ P := hcop.dvd_of_dvd_mul_left hdiv
  exact Polynomial.eq_zero_of_dvd_of_degree_lt hAP hdeg

theorem paperDescendingNumerator_natDegree_le
    (n : ℕ) (hn : 0 < n) (x : ℕ → ℝ) :
    (paperDescendingNumerator n x).natDegree ≤ n-1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [paperDescendingNumerator_coeff, if_neg (by omega : ¬ m < n)]

/-- Injectivity of the paper's cross-polynomial map at every stable
denominator: an identically zero cross forces the lower-degree numerator
to vanish. -/
theorem paperDescendingNumerator_eq_zero_of_cross_zero
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ)
    (ha0 : a 0 = 1)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hcross : paperGeneralCrossPolynomial n a x = 0) :
    paperDescendingNumerator n x = 0 := by
  let P := paperDescendingNumerator n x
  let A := paperDescendingDenominator n a
  have hPdegree : P.natDegree ≤ n-1 :=
    paperDescendingNumerator_natDegree_le n hn x
  have hAdegree : A.natDegree = n :=
    paperDescendingDenominator_natDegree_eq n a ha0
  have hAne : A ≠ 0 := by
    intro hz
    have h := congrArg (fun q : Polynomial ℝ => q.coeff n) hz
    change (paperDescendingDenominator n a).coeff n = 0 at h
    rw [paperDescendingDenominator_coeff, if_pos le_rfl,
      Nat.sub_self, ha0] at h
    norm_num at h
  have hdegree : P.degree < A.degree := by
    by_cases hPzero : P = 0
    · simp [hPzero, Polynomial.degree_eq_natDegree hAne,
        hAdegree]
      exact WithBot.bot_lt_coe n
    · rw [Polynomial.degree_eq_natDegree hPzero,
        Polynomial.degree_eq_natDegree hAne, hAdegree]
      exact_mod_cast (by omega : P.natDegree < n)
  apply paperHurwitz_numerator_eq_zero_of_cross_re_zero
    A P hstable hdegree
  intro ω
  change ((Polynomial.aeval (jw ω)
      (paperDescendingNumerator n x) : ℂ) *
    conj (Polynomial.aeval (jw ω)
      (paperDescendingDenominator n a) : ℂ)).re = 0
  rw [paperDescending_cross_identity n hn a x ω, hcross]
  simp

theorem paperFiniteNumeratorCoeffs_eq_zero_of_descending_zero
    (n : ℕ) (v : Fin n → ℝ)
    (hP : paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n v) = 0) :
    v = 0 := by
  ext i
  let m := n-1-i.val
  have hm : m < n := by dsimp [m]; omega
  have hrev : n-1-m = i.val := by dsimp [m]; omega
  have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff m) hP
  change (paperDescendingNumerator n
    (paperFiniteNumeratorCoeffs n v)).coeff m = 0 at hcoeff
  rw [paperDescendingNumerator_coeff, if_pos hm, hrev] at hcoeff
  simpa [paperFiniteNumeratorCoeffs, i.isLt] using hcoeff

/-- The support-to-cross map has trivial kernel for every monic Hurwitz
denominator and every positive order. -/
theorem paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (ha0 : a 0 = 1)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (v : Fin (n+1) → ℝ) (hv : v ≠ 0) :
    paperRaisedCrossPolynomial n a
      (paperFiniteNumeratorCoeffs n (fun j => v j.succ))
      (v 0) ≠ 0 := by
  intro hp
  have hv0 : v 0 = 0 := by
    have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff n) hp
    change (paperRaisedCrossPolynomial n a
      (paperFiniteNumeratorCoeffs n (fun j => v j.succ))
      (v 0)).coeff n = 0 at hcoeff
    rw [paperRaisedCrossPolynomial_top_coeff n a _ _ ha0] at hcoeff
    exact hcoeff
  have hcross : paperGeneralCrossPolynomial n a
      (paperFiniteNumeratorCoeffs n (fun j => v j.succ)) = 0 := by
    simpa [paperRaisedCrossPolynomial, hv0] using hp
  have hP := paperDescendingNumerator_eq_zero_of_cross_zero
    n hn a (paperFiniteNumeratorCoeffs n (fun j => v j.succ))
      ha0 hstable hcross
  have htail : (fun j : Fin n => v j.succ) = 0 :=
    paperFiniteNumeratorCoeffs_eq_zero_of_descending_zero
      n _ hP
  apply hv
  ext i
  refine Fin.cases ?_ ?_ i
  · simpa using hv0
  · intro j
    exact congrFun htail j



/-- On two stable endpoint denominators, the two support cross polynomials
are automatically nonzero and obey their positive-root bounds. -/
theorem PaperCriticalCertificate.endpoint_positiveRoots_bounds
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    2 * (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
        (C.support 0))).card ≤ n ∧
    2 * (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n b
        (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
        (C.support 0))).card ≤ n := by
  have hneA := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn a ha0 hstableA C.support C.support_ne
  have hneB := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn b hb0 hstableB C.support C.support_ne
  exact ⟨paperFeature_nonneg_positiveRoots_bound
    n a C.support C.support_nonneg_left hneA,
    paperFeature_nonneg_positiveRoots_bound
      n b C.support C.support_nonneg_right hneB⟩

theorem PaperCriticalCertificate.endpoint_positiveRoots_bounds_of_leading_zero
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hzero : C.support 0 = 0) :
    2 * (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
        (C.support 0))).card ≤ n-1 ∧
    2 * (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n b
        (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
        (C.support 0))).card ≤ n-1 := by
  have hneA := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn a ha0 hstableA C.support C.support_ne
  have hneB := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn b hb0 hstableB C.support C.support_ne
  exact C.endpoint_positiveRoots_bounds_of_leading_zero_of_nonzero
    hn ha0 hb0 hzero hneA hneB



noncomputable def PaperCriticalCertificate.positiveFiniteIndices
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) :
    Finset (Fin C.atomCount) :=
  Finset.univ.filter (fun i =>
    0 < C.compactFrequency i ∧ C.compactFrequency i < 1)

noncomputable def PaperCriticalCertificate.positiveFiniteNodes
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) : Finset ℝ :=
  C.positiveFiniteIndices.image (fun i =>
    C.compactFrequency i / (1-C.compactFrequency i))

theorem PaperCriticalCertificate.positiveFiniteNodes_subset_endpoint_roots
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    C.positiveFiniteNodes ⊆
      MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n a
          (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
          (C.support 0)) ∪
      MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n b
          (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
          (C.support 0)) := by
  have hneA := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn a ha0 hstableA C.support C.support_ne
  have hneB := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn b hb0 hstableB C.support C.support_ne
  intro t ht
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
  have hmem := Finset.mem_filter.mp hi
  have hx0 := hmem.2.1
  have hx1 := hmem.2.2
  have htpos : 0 < C.compactFrequency i /
      (1-C.compactFrequency i) :=
    div_pos hx0 (sub_pos.mpr hx1)
  have hroot := (C.positive_contact_root_and_deriv i hx0 hx1).1
  cases hright : C.rightEndpoint i
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨?_, htpos⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hneA]
    simpa [hright] using hroot
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨?_, htpos⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hneB]
    simpa [hright] using hroot

theorem PaperCriticalCertificate.positiveFiniteNodes_card_le_order
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    C.positiveFiniteNodes.card ≤ n := by
  have hsub := C.positiveFiniteNodes_subset_endpoint_roots
    hn ha0 hb0 hstableA hstableB
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
    (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
        (C.support 0)))
    (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n b
        (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
        (C.support 0)))
  have hbound := C.endpoint_positiveRoots_bounds
    hn ha0 hb0 hstableA hstableB
  omega

theorem PaperCriticalCertificate.positiveFiniteNodes_card_le_pred_of_leading_zero
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hzero : C.support 0 = 0) :
    C.positiveFiniteNodes.card ≤ n-1 := by
  have hsub := C.positiveFiniteNodes_subset_endpoint_roots
    hn ha0 hb0 hstableA hstableB
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
    (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
        (C.support 0)))
    (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n b
        (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
        (C.support 0)))
  have hbound := C.endpoint_positiveRoots_bounds_of_leading_zero
    hn ha0 hb0 hstableA hstableB hzero
  omega

theorem PaperCriticalCertificate.positiveFiniteNodes_nonempty
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    C.positiveFiniteNodes.Nonempty := by
  obtain ⟨i, hx0, hx1⟩ := C.exists_interior_frequency
    hn ha0 hb0 hstableA hstableB
  refine ⟨C.compactFrequency i / (1-C.compactFrequency i), ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨i, ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx0, hx1⟩



noncomputable def paperRealImagPolynomial (E O : Polynomial ℝ) :
    Polynomial ℝ :=
  E.comp (-(Polynomial.X^2)) +
    Polynomial.X * O.comp (-(Polynomial.X^2))

theorem paperRealImagPolynomial_aeval_sqrt
    (E O : Polynomial ℝ) (t : ℝ) (ht : 0 ≤ t) :
    (Polynomial.aeval (jw (Real.sqrt t))
      (paperRealImagPolynomial E O) : ℂ) =
      ((E.eval t : ℝ) : ℂ) +
        jw (Real.sqrt t) * ((O.eval t : ℝ) : ℂ) := by
  have hsq : (jw (Real.sqrt t))^2 = (-t : ℂ) := by
    rw [jw, mul_pow, Complex.I_sq]
    simp [← Complex.ofReal_pow, Real.sq_sqrt ht]
  simp only [paperRealImagPolynomial, Polynomial.aeval_add,
    Polynomial.aeval_mul, Polynomial.aeval_comp,
    Polynomial.aeval_X, map_neg, map_pow]
  rw [hsq]
  simp only [neg_neg]
  erw [Polynomial.aeval_ofReal (K := ℂ) E t,
    Polynomial.aeval_ofReal (K := ℂ) O t]
  rfl

noncomputable def paperRealImagInterpolant
    (s : Finset ℝ) (z : ℝ → ℂ) : Polynomial ℝ :=
  paperRealImagPolynomial
    (Lagrange.interpolate s id (fun t => (z t).re))
    (Lagrange.interpolate s id
      (fun t => (z t).im / Real.sqrt t))

theorem paperRealImagInterpolant_aeval_sqrt
    (s : Finset ℝ) (z : ℝ → ℂ)
    (hs : ∀ t ∈ s, 0 < t) {t : ℝ} (ht : t ∈ s) :
    (Polynomial.aeval (jw (Real.sqrt t))
      (paperRealImagInterpolant s z) : ℂ) = z t := by
  let E := Lagrange.interpolate s id (fun t => (z t).re)
  let O := Lagrange.interpolate s id
    (fun t => (z t).im / Real.sqrt t)
  have hinj : Set.InjOn (id : ℝ → ℝ) s :=
    Function.injective_id.injOn
  have hE : E.eval t = (z t).re := by
    exact Lagrange.eval_interpolate_at_node _ hinj ht
  have hO : O.eval t = (z t).im / Real.sqrt t := by
    exact Lagrange.eval_interpolate_at_node _ hinj ht
  have hroot : 0 < Real.sqrt t := Real.sqrt_pos.2 (hs t ht)
  change (Polynomial.aeval (jw (Real.sqrt t))
    (paperRealImagPolynomial E O) : ℂ) = z t
  rw [paperRealImagPolynomial_aeval_sqrt E O t (hs t ht).le,
    hE, hO]
  apply Complex.ext
  · simp [jw, Complex.add_re, Complex.mul_re]
  · simp [jw, Complex.add_im, Complex.mul_im]
    field_simp [ne_of_gt hroot]

theorem paperRealImagPolynomial_natDegree_le
    (E O : Polynomial ℝ) (k : ℕ)
    (hE : E.natDegree ≤ k) (hO : O.natDegree ≤ k) :
    (paperRealImagPolynomial E O).natDegree ≤ 2*k+1 := by
  let Q : Polynomial ℝ := -(Polynomial.X^2)
  have hQ : Q.natDegree = 2 := by simp [Q]
  have hEc : (E.comp Q).natDegree ≤ 2*k := by
    calc
      (E.comp Q).natDegree ≤ E.natDegree * Q.natDegree :=
        Polynomial.natDegree_comp_le
      _ = E.natDegree * 2 := by rw [hQ]
      _ ≤ 2*k := by omega
  have hOc : (O.comp Q).natDegree ≤ 2*k := by
    calc
      (O.comp Q).natDegree ≤ O.natDegree * Q.natDegree :=
        Polynomial.natDegree_comp_le
      _ = O.natDegree * 2 := by rw [hQ]
      _ ≤ 2*k := by omega
  have hXO : (Polynomial.X * O.comp Q).natDegree ≤ 2*k+1 := by
    calc
      (Polynomial.X * O.comp Q).natDegree ≤
          Polynomial.X.natDegree + (O.comp Q).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 2*k+1 := by simp; omega
  change (E.comp Q + Polynomial.X * O.comp Q).natDegree ≤ 2*k+1
  apply Polynomial.natDegree_add_le_of_degree_le
  · omega
  · exact hXO

theorem paperRealImagInterpolant_natDegree_le
    (s : Finset ℝ) (z : ℝ → ℂ) :
    (paperRealImagInterpolant s z).natDegree ≤
      2*(s.card-1)+1 := by
  have hinj : Set.InjOn (id : ℝ → ℝ) s :=
    Function.injective_id.injOn
  apply paperRealImagPolynomial_natDegree_le
  · exact Polynomial.natDegree_le_of_degree_le
      (Lagrange.degree_interpolate_le _ hinj)
  · exact Polynomial.natDegree_le_of_degree_le
      (Lagrange.degree_interpolate_le _ hinj)

noncomputable def paperPositiveNodeProduct
    (s : Finset ℝ) : Polynomial ℝ :=
  ∏ t ∈ s, (Polynomial.X^2 + Polynomial.C t)

theorem paperPositiveNodeProduct_monic
    (s : Finset ℝ) : (paperPositiveNodeProduct s).Monic := by
  unfold paperPositiveNodeProduct
  apply Polynomial.monic_prod_of_monic
  intro t ht
  exact Polynomial.monic_X_pow_add_C t (by norm_num : (2 : ℕ) ≠ 0)

theorem paperPositiveNodeProduct_natDegree
    (s : Finset ℝ) :
    (paperPositiveNodeProduct s).natDegree = 2*s.card := by
  unfold paperPositiveNodeProduct
  rw [Polynomial.natDegree_prod_of_monic]
  · simp
    omega
  · intro t ht
    exact Polynomial.monic_X_pow_add_C t (by norm_num : (2 : ℕ) ≠ 0)

theorem paperPositiveNodeProduct_eval_zero
    (s : Finset ℝ) :
    (paperPositiveNodeProduct s).eval 0 = ∏ t ∈ s, t := by
  simp [paperPositiveNodeProduct, Polynomial.eval_prod]

theorem paperPositiveNodeProduct_eval_zero_pos
    (s : Finset ℝ) (hs : ∀ t ∈ s, 0 < t) :
    0 < (paperPositiveNodeProduct s).eval 0 := by
  rw [paperPositiveNodeProduct_eval_zero]
  exact Finset.prod_pos fun t ht => hs t ht

theorem paperPositiveNodeProduct_aeval_sqrt_zero
    (s : Finset ℝ) {t : ℝ} (ht : t ∈ s) (htpos : 0 ≤ t) :
    (Polynomial.aeval (jw (Real.sqrt t))
      (paperPositiveNodeProduct s) : ℂ) = 0 := by
  unfold paperPositiveNodeProduct
  simp only [map_prod]
  apply Finset.prod_eq_zero ht
  simp [jw, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
    Real.sq_sqrt htpos]

theorem paperRealImagInterpolant_empty (z : ℝ → ℂ) :
    paperRealImagInterpolant ∅ z = 0 := by
  simp [paperRealImagInterpolant, paperRealImagPolynomial,
    Lagrange.interpolate_empty]

theorem paperRealImagInterpolant_coeff_zero_of_small_nodes
    (n : ℕ) (s : Finset ℝ)
    (hcard : 2*s.card ≤ n) (z : ℝ → ℂ) :
    (paperRealImagInterpolant s z).coeff n = 0 := by
  by_cases hs : s = ∅
  · simp [hs, paperRealImagInterpolant_empty]
  · have hk : 0 < s.card := Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr hs)
    have hdeg := paperRealImagInterpolant_natDegree_le s z
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (by omega : (paperRealImagInterpolant s z).natDegree < n)

theorem paperPositiveNodeProduct_coeff_top
    (s : Finset ℝ) :
    (paperPositiveNodeProduct s).coeff (2*s.card) = 1 := by
  rw [← paperPositiveNodeProduct_natDegree s]
  exact (paperPositiveNodeProduct_monic s).coeff_natDegree

noncomputable def paperPositiveInterpolationScale
    (s : Finset ℝ) (z : ℝ → ℂ) : ℝ :=
  (abs ((paperRealImagInterpolant s z).eval 0) + 1) /
    (paperPositiveNodeProduct s).eval 0

noncomputable def paperCorrectedInterpolant
    (n : ℕ) (s : Finset ℝ) (z : ℝ → ℂ) : Polynomial ℝ :=
  paperRealImagInterpolant s z +
    Polynomial.C (paperPositiveInterpolationScale s z) *
      paperPositiveNodeProduct s +
    Polynomial.X^(n-2*s.card) * paperPositiveNodeProduct s

theorem paperCorrectedInterpolant_aeval_sqrt
    (n : ℕ) (s : Finset ℝ) (z : ℝ → ℂ)
    (hs : ∀ t ∈ s, 0 < t) {t : ℝ} (ht : t ∈ s) :
    (Polynomial.aeval (jw (Real.sqrt t))
      (paperCorrectedInterpolant n s z) : ℂ) = z t := by
  have hR := paperPositiveNodeProduct_aeval_sqrt_zero
    s ht (hs t ht).le
  simp only [paperCorrectedInterpolant, Polynomial.aeval_add,
    Polynomial.aeval_mul, hR, mul_zero, add_zero]
  exact paperRealImagInterpolant_aeval_sqrt s z hs ht

theorem paperCorrectedInterpolant_eval_zero_pos
    (n : ℕ) (s : Finset ℝ) (z : ℝ → ℂ)
    (hs : ∀ t ∈ s, 0 < t) :
    0 < (paperCorrectedInterpolant n s z).eval 0 := by
  let I := paperRealImagInterpolant s z
  let R := paperPositiveNodeProduct s
  let δ := paperPositiveInterpolationScale s z
  have hR : 0 < R.eval 0 :=
    paperPositiveNodeProduct_eval_zero_pos s hs
  have hδR : δ * R.eval 0 = |I.eval 0| + 1 := by
    dsimp [δ, paperPositiveInterpolationScale, I, R]
    field_simp [ne_of_gt hR]
  have hpow : 0 ≤ (0 : ℝ)^(n-2*s.card) := by positivity
  have hlast : 0 ≤ (0 : ℝ)^(n-2*s.card) * R.eval 0 :=
    mul_nonneg hpow hR.le
  change 0 < (I + Polynomial.C δ * R +
      Polynomial.X^(n-2*s.card) * R).eval 0
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [hδR]
  nlinarith [neg_le_abs (I.eval 0)]

theorem paperCorrectedInterpolant_top_coeff_pos
    (n : ℕ) (s : Finset ℝ) (z : ℝ → ℂ)
    (hs : ∀ t ∈ s, 0 < t)
    (hcard : 2*s.card ≤ n) :
    0 < (paperCorrectedInterpolant n s z).coeff n := by
  let I := paperRealImagInterpolant s z
  let R := paperPositiveNodeProduct s
  let δ := paperPositiveInterpolationScale s z
  have hR : 0 < R.eval 0 :=
    paperPositiveNodeProduct_eval_zero_pos s hs
  have hδ : 0 < δ := by
    dsimp [δ, paperPositiveInterpolationScale, I, R]
    exact div_pos (by positivity) hR
  have hIcoeff : I.coeff n = 0 :=
    paperRealImagInterpolant_coeff_zero_of_small_nodes
      n s hcard z
  have hRtop : R.coeff (2*s.card) = 1 :=
    paperPositiveNodeProduct_coeff_top s
  have hXcoeff :
      (Polynomial.X^(n-2*s.card) * R).coeff n = 1 := by
    have hsum : 2*s.card+(n-2*s.card)=n := by omega
    calc
      (Polynomial.X^(n-2*s.card) * R).coeff n =
          (Polynomial.X^(n-2*s.card) * R).coeff
            (2*s.card+(n-2*s.card)) := by rw [hsum]
      _ = R.coeff (2*s.card) := by
        rw [Polynomial.coeff_X_pow_mul]
      _ = 1 := hRtop
  change 0 < (I + Polynomial.C δ * R +
    Polynomial.X^(n-2*s.card) * R).coeff n
  rw [Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, hIcoeff, hXcoeff]
  by_cases heq : n = 2*s.card
  · rw [heq, hRtop]
    nlinarith
  · have hRzero : R.coeff n = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [paperPositiveNodeProduct_natDegree]
      omega
    rw [hRzero]
    norm_num

theorem paperCorrectedInterpolant_natDegree_le
    (n : ℕ) (hn : 0 < n) (s : Finset ℝ) (z : ℝ → ℂ)
    (hcard : 2*s.card ≤ n) :
    (paperCorrectedInterpolant n s z).natDegree ≤ n := by
  let I := paperRealImagInterpolant s z
  let R := paperPositiveNodeProduct s
  let δ := paperPositiveInterpolationScale s z
  have hI : I.natDegree ≤ n :=
    (paperRealImagInterpolant_natDegree_le s z).trans
      (by omega)
  have hR : R.natDegree ≤ n := by
    rw [paperPositiveNodeProduct_natDegree]
    exact hcard
  have hδR : (Polynomial.C δ * R).natDegree ≤ n := by
    have h := Polynomial.natDegree_mul_le
      (p := Polynomial.C δ) (q := R)
    rw [Polynomial.natDegree_C] at h
    omega
  have hXR : (Polynomial.X^(n-2*s.card) * R).natDegree ≤ n := by
    have h := Polynomial.natDegree_mul_le
      (p := Polynomial.X^(n-2*s.card)) (q := R)
    rw [Polynomial.natDegree_X_pow] at h
    have hRdegree := paperPositiveNodeProduct_natDegree s
    rw [hRdegree] at h
    omega
  change (I + Polynomial.C δ * R +
    Polynomial.X^(n-2*s.card) * R).natDegree ≤ n
  exact Polynomial.natDegree_add_le_of_degree_le
    (Polynomial.natDegree_add_le_of_degree_le hI hδR) hXR

theorem paperCorrectedInterpolant_natDegree_eq
    (n : ℕ) (hn : 0 < n) (s : Finset ℝ) (z : ℝ → ℂ)
    (hs : ∀ t ∈ s, 0 < t)
    (hcard : 2*s.card ≤ n) :
    (paperCorrectedInterpolant n s z).natDegree = n := by
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (paperCorrectedInterpolant_natDegree_le n hn s z hcard)
    (ne_of_gt (paperCorrectedInterpolant_top_coeff_pos
      n s z hs hcard))

theorem paper_exists_interpolating_numerator_with_positive_endpoints
    (n : ℕ) (hn : 0 < n) (s : Finset ℝ) (z : ℝ → ℂ)
    (hs : ∀ t ∈ s, 0 < t)
    (hcard : 2*s.card ≤ n) :
    ∃ P : Polynomial ℝ,
      P.natDegree = n ∧ 0 < P.coeff n ∧ 0 < P.eval 0 ∧
        ∀ t ∈ s,
          (Polynomial.aeval (jw (Real.sqrt t)) P : ℂ) = z t := by
  exact ⟨paperCorrectedInterpolant n s z,
    paperCorrectedInterpolant_natDegree_eq n hn s z hs hcard,
    paperCorrectedInterpolant_top_coeff_pos n s z hs hcard,
    paperCorrectedInterpolant_eval_zero_pos n s z hs,
    fun t ht => paperCorrectedInterpolant_aeval_sqrt
      n s z hs ht⟩



noncomputable def paperPolynomialSupport
    (n : ℕ) (P : Polynomial ℝ) : Fin (n+1) → ℝ :=
  Fin.cons (P.coeff n)
    (fun i => paperNumeratorCoordinates n P i)

theorem paperPolynomialSupport_cross
    (n : ℕ) (a : ℕ → ℝ) (P : Polynomial ℝ) :
    paperRaisedCrossPolynomial n a
      (paperFiniteNumeratorCoeffs n
        (fun j => (paperPolynomialSupport n P) j.succ))
      ((paperPolynomialSupport n P) 0) =
    paperRaisedCrossPolynomial n a
      (paperNumeratorCoordinates n P) (P.coeff n) := by
  simp only [paperPolynomialSupport, Fin.cons_zero, Fin.cons_succ]
  unfold paperRaisedCrossPolynomial
  congr 1
  apply paperGeneralCrossPolynomial_eq_of_below
  intro i hi
  simp [paperFiniteNumeratorCoeffs, hi]

theorem paperPolynomialSupport_feature_at_one
    (n : ℕ) (a : ℕ → ℝ) (ha0 : a 0 = 1)
    (P : Polynomial ℝ) :
    paperFeatureDot (paperPolynomialSupport n P)
      (paperCompactFeature n a 1) = P.coeff n := by
  rw [paperCompactFeature_one n a ha0]
  simp [paperFeatureDot, paperPolynomialSupport,
    Fin.sum_univ_succ, Pi.single_apply]

theorem paperPolynomialSupport_feature_pos_of_phase
    (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (P : Polynomial ℝ) (hP : P.natDegree ≤ n)
    (t : ℝ) (ht : 0 ≤ t)
    (hphase : 0 < ((Polynomial.aeval (jw (Real.sqrt t)) P : ℂ) /
      Polynomial.aeval (jw (Real.sqrt t))
        (paperDescendingDenominator n a)).re) :
    0 < paperFeatureDot (paperPolynomialSupport n P)
      (paperCompactFeature n a (t/(1+t))) := by
  let x := paperNumeratorCoordinates n P
  let ε := P.coeff n
  let D := paperDescendingDenominator n a
  let Q := paperRaisedCrossPolynomial n a x ε
  have hden : 0 < 1+t := by linarith
  have hu1 : t/(1+t) < 1 :=
    (div_lt_one hden).mpr (by linarith)
  have hfactor : t/(1+t)/(1-t/(1+t)) = t := by
    field_simp
  have hDne : (Polynomial.aeval (jw (Real.sqrt t)) D : ℂ) ≠ 0 :=
    paperPolynomialHurwitz_imag_ne_zero D hstable _
  have hnorm : 0 < Complex.normSq
      (Polynomial.aeval (jw (Real.sqrt t)) D : ℂ) :=
    Complex.normSq_pos.mpr hDne
  have hcross : 0 < Q.eval t := by
    have heq := paperDescending_degree_raised_re n hn a x ε
      (Real.sqrt t)
    rw [← paperNumerator_coordinates_repr n P hP,
      Real.sq_sqrt ht] at heq
    have hquot : 0 < Q.eval t /
        Complex.normSq
          (Polynomial.aeval (jw (Real.sqrt t)) D : ℂ) := by
      rw [heq] at hphase
      simpa [D, Q, x, ε, paperRaisedCrossPolynomial,
        Polynomial.eval_add, Polynomial.eval_C_mul] using hphase
    exact (div_pos_iff_of_pos_right hnorm).mp hquot
  rw [paperFeatureDot_compactFeature,
    paperPolynomialSupport_cross]
  rw [paperHomogenizedPolynomial_eq n Q
    (paperRaisedCrossPolynomial_natDegree_le n a x ε)
      (t/(1+t)) (ne_of_lt hu1), hfactor]
  exact mul_pos (pow_pos (sub_pos.mpr hu1) n) hcross

theorem paperPolynomialSupport_feature_at_zero
    (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (P : Polynomial ℝ) :
    paperFeatureDot (paperPolynomialSupport n P)
      (paperCompactFeature n a 0) = a n * P.eval 0 := by
  rw [paperFeatureDot_compactFeature,
    paperPolynomialSupport_cross,
    paperHomogenizedPolynomial_zero]
  rw [paperRaisedCrossPolynomial, Polynomial.coeff_add,
    paperGeneralCrossPolynomial_coeff, if_pos hn,
    Nat.sub_zero, paperGeneralCoefficient_last n hn,
    Polynomial.coeff_C_mul,
    paperRaiseCorrection_coeff_zero n hn]
  simp [paperNumeratorCoordinates,
    show n-1<n by omega, Polynomial.coeff_zero_eq_eval_zero]



/-- A stable segment cannot have a critical certificate with too few
distinct positive finite contacts.  The contradiction uses polynomial
interpolation of the pointwise common positive phase. -/
theorem PaperCriticalCertificate.low_contact_excluded
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun j => (1-r)*a j+r*b j))) :
    n < 2*C.positiveFiniteNodes.card := by
  by_contra hnot
  have hcard : 2*C.positiveFiniteNodes.card ≤ n := by omega
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa using hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa using hsegment 1 (by norm_num) (by norm_num)
  have hnodes : ∀ t ∈ C.positiveFiniteNodes, 0 < t := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    have hfreq := (Finset.mem_filter.mp hi).2
    exact div_pos hfreq.1 (sub_pos.mpr hfreq.2)
  let z : ℝ → ℂ := fun t =>
    paperPointwiseBisector n a b (Real.sqrt t)
  obtain ⟨P, hPdeg, hPtop, hPzero, hinterp⟩ :=
    paper_exists_interpolating_numerator_with_positive_endpoints
      n hn C.positiveFiniteNodes z hnodes hcard
  let v := paperPolynomialSupport n P
  have hpos : ∀ i : Fin C.atomCount,
      0 < paperFeatureDot v
        (paperCompactFeature n
          (if C.rightEndpoint i then b else a)
          (C.compactFrequency i)) := by
    intro i
    let d := if C.rightEndpoint i then b else a
    have hd0 : d 0 = 1 := by
      cases hright : C.rightEndpoint i
      · simpa [d, hright] using ha0
      · simpa [d, hright] using hb0
    have hstableD : paperPolynomialHurwitz
        (paperDescendingDenominator n d) := by
      cases hright : C.rightEndpoint i
      · simpa [d, hright] using hstableA
      · simpa [d, hright] using hstableB
    by_cases hxi : C.compactFrequency i = 1
    · have htop := paperPolynomialSupport_feature_at_one
        n d hd0 P
      simpa [d, v, hxi, htop] using hPtop
    by_cases hx0 : C.compactFrequency i = 0
    · have hconst := paperDescendingDenominator_const_pos_of_hurwitz
        n hn d hd0 hstableD
      have hzero := paperPolynomialSupport_feature_at_zero
        n hn d P
      rw [hx0]
      rw [hzero]
      exact mul_pos hconst hPzero
    have hxlt : C.compactFrequency i < 1 :=
      lt_of_le_of_ne (C.frequency_mem i).2 hxi
    have hxpos : 0 < C.compactFrequency i :=
      lt_of_le_of_ne (C.frequency_mem i).1 (Ne.symm hx0)
    let t := C.compactFrequency i /
      (1-C.compactFrequency i)
    have htpos : 0 < t := div_pos hxpos (sub_pos.mpr hxlt)
    have htmem : t ∈ C.positiveFiniteNodes := by
      apply Finset.mem_image.mpr
      refine ⟨i, ?_, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, hxpos, hxlt⟩
    have hbis := paperStableSegment_pointwise_bisector_positive
      n a b hsegment (Real.sqrt t)
    have hphase :
        0 < ((Polynomial.aeval (jw (Real.sqrt t)) P : ℂ) /
          Polynomial.aeval (jw (Real.sqrt t))
            (paperDescendingDenominator n d)).re := by
      cases hright : C.rightEndpoint i
      · simpa [d, hright, hinterp t htmem, z] using hbis.1
      · simpa [d, hright, hinterp t htmem, z] using hbis.2
    have hfreqpos := paperPolynomialSupport_feature_pos_of_phase
      n hn d hstableD P (le_of_eq hPdeg) t htpos.le hphase
    have hback : t/(1+t) = C.compactFrequency i := by
      dsimp [t]
      have hden : 1-C.compactFrequency i ≠ 0 :=
        ne_of_gt (sub_pos.mpr hxlt)
      field_simp [hden]
    simpa [d, v, hback] using hfreqpos
  have hsumdot :
      (∑ i, C.weight i * paperFeatureDot v
        (paperCompactFeature n
          (if C.rightEndpoint i then b else a)
          (C.compactFrequency i))) = 0 := by
    have h := congrArg (paperFeatureDotCLM v) C.balance
    simpa only [map_sum, map_smul, smul_eq_mul,
      paperFeatureDotCLM_apply, map_zero] using h
  have hm : C.atomCount ≠ 0 := by
    intro hm
    have hsum := C.weight_sum
    haveI : IsEmpty (Fin C.atomCount) := by
      rw [hm]
      infer_instance
    simp at hsum
  let i : Fin C.atomCount := ⟨0, Nat.pos_of_ne_zero hm⟩
  have hsumpos : 0 < (∑ i, C.weight i * paperFeatureDot v
        (paperCompactFeature n
          (if C.rightEndpoint i then b else a)
          (C.compactFrequency i))) := by
    apply Finset.sum_pos
    · intro j hj
      exact mul_pos (C.weight_pos j) (hpos j)
    · exact ⟨i, Finset.mem_univ i⟩
  exact (ne_of_gt hsumpos) hsumdot



/-- At the first failure of common synthesis, every finite certificate
must use more than half the degree many distinct positive nodes. -/
theorem paperFirstFailure_many_positive_nodes
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun j => (1-r)*a j+r*b j)))
    (hno : ¬ ∃ p : Polynomial ℝ,
      paperPolynomialSPR n p (paperDescendingDenominator n a) ∧
      paperPolynomialSPR n p (paperDescendingDenominator n b)) :
    ∃ r ∈ Set.Ioc (0 : ℝ) 1,
      ∃ C : PaperCriticalCertificate n a
          (fun j => (1-r)*a j+r*b j),
        n < 2*C.positiveFiniteNodes.card ∧
        C.positiveFiniteNodes.card ≤ n := by
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa using hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa using hsegment 1 (by norm_num) (by norm_num)
  obtain ⟨r, hr, ⟨C⟩⟩ := paperCriticalCertificate_at_first_failure
    n hn a b ha0 hb0 hstableA hstableB hno
  let d : ℕ → ℝ := fun j => (1-r)*a j+r*b j
  have hd0 : d 0 = 1 := by
    dsimp [d]
    rw [ha0, hb0]
    ring
  have hdStable : paperPolynomialHurwitz
      (paperDescendingDenominator n d) :=
    hsegment r hr.1.le hr.2
  have hinitial : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun j => (1-s)*a j+s*d j)) := by
    intro s hs0 hs1
    have hsr0 : 0 ≤ s*r := mul_nonneg hs0 hr.1.le
    have hsr1 : s*r ≤ 1 := by
      calc
        s*r ≤ s*1 := mul_le_mul_of_nonneg_left hr.2 hs0
        _ = s := by ring
        _ ≤ 1 := hs1
    have heq : (fun j => (1-s)*a j+s*d j) =
        (fun j => (1-s*r)*a j+(s*r)*b j) := by
      funext j
      dsimp [d]
      ring
    rw [heq]
    exact hsegment (s*r) hsr0 hsr1
  have hmany : n < 2*C.positiveFiniteNodes.card :=
    C.low_contact_excluded hn ha0 hd0 hinitial
  have hfew : C.positiveFiniteNodes.card ≤ n :=
    C.positiveFiniteNodes_card_le_order
      hn ha0 hd0 hstableA hdStable
  exact ⟨r, hr, C, hmany, hfew⟩



/-- A stable-segment critical certificate has an interior-frequency contact
on each of the two endpoint feature curves. -/
theorem PaperCriticalCertificate.interior_contacts_on_both_endpoints
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun j => (1-r)*a j+r*b j))) :
    (∃ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1 ∧
      C.rightEndpoint i = false) ∧
    (∃ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1 ∧
      C.rightEndpoint i = true) := by
  have hmany := C.low_contact_excluded hn ha0 hb0 hsegment
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa using hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa using hsegment 1 (by norm_num) (by norm_num)
  let pA := paperRaisedCrossPolynomial n a
    (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
    (C.support 0)
  let pB := paperRaisedCrossPolynomial n b
    (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
    (C.support 0)
  have hneA : pA ≠ 0 :=
    paperRaisedCrossPolynomial_ne_zero_of_hurwitz
      n hn a ha0 hstableA C.support C.support_ne
  have hneB : pB ≠ 0 :=
    paperRaisedCrossPolynomial_ne_zero_of_hurwitz
      n hn b hb0 hstableB C.support C.support_ne
  have hbounds := C.endpoint_positiveRoots_bounds
    hn ha0 hb0 hstableA hstableB
  constructor
  · by_contra hno
    have hsub : C.positiveFiniteNodes ⊆
        MonicQuinticCoeff.positiveRealRoots pB := by
      intro t ht
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
      have hf := (Finset.mem_filter.mp hi).2
      have hright : C.rightEndpoint i = true := by
        cases h : C.rightEndpoint i
        · exact False.elim (hno ⟨i, hf.1, hf.2, h⟩)
        · rfl
      have hroot := (C.positive_contact_root_and_deriv i hf.1 hf.2).1
      apply Finset.mem_filter.mpr
      refine ⟨?_, div_pos hf.1 (sub_pos.mpr hf.2)⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hneB]
      simpa [pB, hright] using hroot
    have hcard := Finset.card_le_card hsub
    have hbound : 2 * (MonicQuinticCoeff.positiveRealRoots pB).card ≤ n :=
      hbounds.2
    omega
  · by_contra hno
    have hsub : C.positiveFiniteNodes ⊆
        MonicQuinticCoeff.positiveRealRoots pA := by
      intro t ht
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
      have hf := (Finset.mem_filter.mp hi).2
      have hright : C.rightEndpoint i = false := by
        cases h : C.rightEndpoint i
        · rfl
        · exact False.elim (hno ⟨i, hf.1, hf.2, h⟩)
      have hroot := (C.positive_contact_root_and_deriv i hf.1 hf.2).1
      apply Finset.mem_filter.mpr
      refine ⟨?_, div_pos hf.1 (sub_pos.mpr hf.2)⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hneA]
      simpa [pA, hright] using hroot
    have hcard := Finset.card_le_card hsub
    have hbound : 2 * (MonicQuinticCoeff.positiveRealRoots pA).card ≤ n :=
      hbounds.1
    omega



/-- The remaining arbitrary-order synthesis obstruction can be restricted to
critical certificates with more than half the degree many finite contacts. -/
theorem paperTheorem2_iff_no_high_contact_certificate
    (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun j => (1-r)*a j+r*b j))) :
    (∃ p : Polynomial ℝ,
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        paperPolynomialSPR n p
          (paperDescendingDenominator n
            (fun j => (1-r)*a j+r*b j))) ↔
      ¬ ∃ r ∈ Set.Ioc (0 : ℝ) 1,
        ∃ C : PaperCriticalCertificate n a
            (fun j => (1-r)*a j+r*b j),
          n < 2*C.positiveFiniteNodes.card := by
  constructor
  · intro ⟨p, hp⟩ ⟨r, hr, C, _⟩
    have hstableA : paperPolynomialHurwitz
        (paperDescendingDenominator n a) := by
      simpa using hsegment 0 (by norm_num) (by norm_num)
    have hstableB : paperPolynomialHurwitz
        (paperDescendingDenominator n b) := by
      simpa using hsegment 1 (by norm_num) (by norm_num)
    have hno := (paperCommonSPR_iff_no_segment_critical_certificate
      n hn a b ha0 hb0 hstableA hstableB).mp
        ⟨p, by simpa using hp 0 (by norm_num) (by norm_num),
          by simpa using hp 1 (by norm_num) (by norm_num)⟩
    exact hno ⟨r, hr, ⟨C⟩⟩
  · intro hnone
    by_contra hno
    have hnoend : ¬ ∃ p : Polynomial ℝ,
        paperPolynomialSPR n p (paperDescendingDenominator n a) ∧
        paperPolynomialSPR n p (paperDescendingDenominator n b) := by
      rintro ⟨p, hpA, hpB⟩
      exact hno ⟨p, paperTheorem2_commonSPR_on_segment
        n a b p ha0 hb0 hpA hpB⟩
    obtain ⟨r, hr, C, hmany, _⟩ :=
      paperFirstFailure_many_positive_nodes
        n hn a b ha0 hb0 hsegment hnoend
    exact hnone ⟨r, hr, C, hmany⟩



/-- The total number of distinct finite contacts plus the number of positive
roots shared by the endpoint cross polynomials is bounded by twice the
half-degree.  This also improves the contact bound by one at odd orders. -/
theorem PaperCriticalCertificate.positiveFiniteNodes_card_add_overlap_le
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    C.positiveFiniteNodes.card +
      ((MonicQuinticCoeff.positiveRealRoots
          (paperRaisedCrossPolynomial n a
            (paperFiniteNumeratorCoeffs n
              (fun j => C.support j.succ)) (C.support 0))) ∩
        (MonicQuinticCoeff.positiveRealRoots
          (paperRaisedCrossPolynomial n b
            (paperFiniteNumeratorCoeffs n
              (fun j => C.support j.succ)) (C.support 0)))).card
        ≤ 2*(n/2) := by
  let rootsA := MonicQuinticCoeff.positiveRealRoots
    (paperRaisedCrossPolynomial n a
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ)) (C.support 0))
  let rootsB := MonicQuinticCoeff.positiveRealRoots
    (paperRaisedCrossPolynomial n b
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ)) (C.support 0))
  have hsub : C.positiveFiniteNodes ⊆ rootsA ∪ rootsB :=
    C.positiveFiniteNodes_subset_endpoint_roots
      hn ha0 hb0 hstableA hstableB
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_add_card_inter rootsA rootsB
  have hbound := C.endpoint_positiveRoots_bounds
    hn ha0 hb0 hstableA hstableB
  have hboundA : 2*rootsA.card ≤ n := hbound.1
  have hboundB : 2*rootsB.card ≤ n := hbound.2
  change C.positiveFiniteNodes.card + (rootsA ∩ rootsB).card ≤ 2*(n/2)
  omega

/-- At odd order the maximum possible number of distinct positive finite
contacts drops from `n` to `n-1`. -/
theorem PaperCriticalCertificate.positiveFiniteNodes_card_le_even_part
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    C.positiveFiniteNodes.card ≤ 2*(n/2) := by
  have h := C.positiveFiniteNodes_card_add_overlap_le
    hn ha0 hb0 hstableA hstableB
  omega

/-- If all available positive root slots are used, the two endpoint root
sets are disjoint, each has exactly half the even part of the degree, and
the certificate's positive nodes exhaust their union. -/
theorem PaperCriticalCertificate.maximal_positiveFiniteNodes_structure
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2)) :
    let rootsA := MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n
          (fun j => C.support j.succ)) (C.support 0))
    let rootsB := MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n b
        (paperFiniteNumeratorCoeffs n
          (fun j => C.support j.succ)) (C.support 0))
    rootsA.card = n/2 ∧ rootsB.card = n/2 ∧
      rootsA ∩ rootsB = ∅ ∧
      C.positiveFiniteNodes = rootsA ∪ rootsB := by
  dsimp
  let rootsA := MonicQuinticCoeff.positiveRealRoots
    (paperRaisedCrossPolynomial n a
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ)) (C.support 0))
  let rootsB := MonicQuinticCoeff.positiveRealRoots
    (paperRaisedCrossPolynomial n b
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ)) (C.support 0))
  have hsub : C.positiveFiniteNodes ⊆ rootsA ∪ rootsB :=
    C.positiveFiniteNodes_subset_endpoint_roots
      hn ha0 hb0 hstableA hstableB
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_add_card_inter rootsA rootsB
  have hbound := C.endpoint_positiveRoots_bounds
    hn ha0 hb0 hstableA hstableB
  have hboundA : 2*rootsA.card ≤ n := hbound.1
  have hboundB : 2*rootsB.card ≤ n := hbound.2
  have hA : rootsA.card = n/2 := by omega
  have hB : rootsB.card = n/2 := by omega
  have hinter : rootsA ∩ rootsB = ∅ := by
    apply Finset.card_eq_zero.mp
    omega
  have heq : C.positiveFiniteNodes = rootsA ∪ rootsB := by
    apply Finset.eq_of_subset_of_card_le hsub
    omega
  exact ⟨hA, hB, hinter, heq⟩


/-- A certificate with as many distinct positive contacts as the degree
must have a positive leading support coefficient. -/
theorem PaperCriticalCertificate.support_leading_pos_of_full_contacts
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hfull : C.positiveFiniteNodes.card = n) :
    0 < C.support 0 := by
  have hnonneg := C.support_leading_nonneg ha0
  rcases hnonneg.eq_or_lt with hzero | hpos
  · have hbound := C.positiveFiniteNodes_card_le_pred_of_leading_zero
      hn ha0 hb0 hstableA hstableB hzero.symm
    omega
  · exact hpos



/-- The first-order base case of the paper's arbitrary-order theorem follows
from the contact-count obstruction: a nonnegative linear cross polynomial
has no positive multiple root. -/
theorem paperTheorem2_first_order
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator 1
          (fun j => (1-r)*a j+r*b j))) :
    ∃ p : Polynomial ℝ,
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        paperPolynomialSPR 1 p
          (paperDescendingDenominator 1
            (fun j => (1-r)*a j+r*b j)) := by
  apply (paperTheorem2_iff_no_high_contact_certificate
    1 (by norm_num) a b ha0 hb0 hsegment).2
  rintro ⟨r, hr, C, hmany⟩
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator 1 a) := by
    simpa using hsegment 0 (by norm_num) (by norm_num)
  have hstableD : paperPolynomialHurwitz
      (paperDescendingDenominator 1
        (fun j => (1-r)*a j+r*b j)) :=
    hsegment r hr.1.le hr.2
  have hd0 : (fun j => (1-r)*a j+r*b j) 0 = 1 := by
    change (1-r)*a 0+r*b 0=1
    rw [ha0, hb0]
    ring
  have hbound := C.positiveFiniteNodes_card_le_even_part
    (by norm_num : 0 < 1) ha0 hd0 hstableA hstableD
  omega



/-- Distinct positive finite contact nodes assigned to one endpoint. -/
noncomputable def PaperCriticalCertificate.positiveFiniteNodesOn
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (side : Bool) : Finset ℝ :=
  (Finset.univ.filter (fun i : Fin C.atomCount =>
    0 < C.compactFrequency i ∧ C.compactFrequency i < 1 ∧
      C.rightEndpoint i = side)).image
        (fun i => C.compactFrequency i / (1-C.compactFrequency i))

theorem PaperCriticalCertificate.positiveFiniteNodes_eq_side_union
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) :
    C.positiveFiniteNodes =
      C.positiveFiniteNodesOn false ∪
      C.positiveFiniteNodesOn true := by
  ext t
  constructor
  · intro ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    have hf := (Finset.mem_filter.mp hi).2
    cases h : C.rightEndpoint i
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨i, ?_, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, hf.1, hf.2, h⟩
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨i, ?_, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, hf.1, hf.2, h⟩
  · intro ht
    rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
      have hf := (Finset.mem_filter.mp hi).2
      apply Finset.mem_image.mpr
      refine ⟨i, ?_, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, hf.1, hf.2.1⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
      have hf := (Finset.mem_filter.mp hi).2
      apply Finset.mem_image.mpr
      refine ⟨i, ?_, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, hf.1, hf.2.1⟩

theorem PaperCriticalCertificate.positiveFiniteNodesOn_subset_roots
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (side : Bool) :
    C.positiveFiniteNodesOn side ⊆
      MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n (if side then b else a)
          (paperFiniteNumeratorCoeffs n
            (fun j => C.support j.succ)) (C.support 0)) := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
  have hf := (Finset.mem_filter.mp hi).2
  have hroot := (C.positive_contact_root_and_deriv i hf.1 hf.2.1).1
  have hneA := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn a ha0 hstableA C.support C.support_ne
  have hneB := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn b hb0 hstableB C.support C.support_ne
  cases side with
  | false =>
      have hright : C.rightEndpoint i = false := hf.2.2
      apply Finset.mem_filter.mpr
      refine ⟨?_, div_pos hf.1 (sub_pos.mpr hf.2.1)⟩
      simpa [hright, Polynomial.mem_roots hneA] using hroot
  | true =>
      have hright : C.rightEndpoint i = true := hf.2.2
      apply Finset.mem_filter.mpr
      refine ⟨?_, div_pos hf.1 (sub_pos.mpr hf.2.1)⟩
      simpa [hright, Polynomial.mem_roots hneB] using hroot

theorem PaperCriticalCertificate.positiveFiniteNodes_side_card_bounds
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    (C.positiveFiniteNodesOn false).card ≤ n/2 ∧
    (C.positiveFiniteNodesOn true).card ≤ n/2 ∧
    C.positiveFiniteNodes.card ≤
      (C.positiveFiniteNodesOn false).card + n/2 ∧
    C.positiveFiniteNodes.card ≤
      (C.positiveFiniteNodesOn true).card + n/2 := by
  have hsubA := C.positiveFiniteNodesOn_subset_roots
    hn ha0 hb0 hstableA hstableB false
  have hsubB := C.positiveFiniteNodesOn_subset_roots
    hn ha0 hb0 hstableA hstableB true
  have hcardA := Finset.card_le_card hsubA
  have hcardB := Finset.card_le_card hsubB
  have hcardA' : (C.positiveFiniteNodesOn false).card ≤
      (MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n a
          (paperFiniteNumeratorCoeffs n
            (fun j => C.support j.succ)) (C.support 0))).card := by
    simpa using hcardA
  have hcardB' : (C.positiveFiniteNodesOn true).card ≤
      (MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n b
          (paperFiniteNumeratorCoeffs n
            (fun j => C.support j.succ)) (C.support 0))).card := by
    simpa using hcardB
  have hbounds := C.endpoint_positiveRoots_bounds
    hn ha0 hb0 hstableA hstableB
  have hA : (C.positiveFiniteNodesOn false).card ≤ n/2 := by
    omega
  have hB : (C.positiveFiniteNodesOn true).card ≤ n/2 := by
    omega
  have hsplit := C.positiveFiniteNodes_eq_side_union
  have hunion := Finset.card_union_le
    (C.positiveFiniteNodesOn false)
    (C.positiveFiniteNodesOn true)
  rw [hsplit]
  omega

/-- Distinct contact nodes assigned to the two endpoints consume at least
that many atoms of the finite certificate. -/
theorem PaperCriticalCertificate.positiveFiniteNodes_side_cards_le_atoms
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) :
    (C.positiveFiniteNodesOn false).card +
      (C.positiveFiniteNodesOn true).card ≤ C.atomCount := by
  let IA : Finset (Fin C.atomCount) :=
    Finset.univ.filter (fun i =>
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1 ∧
        C.rightEndpoint i = false)
  let IB : Finset (Fin C.atomCount) :=
    Finset.univ.filter (fun i =>
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1 ∧
        C.rightEndpoint i = true)
  have hA : (C.positiveFiniteNodesOn false).card ≤ IA.card := by
    exact Finset.card_image_le
  have hB : (C.positiveFiniteNodesOn true).card ≤ IB.card := by
    exact Finset.card_image_le
  have hdisj : Disjoint IA IB := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    have hf := (Finset.mem_filter.mp hiA).2.2.2
    have ht := (Finset.mem_filter.mp hiB).2.2.2
    simp [hf] at ht
  have hle : (IA ∪ IB).card ≤ C.atomCount := by
    simpa using Finset.card_le_card (Finset.subset_univ (IA ∪ IB))
  rw [Finset.card_union_of_disjoint hdisj] at hle
  omega

/-- The endpoint root budget gives a quantitative lower bound for each
side's share of any positive finite contact set. -/
theorem PaperCriticalCertificate.positiveFiniteNodes_side_card_lower
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    C.positiveFiniteNodes.card - n/2 ≤
      (C.positiveFiniteNodesOn false).card ∧
    C.positiveFiniteNodes.card - n/2 ≤
      (C.positiveFiniteNodesOn true).card := by
  have h := C.positiveFiniteNodes_side_card_bounds
    hn ha0 hb0 hstableA hstableB
  omega

/-- At maximal contact count, each endpoint supplies exactly half the
available positive nodes, leaving at most one atom outside those nodes
when the degree is even. -/
theorem PaperCriticalCertificate.maximal_side_node_counts
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2)) :
    (C.positiveFiniteNodesOn false).card = n/2 ∧
    (C.positiveFiniteNodesOn true).card = n/2 ∧
    2*(n/2) ≤ C.atomCount := by
  have hside := C.positiveFiniteNodes_side_card_bounds
    hn ha0 hb0 hstableA hstableB
  have hsplit := C.positiveFiniteNodes_eq_side_union
  have hunion := Finset.card_union_le
    (C.positiveFiniteNodesOn false)
    (C.positiveFiniteNodesOn true)
  have hbudget := C.positiveFiniteNodes_side_cards_le_atoms
  rw [hsplit] at hmax
  omega



/-- With a full set of `n` distinct positive finite contacts, at most one
certificate atom can occur at zero frequency, infinity, or any other
noninterior location. -/
theorem PaperCriticalCertificate.maximal_contacts_at_most_one_noninterior_atom
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b)
    (hfull : C.positiveFiniteNodes.card = n) :
    (C.positiveFiniteIndicesᶜ).card ≤ 1 := by
  have himage : C.positiveFiniteNodes.card ≤
      C.positiveFiniteIndices.card := Finset.card_image_le
  rw [hfull] at himage
  have hcomplement := Finset.card_add_card_compl
    C.positiveFiniteIndices
  simp only [Fintype.card_fin] at hcomplement
  have hbudget := C.atomCount_le
  omega

/-- If the certificate uses only `n` atoms at full contact count, every
atom is at a positive finite frequency. -/
theorem PaperCriticalCertificate.full_contacts_no_noninterior_atom_of_atomCount_eq
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b)
    (hfull : C.positiveFiniteNodes.card = n)
    (hatoms : C.atomCount = n) :
    C.positiveFiniteIndices = Finset.univ := by
  have himage : C.positiveFiniteNodes.card ≤
      C.positiveFiniteIndices.card := Finset.card_image_le
  have hsub : C.positiveFiniteIndices ⊆ Finset.univ := Finset.subset_univ _
  apply Finset.eq_of_subset_of_card_le hsub
  simp [hatoms]
  omega

/-- When the unique extra atom is outside the positive finite range, every
positive finite atom has a distinct contact frequency. -/
theorem PaperCriticalCertificate.full_contacts_injective_of_one_noninterior_atom
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b)
    (hfull : C.positiveFiniteNodes.card = n)
    (hone : (C.positiveFiniteIndicesᶜ).card = 1) :
    Set.InjOn
      (fun i : Fin C.atomCount =>
        C.compactFrequency i / (1-C.compactFrequency i))
      C.positiveFiniteIndices := by
  have himage : C.positiveFiniteNodes.card ≤
      C.positiveFiniteIndices.card := Finset.card_image_le
  have hcomplement := Finset.card_add_card_compl
    C.positiveFiniteIndices
  simp only [Fintype.card_fin] at hcomplement
  have hbudget := C.atomCount_le
  have hindices : C.positiveFiniteIndices.card = n := by
    rw [hfull] at himage
    omega
  apply Finset.card_image_iff.mp
  change C.positiveFiniteNodes.card = C.positiveFiniteIndices.card
  rw [hfull, hindices]

theorem PaperCriticalCertificate.full_contacts_atomCount_dichotomy
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b)
    (hfull : C.positiveFiniteNodes.card = n) :
    C.atomCount = n ∨ C.atomCount = n+1 := by
  have himage : C.positiveFiniteNodes.card ≤
      C.positiveFiniteIndices.card := Finset.card_image_le
  have hsub : C.positiveFiniteIndices.card ≤ C.atomCount := by
    simpa using Finset.card_le_card
      (Finset.subset_univ C.positiveFiniteIndices)
  have hbudget := C.atomCount_le
  rw [hfull] at himage
  omega

/-- A minimal full-contact certificate has one atom per positive contact. -/
theorem PaperCriticalCertificate.full_contacts_injective_of_atomCount_eq
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b)
    (hfull : C.positiveFiniteNodes.card = n)
    (hatoms : C.atomCount = n) :
    Set.InjOn
      (fun i : Fin C.atomCount =>
        C.compactFrequency i / (1-C.compactFrequency i))
      C.positiveFiniteIndices := by
  have hindices := C.full_contacts_no_noninterior_atom_of_atomCount_eq
    hfull hatoms
  apply Finset.card_image_iff.mp
  change C.positiveFiniteNodes.card = C.positiveFiniteIndices.card
  rw [hfull, hindices]
  simp [hatoms]



private theorem paperQuadratic_eval
    (a : ℕ → ℝ) (ha0 : a 0 = 1) (z : ℂ) :
    Polynomial.aeval z (paperDescendingDenominator 2 a) =
      z^2 + (a 1 : ℂ)*z + (a 2 : ℂ) := by
  simp [paperDescendingDenominator, Finset.sum_range_succ, ha0,
    Polynomial.aeval_monomial]
  ring

/-- A monic Hurwitz quadratic has positive linear coefficient. -/
private theorem paperQuadratic_linear_pos
    (a : ℕ → ℝ) (ha0 : a 0 = 1)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator 2 a)) :
    0 < a 1 := by
  by_contra hnot
  have hu : a 1 ≤ 0 := le_of_not_gt hnot
  let Δ : ℂ := (a 1 : ℂ)^2 - 4*(a 2 : ℂ)
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq Δ
    (by norm_num : 0 < 2)
  let z₁ : ℂ := (-(a 1 : ℂ)+w)/2
  let z₂ : ℂ := (-(a 1 : ℂ)-w)/2
  have hz₁ : Polynomial.aeval z₁ (paperDescendingDenominator 2 a) = 0 := by
    rw [paperQuadratic_eval a ha0]
    dsimp [z₁, Δ] at *
    linear_combination (1/4)*hw
  have hz₂ : Polynomial.aeval z₂ (paperDescendingDenominator 2 a) = 0 := by
    rw [paperQuadratic_eval a ha0]
    dsimp [z₂, Δ] at *
    linear_combination (1/4)*hw
  have hsum : z₁.re + z₂.re = -a 1 := by
    simp [z₁, z₂]
    ring
  by_cases h₁ : 0 ≤ z₁.re
  · exact (hstable z₁ h₁) hz₁
  · have h₂ : 0 ≤ z₂.re := by linarith
    exact (hstable z₂ h₂) hz₂

private noncomputable def paperQuadraticCommonNumerator (c : ℝ) : Polynomial ℝ :=
  paperDescendingDenominator 2
    (fun j => if j = 0 then 1 else if j = 1 then c else 1)

private theorem paperQuadraticCommonNumerator_re
    (c ω : ℝ) :
    (Polynomial.aeval (jw ω)
      (paperQuadraticCommonNumerator c)).re = 1 - ω^2 := by
  rw [paperQuadraticCommonNumerator,
    paperQuadratic_eval]
  · simp [jw, pow_two, Complex.add_re, Complex.mul_re]
    ring
  · simp

private theorem paperQuadraticCommonNumerator_im
    (c ω : ℝ) :
    (Polynomial.aeval (jw ω)
      (paperQuadraticCommonNumerator c)).im = c*ω := by
  rw [paperQuadraticCommonNumerator,
    paperQuadratic_eval]
  · simp [jw, pow_two, Complex.add_im, Complex.mul_im]
  · simp

private theorem paperQuadratic_denominator_re
    (a : ℕ → ℝ) (ha0 : a 0 = 1) (ω : ℝ) :
    (Polynomial.aeval (jw ω)
      (paperDescendingDenominator 2 a)).re = a 2 - ω^2 := by
  rw [paperQuadratic_eval a ha0]
  simp [jw, pow_two, Complex.add_re, Complex.mul_re]
  ring

private theorem paperQuadratic_denominator_im
    (a : ℕ → ℝ) (ha0 : a 0 = 1) (ω : ℝ) :
    (Polynomial.aeval (jw ω)
      (paperDescendingDenominator 2 a)).im = a 1 * ω := by
  rw [paperQuadratic_eval a ha0]
  simp [jw, pow_two, Complex.add_im, Complex.mul_im]

private theorem paperQuadraticCommonNumerator_spr
    (a : ℕ → ℝ) (ha0 : a 0 = 1)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator 2 a))
    (c : ℝ) (hc : a 2 + 1 < c*a 1) :
    paperPolynomialSPR 2
      (paperQuadraticCommonNumerator c)
      (paperDescendingDenominator 2 a) := by
  have hconst : 0 < a 2 :=
    paperDescendingDenominator_const_pos_of_hurwitz
      2 (by norm_num) a ha0 hstable
  have hPdeg : (paperQuadraticCommonNumerator c).natDegree = 2 := by
    unfold paperQuadraticCommonNumerator
    exact paperDescendingDenominator_natDegree_eq 2 _ (by simp)
  refine ⟨hPdeg, paperDescendingDenominator_natDegree_eq 2 a ha0,
    hstable, ?_⟩
  intro ω
  have hnorm : 0 < Complex.normSq
      (Polynomial.aeval (jw ω) (paperDescendingDenominator 2 a)) :=
    Complex.normSq_pos.mpr
      (paperPolynomialHurwitz_imag_ne_zero _ hstable ω)
  have hcoeff : 0 < c*a 1-a 2-1 := by linarith
  have hnum : 0 < (1-ω^2)*(a 2-ω^2)+(c*ω)*(a 1*ω) := by
    have hs : 0 ≤ ω^2 := sq_nonneg ω
    have hsq : 0 ≤ (ω^2)^2 := sq_nonneg _
    have hprod : 0 ≤ (c*a 1-a 2-1)*ω^2 :=
      mul_nonneg hcoeff.le hs
    nlinarith
  rw [Complex.div_re,
    paperQuadraticCommonNumerator_re,
    paperQuadraticCommonNumerator_im,
    paperQuadratic_denominator_re a ha0,
    paperQuadratic_denominator_im a ha0]
  rw [← add_div]
  exact div_pos hnum hnorm

/-- The second-order base case of the paper's robust synthesis theorem,
with an explicit common numerator `s²+c s+1`. -/
theorem paperTheorem2_second_order
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator 2
          (fun j => (1-r)*a j+r*b j))) :
    ∃ p : Polynomial ℝ,
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        paperPolynomialSPR 2 p
          (paperDescendingDenominator 2
            (fun j => (1-r)*a j+r*b j)) := by
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator 2 a) := by
    simpa using hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator 2 b) := by
    simpa using hsegment 1 (by norm_num) (by norm_num)
  have huA : 0 < a 1 := paperQuadratic_linear_pos a ha0 hstableA
  have huB : 0 < b 1 := paperQuadratic_linear_pos b hb0 hstableB
  let c : ℝ := max ((a 2+1)/(a 1)) ((b 2+1)/(b 1)) + 1
  have hcA : a 2+1 < c*a 1 := by
    have hmax : (a 2+1)/(a 1) ≤
        max ((a 2+1)/(a 1)) ((b 2+1)/(b 1)) := le_max_left _ _
    have hle := (div_le_iff₀ huA).mp hmax
    dsimp [c]
    nlinarith
  have hcB : b 2+1 < c*b 1 := by
    have hmax : (b 2+1)/(b 1) ≤
        max ((a 2+1)/(a 1)) ((b 2+1)/(b 1)) := le_max_right _ _
    have hle := (div_le_iff₀ huB).mp hmax
    dsimp [c]
    nlinarith
  have hpA := paperQuadraticCommonNumerator_spr
    a ha0 hstableA c hcA
  have hpB := paperQuadraticCommonNumerator_spr
    b hb0 hstableB c hcB
  exact ⟨paperQuadraticCommonNumerator c,
    paperTheorem2_commonSPR_on_segment
      2 a b _ ha0 hb0 hpA hpB⟩



/-- The paper's full first-order equivalence. -/
theorem paperTheorem2_first_order_iff
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    (∃ p : Polynomial ℝ,
      paperPolynomialSPR 1 p (paperDescendingDenominator 1 a) ∧
      paperPolynomialSPR 1 p (paperDescendingDenominator 1 b)) ↔
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator 1
          (fun j => (1-r)*a j+r*b j))) := by
  constructor
  · rintro ⟨p, hpA, hpB⟩
    exact paperTheorem2_necessity 1 a b p ha0 hb0 hpA hpB
  · intro hsegment
    obtain ⟨p, hp⟩ := paperTheorem2_first_order
      a b ha0 hb0 hsegment
    refine ⟨p, ?_, ?_⟩
    · simpa using hp 0 (by norm_num) (by norm_num)
    · simpa using hp 1 (by norm_num) (by norm_num)

/-- The paper's full second-order equivalence, with its explicit
construction supplying the sufficiency direction. -/
theorem paperTheorem2_second_order_iff
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    (∃ p : Polynomial ℝ,
      paperPolynomialSPR 2 p (paperDescendingDenominator 2 a) ∧
      paperPolynomialSPR 2 p (paperDescendingDenominator 2 b)) ↔
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator 2
          (fun j => (1-r)*a j+r*b j))) := by
  constructor
  · rintro ⟨p, hpA, hpB⟩
    exact paperTheorem2_necessity 2 a b p ha0 hb0 hpA hpB
  · intro hsegment
    obtain ⟨p, hp⟩ := paperTheorem2_second_order
      a b ha0 hb0 hsegment
    refine ⟨p, ?_, ?_⟩
    · simpa using hp 0 (by norm_num) (by norm_num)
    · simpa using hp 1 (by norm_num) (by norm_num)



/-- The sixth-order instance of the paper's general endpoint theorem:
a common SPR numerator for the two endpoint denominators exists exactly
when the entire coefficient segment is Hurwitz stable. -/
theorem paperTheorem2_sixth_order_iff
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    (∃ p : Polynomial ℝ,
      paperPolynomialSPR 6 p (paperDescendingDenominator 6 a) ∧
      paperPolynomialSPR 6 p (paperDescendingDenominator 6 b)) ↔
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator 6
          (fun j => (1-r)*a j+r*b j))) := by
  constructor
  · rintro ⟨p, hpA, hpB⟩
    exact paperTheorem2_necessity 6 a b p ha0 hb0 hpA hpB
  · intro hsegment
    obtain ⟨p, hp⟩ :=
      (sixth_order_paper_coefficient_sequence a b ha0 hb0).mp hsegment
    refine ⟨p, ?_, ?_⟩
    · simpa using hp 0 (by norm_num) (by norm_num)
    · simpa using hp 1 (by norm_num) (by norm_num)



/-- If a raised numerator vanishes at an imaginary frequency, then the
corresponding real cross polynomial vanishes at the squared frequency. -/
theorem paperRaisedCross_eval_zero_of_numerator_imag_zero
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) (ε ω : ℝ)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hzero : Polynomial.aeval (jw ω)
      (paperDescendingNumerator n x +
        Polynomial.C ε * Polynomial.X^n) = (0 : ℂ)) :
    (paperRaisedCrossPolynomial n a x ε).eval (ω^2) = 0 := by
  have hnorm : 0 < Complex.normSq
      (Polynomial.aeval (jw ω)
        (paperDescendingDenominator n a) : ℂ) :=
    Complex.normSq_pos.mpr
      (paperPolynomialHurwitz_imag_ne_zero _ hstable ω)
  have hquot :
      ((paperGeneralCrossPolynomial n a x).eval (ω^2) +
        ε * (paperRaiseCorrection n a).eval (ω^2)) /
          Complex.normSq
            (Polynomial.aeval (jw ω)
              (paperDescendingDenominator n a) : ℂ) = 0 := by
    rw [← paperDescending_degree_raised_re n hn a x ε ω]
    simp [hzero]
  have hcross : (paperGeneralCrossPolynomial n a x).eval (ω^2) +
      ε * (paperRaiseCorrection n a).eval (ω^2) = 0 :=
    (div_eq_zero_iff.mp hquot).resolve_right (ne_of_gt hnorm)
  simpa [paperRaisedCrossPolynomial, Polynomial.eval_add,
    Polynomial.eval_C_mul] using hcross

/-- At maximal positive contact count, the supporting numerator has no
zero at a positive imaginary frequency. -/
theorem PaperCriticalCertificate.support_numerator_imag_ne_zero_of_maximal_contacts
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (ω : ℝ) (hω : ω ≠ 0) :
    Polynomial.aeval (jw ω)
      (paperDescendingNumerator n
        (paperFiniteNumeratorCoeffs n
          (fun j => C.support j.succ)) +
       Polynomial.C (C.support 0) * Polynomial.X^n) ≠ (0 : ℂ) := by
  intro hz
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let qA := paperRaisedCrossPolynomial n a x ε
  let qB := paperRaisedCrossPolynomial n b x ε
  have hneA : qA ≠ 0 :=
    paperRaisedCrossPolynomial_ne_zero_of_hurwitz
      n hn a ha0 hstableA C.support C.support_ne
  have hneB : qB ≠ 0 :=
    paperRaisedCrossPolynomial_ne_zero_of_hurwitz
      n hn b hb0 hstableB C.support C.support_ne
  have hzeroA : qA.eval (ω^2) = 0 :=
    paperRaisedCross_eval_zero_of_numerator_imag_zero
      n hn a x ε ω hstableA (by simpa [x, ε] using hz)
  have hzeroB : qB.eval (ω^2) = 0 :=
    paperRaisedCross_eval_zero_of_numerator_imag_zero
      n hn b x ε ω hstableB (by simpa [x, ε] using hz)
  have htpos : 0 < ω^2 := sq_pos_of_ne_zero hω
  have hmemA : ω^2 ∈ MonicQuinticCoeff.positiveRealRoots qA := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, htpos⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hneA]
    exact hzeroA
  have hmemB : ω^2 ∈ MonicQuinticCoeff.positiveRealRoots qB := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, htpos⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hneB]
    exact hzeroB
  have hstructure := C.maximal_positiveFiniteNodes_structure
    hn ha0 hb0 hstableA hstableB hmax
  have hdisj : MonicQuinticCoeff.positiveRealRoots qA ∩
      MonicQuinticCoeff.positiveRealRoots qB = ∅ := by
    simpa [qA, qB, x, ε] using hstructure.2.2.1
  have hmem : ω^2 ∈ MonicQuinticCoeff.positiveRealRoots qA ∩
      MonicQuinticCoeff.positiveRealRoots qB :=
    Finset.mem_inter.mpr ⟨hmemA, hmemB⟩
  rw [hdisj] at hmem
  simp at hmem



/-- In the maximal-contact case at even order, the supporting numerator
cannot vanish at any imaginary-axis frequency, including zero. -/
theorem PaperCriticalCertificate.support_numerator_imag_ne_zero_of_maximal_even_contacts
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (heven : n = 2*(n/2)) :
    ∀ ω : ℝ,
      Polynomial.aeval (jw ω)
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n
            (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n) ≠ (0 : ℂ) := by
  intro ω
  by_cases hω : ω = 0
  · subst ω
    intro hz
    let x := paperFiniteNumeratorCoeffs n
      (fun j => C.support j.succ)
    let ε := C.support 0
    let qA := paperRaisedCrossPolynomial n a x ε
    have hneA : qA ≠ 0 :=
      paperRaisedCrossPolynomial_ne_zero_of_hurwitz
        n hn a ha0 hstableA C.support C.support_ne
    have hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ qA.eval t :=
      paperFeature_nonneg_cross_nonneg
        n a C.support C.support_nonneg_left
    have hzero : qA.eval 0 = 0 := by
      simpa [qA] using
        (paperRaisedCross_eval_zero_of_numerator_imag_zero
          n hn a x ε 0 hstableA (by simpa [x, ε] using hz))
    have hcount :=
      MonicQuinticCoeff.twice_card_positiveRealRoots_add_one_le_natDegree_of_zero_root
        qA hneA hnonneg hzero
    have hdegree : qA.natDegree ≤ n :=
      paperRaisedCrossPolynomial_natDegree_le n a x ε
    have hstructure := C.maximal_positiveFiniteNodes_structure
      hn ha0 hb0 hstableA hstableB hmax
    have hrootcard :
        (MonicQuinticCoeff.positiveRealRoots qA).card = n/2 := by
      simpa [qA, x, ε] using hstructure.1
    omega
  · exact C.support_numerator_imag_ne_zero_of_maximal_contacts
      hn ha0 hb0 hstableA hstableB hmax ω hω



theorem paperRaisedCrossPolynomial_eval_zero
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) (ε : ℝ) :
    (paperRaisedCrossPolynomial n a x ε).eval 0 =
      a n * x (n-1) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero,
    paperRaisedCrossPolynomial, Polynomial.coeff_add,
    paperGeneralCrossPolynomial_coeff, if_pos hn,
    Nat.sub_zero, paperGeneralCoefficient_last n hn,
    Polynomial.coeff_C_mul,
    paperRaiseCorrection_coeff_zero n hn]
  ring

theorem paperRaisedNumerator_eval_zero
    (n : ℕ) (hn : 0 < n) (x : ℕ → ℝ) (ε : ℝ) :
    (paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n).eval 0 = x (n-1) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_add, paperDescendingNumerator_coeff,
    if_pos hn, Nat.sub_zero,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  simp [show 0 ≠ n by omega]

/-- At full even-order contact count the support numerator has strictly
positive value at zero. -/
theorem PaperCriticalCertificate.support_numerator_eval_zero_pos_of_maximal_even_contacts
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (heven : n = 2*(n/2)) :
    0 < (paperDescendingNumerator n
        (paperFiniteNumeratorCoeffs n
          (fun j => C.support j.succ)) +
       Polynomial.C (C.support 0) * Polynomial.X^n).eval 0 := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let qA := paperRaisedCrossPolynomial n a x ε
  have hneA : qA ≠ 0 :=
    paperRaisedCrossPolynomial_ne_zero_of_hurwitz
      n hn a ha0 hstableA C.support C.support_ne
  have hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ qA.eval t :=
    paperFeature_nonneg_cross_nonneg
      n a C.support C.support_nonneg_left
  have hstructure := C.maximal_positiveFiniteNodes_structure
    hn ha0 hb0 hstableA hstableB hmax
  have hrootcard :
      (MonicQuinticCoeff.positiveRealRoots qA).card = n/2 := by
    simpa [qA, x, ε] using hstructure.1
  have hzeroNe : qA.eval 0 ≠ 0 := by
    intro hz
    have hcount :=
      MonicQuinticCoeff.twice_card_positiveRealRoots_add_one_le_natDegree_of_zero_root
        qA hneA hnonneg hz
    have hdegree : qA.natDegree ≤ n :=
      paperRaisedCrossPolynomial_natDegree_le n a x ε
    omega
  have hqPos : 0 < qA.eval 0 := lt_of_le_of_ne (hnonneg 0 le_rfl)
    (Ne.symm hzeroNe)
  have hconst : 0 < a n :=
    paperDescendingDenominator_const_pos_of_hurwitz
      n hn a ha0 hstableA
  have hxPos : 0 < x (n-1) := by
    have heq := paperRaisedCrossPolynomial_eval_zero n hn a x ε
    change qA.eval 0 = a n * x (n-1) at heq
    rw [heq] at hqPos
    exact (mul_pos_iff_of_pos_left hconst).mp hqPos
  simpa [x, ε, paperRaisedNumerator_eval_zero n hn] using hxPos



/-- The support vector of a critical certificate is a common weak
positive-real numerator on the imaginary axis.  This is the analytic form
of its two nonnegative feature-pairing conditions. -/
theorem PaperCriticalCertificate.support_numerator_weak_re_nonneg
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    ∀ ω : ℝ,
      0 ≤ ((Polynomial.aeval (jw ω)
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n
            (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n) : ℂ) /
          Polynomial.aeval (jw ω)
            (paperDescendingDenominator n a)).re ∧
      0 ≤ ((Polynomial.aeval (jw ω)
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n
            (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n) : ℂ) /
          Polynomial.aeval (jw ω)
            (paperDescendingDenominator n b)).re := by
  intro ω
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  have hqA := paperFeature_nonneg_cross_nonneg
    n a C.support C.support_nonneg_left (ω^2) (sq_nonneg ω)
  have hqB := paperFeature_nonneg_cross_nonneg
    n b C.support C.support_nonneg_right (ω^2) (sq_nonneg ω)
  have hnormA : 0 < Complex.normSq
      (Polynomial.aeval (jw ω)
        (paperDescendingDenominator n a) : ℂ) :=
    Complex.normSq_pos.mpr
      (paperPolynomialHurwitz_imag_ne_zero _ hstableA ω)
  have hnormB : 0 < Complex.normSq
      (Polynomial.aeval (jw ω)
        (paperDescendingDenominator n b) : ℂ) :=
    Complex.normSq_pos.mpr
      (paperPolynomialHurwitz_imag_ne_zero _ hstableB ω)
  constructor
  · rw [paperDescending_degree_raised_re n hn a x ε ω]
    have hcross : 0 ≤
        (paperGeneralCrossPolynomial n a x).eval (ω^2) +
          ε * (paperRaiseCorrection n a).eval (ω^2) := by
      simpa [x, ε, paperRaisedCrossPolynomial,
        Polynomial.eval_add, Polynomial.eval_C_mul] using hqA
    exact div_nonneg hcross hnormA.le
  · rw [paperDescending_degree_raised_re n hn b x ε ω]
    have hcross : 0 ≤
        (paperGeneralCrossPolynomial n b x).eval (ω^2) +
          ε * (paperRaiseCorrection n b).eval (ω^2) := by
      simpa [x, ε, paperRaisedCrossPolynomial,
        Polynomial.eval_add, Polynomial.eval_C_mul] using hqB
    exact div_nonneg hcross hnormB.le



/-- Equality in the positive-root bound determines the complete root
multiset: every root is positive and occurs exactly twice. -/
theorem MonicQuinticCoeff.saturated_positive_roots_structure
    (P : Polynomial ℝ) (hP : P ≠ 0)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ P.eval t)
    (hsaturated : 2 * (MonicQuinticCoeff.positiveRealRoots P).card =
      P.natDegree) :
    (∀ r ∈ MonicQuinticCoeff.positiveRealRoots P,
      P.roots.count r = 2) ∧
    P.roots.card = P.natDegree ∧
    P.roots.toFinset = MonicQuinticCoeff.positiveRealRoots P := by
  let S := MonicQuinticCoeff.positiveRealRoots P
  have hsat : 2*S.card = P.natDegree := by
    simpa [S] using hsaturated
  have hcount : ∀ r ∈ S, 2 ≤ P.roots.count r := by
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    rw [Polynomial.count_roots]
    exact MonicQuinticCoeff.rootMultiplicity_two_le_of_nonneg_of_pos_root
      P hP hnonneg hr'.2
        ((Polynomial.mem_roots hP).mp
          (Multiset.mem_toFinset.mp hr'.1))
  have hsub : S ⊆ P.roots.toFinset := Finset.filter_subset _ _
  have hsumLower : 2*S.card ≤ ∑ r ∈ S, P.roots.count r := by
    calc
      2*S.card = ∑ r ∈ S, (2 : ℕ) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hcount
  have hsumUpper : (∑ r ∈ S, P.roots.count r) ≤ P.roots.card := by
    calc
      _ ≤ ∑ r ∈ P.roots.toFinset, P.roots.count r :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => Nat.zero_le _)
      _ = P.roots.card := Multiset.toFinset_sum_count_eq P.roots
  have hrootsLe := Polynomial.card_roots' P
  have hsumEq : (∑ r ∈ S, P.roots.count r) = 2*S.card := by
    omega
  have hrootcard : P.roots.card = P.natDegree := by omega
  have hcountExact : ∀ r ∈ S, P.roots.count r = 2 := by
    have heq : (∑ r ∈ S, (2 : ℕ)) =
        ∑ r ∈ S, P.roots.count r := by
      calc
        _ = 2*S.card := by simp [mul_comm]
        _ = _ := hsumEq.symm
    intro r hr
    exact ((Finset.sum_eq_sum_iff_of_le hcount).mp heq r hr).symm
  have hreverse : P.roots.toFinset ⊆ S := by
    intro r hr
    by_cases hmem : r ∈ S
    · exact hmem
    · exfalso
      have hlt : (∑ r ∈ S, P.roots.count r) <
          ∑ r ∈ P.roots.toFinset, P.roots.count r :=
        Finset.sum_lt_sum_of_subset hsub hr hmem
          (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hr))
          (fun _ _ _ => Nat.zero_le _)
      rw [Multiset.toFinset_sum_count_eq] at hlt
      omega
  exact ⟨hcountExact, hrootcard,
    Finset.Subset.antisymm hreverse hsub⟩

/-- A nonnegative real polynomial that saturates the positive-root bound
is a positive scalar times a square of a monic polynomial with positive
roots. -/
theorem MonicQuinticCoeff.saturated_positive_roots_square
    (P : Polynomial ℝ) (hP : P ≠ 0)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ P.eval t)
    (hsaturated : 2 * (MonicQuinticCoeff.positiveRealRoots P).card =
      P.natDegree) :
    ∃ Q : Polynomial ℝ,
      Q.Monic ∧
      Q.natDegree = (MonicQuinticCoeff.positiveRealRoots P).card ∧
      P = Polynomial.C P.leadingCoeff * Q^2 := by
  let S := MonicQuinticCoeff.positiveRealRoots P
  let Q : Polynomial ℝ :=
    (S.val.map (fun r : ℝ => Polynomial.X - Polynomial.C r)).prod
  obtain ⟨hcount, hrootcard, hrootset⟩ :=
    MonicQuinticCoeff.saturated_positive_roots_structure
      P hP hnonneg hsaturated
  have hroots : P.roots = S.val + S.val := by
    apply Multiset.ext.mpr
    intro r
    by_cases hr : r ∈ S
    · have hcountR : P.roots.count r = 2 := hcount r hr
      have hval : S.val.count r = 1 :=
        Multiset.count_eq_one_of_mem S.nodup (by simpa using hr)
      rw [hcountR, Multiset.count_add, hval]
    · have hnot : r ∉ P.roots := by
        intro hmem
        have hmem' : r ∈ P.roots.toFinset :=
          Multiset.mem_toFinset.mpr hmem
        rw [hrootset] at hmem'
        exact hr hmem'
      have hcountR : P.roots.count r = 0 :=
        Multiset.count_eq_zero.mpr hnot
      have hval : S.val.count r = 0 :=
        Multiset.count_eq_zero.mpr (by simpa using hr)
      rw [hcountR, Multiset.count_add, hval]
  have hQmonic : Q.Monic := by
    exact Polynomial.monic_multiset_prod_of_monic
      S.val _ (fun r _ => Polynomial.monic_X_sub_C r)
  have hQdegree : Q.natDegree = S.card := by
    simpa [Q] using
      Polynomial.natDegree_multiset_prod_X_sub_C_eq_card S.val
  have hfactor := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    hrootcard
  rw [hroots, Multiset.map_add, Multiset.prod_add] at hfactor
  have hPfactor : P = Polynomial.C P.leadingCoeff * Q^2 := by
    simpa [Q, pow_two] using hfactor.symm
  exact ⟨Q, hQmonic, hQdegree, hPfactor⟩



/-- At maximal contact count in even order, both endpoint cross
polynomials are the same positive scalar times squares of monic
half-degree polynomials.  Their positive root sets are disjoint. -/
theorem PaperCriticalCertificate.maximal_even_endpoint_square_structure
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (heven : n = 2*(n/2)) :
    let x := paperFiniteNumeratorCoeffs n
      (fun j => C.support j.succ)
    let ε := C.support 0
    let qA := paperRaisedCrossPolynomial n a x ε
    let qB := paperRaisedCrossPolynomial n b x ε
    ∃ UA UB : Polynomial ℝ,
      0 < ε ∧ UA.Monic ∧ UB.Monic ∧
      UA.natDegree = n/2 ∧ UB.natDegree = n/2 ∧
      qA = Polynomial.C ε * UA^2 ∧
      qB = Polynomial.C ε * UB^2 ∧
      MonicQuinticCoeff.positiveRealRoots qA ∩
        MonicQuinticCoeff.positiveRealRoots qB = ∅ := by
  dsimp
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let qA := paperRaisedCrossPolynomial n a x ε
  let qB := paperRaisedCrossPolynomial n b x ε
  have hfull : C.positiveFiniteNodes.card = n := by
    exact hmax.trans heven.symm
  have hε : 0 < ε :=
    C.support_leading_pos_of_full_contacts
      hn ha0 hb0 hstableA hstableB hfull
  have hneA : qA ≠ 0 :=
    paperRaisedCrossPolynomial_ne_zero_of_hurwitz
      n hn a ha0 hstableA C.support C.support_ne
  have hneB : qB ≠ 0 :=
    paperRaisedCrossPolynomial_ne_zero_of_hurwitz
      n hn b hb0 hstableB C.support C.support_ne
  have hnonnegA : ∀ t : ℝ, 0 ≤ t → 0 ≤ qA.eval t :=
    paperFeature_nonneg_cross_nonneg
      n a C.support C.support_nonneg_left
  have hnonnegB : ∀ t : ℝ, 0 ≤ t → 0 ≤ qB.eval t :=
    paperFeature_nonneg_cross_nonneg
      n b C.support C.support_nonneg_right
  have hdegreeA : qA.natDegree = n :=
    paperRaisedCrossPolynomial_natDegree_eq
      n a x ε ha0 (ne_of_gt hε)
  have hdegreeB : qB.natDegree = n :=
    paperRaisedCrossPolynomial_natDegree_eq
      n b x ε hb0 (ne_of_gt hε)
  have hstructure := C.maximal_positiveFiniteNodes_structure
    hn ha0 hb0 hstableA hstableB hmax
  have hrootsA :
      (MonicQuinticCoeff.positiveRealRoots qA).card = n/2 := by
    simpa [qA, x, ε] using hstructure.1
  have hrootsB :
      (MonicQuinticCoeff.positiveRealRoots qB).card = n/2 := by
    simpa [qB, x, ε] using hstructure.2.1
  have hsatA :
      2*(MonicQuinticCoeff.positiveRealRoots qA).card =
        qA.natDegree := by omega
  have hsatB :
      2*(MonicQuinticCoeff.positiveRealRoots qB).card =
        qB.natDegree := by omega
  obtain ⟨UA, hUmonic, hUdegree, hUA⟩ :=
    MonicQuinticCoeff.saturated_positive_roots_square
      qA hneA hnonnegA hsatA
  obtain ⟨UB, hVmonic, hVdegree, hUB⟩ :=
    MonicQuinticCoeff.saturated_positive_roots_square
      qB hneB hnonnegB hsatB
  have hleadA : qA.leadingCoeff = ε :=
    paperRaisedCrossPolynomial_leadingCoeff
      n a x ε ha0 (ne_of_gt hε)
  have hleadB : qB.leadingCoeff = ε :=
    paperRaisedCrossPolynomial_leadingCoeff
      n b x ε hb0 (ne_of_gt hε)
  rw [hleadA] at hUA
  rw [hleadB] at hUB
  have hdisj : MonicQuinticCoeff.positiveRealRoots qA ∩
      MonicQuinticCoeff.positiveRealRoots qB = ∅ := by
    simpa [qA, qB, x, ε] using hstructure.2.2.1
  exact ⟨UA, UB, hε, hUmonic, hVmonic,
    by simpa [hrootsA] using hUdegree,
    by simpa [hrootsB] using hVdegree,
    hUA, hUB, hdisj⟩



/-- Two nonnegative half-line polynomials with positive values at zero and
disjoint positive-root sets have a strictly positive convex combination
at every nonnegative argument. -/
theorem paperStrictConvexOfDisjointPositiveRoots
    (P Q : Polynomial ℝ) (hPne : P ≠ 0) (hQne : Q ≠ 0)
    (hPnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ P.eval t)
    (hQnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ Q.eval t)
    (hPzero : 0 < P.eval 0)
    (hdisj : MonicQuinticCoeff.positiveRealRoots P ∩
      MonicQuinticCoeff.positiveRealRoots Q = ∅)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    0 < (1-r)*P.eval t+r*Q.eval t := by
  by_contra hnot
  have hleft : 0 ≤ (1-r)*P.eval t :=
    mul_nonneg (by linarith) (hPnonneg t ht)
  have hright : 0 ≤ r*Q.eval t :=
    mul_nonneg hr0.le (hQnonneg t ht)
  have hsum : (1-r)*P.eval t+r*Q.eval t = 0 := by
    exact le_antisymm (le_of_not_gt hnot) (add_nonneg hleft hright)
  have hzeros := (add_eq_zero_iff_of_nonneg hleft hright).mp hsum
  have hp : P.eval t = 0 :=
    (mul_eq_zero.mp hzeros.1).resolve_left (ne_of_gt (by linarith : 0 < 1-r))
  have hq : Q.eval t = 0 :=
    (mul_eq_zero.mp hzeros.2).resolve_left (ne_of_gt hr0)
  have htpos : 0 < t := by
    rcases ht.eq_or_lt with hzero | hpos
    · subst t
      exact False.elim ((ne_of_gt hPzero) hp)
    · exact hpos
  have hmemP : t ∈ MonicQuinticCoeff.positiveRealRoots P := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, htpos⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne]
    exact hp
  have hmemQ : t ∈ MonicQuinticCoeff.positiveRealRoots Q := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, htpos⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQne]
    exact hq
  have hmem : t ∈ MonicQuinticCoeff.positiveRealRoots P ∩
      MonicQuinticCoeff.positiveRealRoots Q :=
    Finset.mem_inter.mpr ⟨hmemP, hmemQ⟩
  rw [hdisj] at hmem
  simp at hmem



/-- A maximal even-order critical support is strictly positive real against
every denominator strictly inside the stable endpoint segment.  Its
possible zero contacts occur only at the two endpoint denominators. -/
theorem PaperCriticalCertificate.maximal_even_support_SPR_interior
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun j => (1-r)*a j+r*b j)))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (heven : n = 2*(n/2)) :
    ∀ r : ℝ, 0 < r → r < 1 →
      paperPolynomialSPR n
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n
            (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n)
        (paperDescendingDenominator n
          (fun j => (1-r)*a j+r*b j)) := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let qA := paperRaisedCrossPolynomial n a x ε
  let qB := paperRaisedCrossPolynomial n b x ε
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa using hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa using hsegment 1 (by norm_num) (by norm_num)
  have hfull : C.positiveFiniteNodes.card = n := hmax.trans heven.symm
  have hε : 0 < ε := C.support_leading_pos_of_full_contacts
    hn ha0 hb0 hstableA hstableB hfull
  have hneA : qA ≠ 0 :=
    paperRaisedCrossPolynomial_ne_zero_of_hurwitz
      n hn a ha0 hstableA C.support C.support_ne
  have hneB : qB ≠ 0 :=
    paperRaisedCrossPolynomial_ne_zero_of_hurwitz
      n hn b hb0 hstableB C.support C.support_ne
  have hnonnegA : ∀ t : ℝ, 0 ≤ t → 0 ≤ qA.eval t :=
    paperFeature_nonneg_cross_nonneg
      n a C.support C.support_nonneg_left
  have hnonnegB : ∀ t : ℝ, 0 ≤ t → 0 ≤ qB.eval t :=
    paperFeature_nonneg_cross_nonneg
      n b C.support C.support_nonneg_right
  have hstructure := C.maximal_positiveFiniteNodes_structure
    hn ha0 hb0 hstableA hstableB hmax
  have hdisj : MonicQuinticCoeff.positiveRealRoots qA ∩
      MonicQuinticCoeff.positiveRealRoots qB = ∅ := by
    simpa [qA, qB, x, ε] using hstructure.2.2.1
  have hPzero := C.support_numerator_eval_zero_pos_of_maximal_even_contacts
    hn ha0 hb0 hstableA hstableB hmax heven
  have hxzero : 0 < x (n-1) := by
    simpa [x, ε, paperRaisedNumerator_eval_zero n hn] using hPzero
  have hconstA : 0 < a n :=
    paperDescendingDenominator_const_pos_of_hurwitz
      n hn a ha0 hstableA
  have hqAzero : 0 < qA.eval 0 := by
    rw [paperRaisedCrossPolynomial_eval_zero n hn a x ε]
    exact mul_pos hconstA hxzero
  intro r hr0 hr1
  let d : ℕ → ℝ := fun j => (1-r)*a j+r*b j
  have hd0 : d 0 = 1 := by
    change (1-r)*a 0+r*b 0=1
    rw [ha0, hb0]
    ring
  have hstableD : paperPolynomialHurwitz
      (paperDescendingDenominator n d) :=
    hsegment r hr0.le hr1.le
  apply (paperSPR_iff_cross_positive n hn d x ε hε hd0 hstableD).mpr
  intro t ht
  have hpos := paperStrictConvexOfDisjointPositiveRoots
    qA qB hneA hneB hnonnegA hnonnegB hqAzero
      hdisj r hr0 hr1 t ht
  have hq : 0 < (paperRaisedCrossPolynomial n d x ε).eval t := by
    rw [paperRaisedCrossPolynomial_affine_denominator]
    simpa [qA, qB, d, Polynomial.eval_add,
      Polynomial.eval_C_mul] using hpos
  simpa [paperRaisedCrossPolynomial,
    Polynomial.eval_add, Polynomial.eval_C_mul] using hq



theorem paperRaisedNumerator_eq_scaled_denominator
    (n : ℕ) (x : ℕ → ℝ) (ε : ℝ) (hε : ε ≠ 0) :
    paperDescendingNumerator n x + Polynomial.C ε * Polynomial.X^n =
      Polynomial.C ε *
        paperDescendingDenominator n
          (fun i => if i = 0 then 1 else x (i-1) / ε) := by
  ext m
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, paperDescendingNumerator_coeff,
    Polynomial.coeff_C_mul, paperDescendingDenominator_coeff]
  by_cases hmn : m < n
  · rw [if_pos hmn, if_neg (by omega : m ≠ n),
      if_pos (by omega : m ≤ n),
      if_neg (by omega : n - m ≠ 0)]
    have hid : n-m-1 = n-1-m := by omega
    rw [hid]
    field_simp
  · by_cases hmeq : m = n
    · subst m
      simp
    · rw [if_neg hmn, if_neg hmeq,
        if_neg (by omega : ¬ m ≤ n)]
      simp

theorem complex_convex_ne_zero_of_re_div_nonneg
    (A B : ℂ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hRe : 0 ≤ (B/A).re)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ((1-r : ℝ) : ℂ)*A+(r : ℂ)*B ≠ 0 := by
  intro hz
  by_cases hre : r = 1
  · subst r
    apply hB
    simpa using hz
  have hrlt : r < 1 := lt_of_le_of_ne hr1 hre
  have hzero : (((1-r : ℝ) : ℂ) + (r : ℂ)*(B/A)) = 0 := by
    calc
      _ = (((1-r : ℝ) : ℂ)*A+(r : ℂ)*B)/A := by
        field_simp
      _ = 0 := by rw [hz]; simp
  have hreal : 1-r+r*(B/A).re = 0 := by
    have h := congrArg Complex.re hzero
    simpa using h
  have hpos : 0 < 1-r+r*(B/A).re := by
    have hm : 0 ≤ r*(B/A).re := mul_nonneg hr0 hRe
    linarith
  linarith

theorem paperRaisedNumerator_hurwitz_of_weak_re
    (n : ℕ) (a x : ℕ → ℝ) (ε : ℝ)
    (ha0 : a 0 = 1) (hε : 0 < ε)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hweak : ∀ ω : ℝ,
      0 ≤ ((Polynomial.aeval (jw ω)
        (paperDescendingNumerator n x +
          Polynomial.C ε * Polynomial.X^n) : ℂ) /
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n a)).re)
    (himag : ∀ ω : ℝ,
      Polynomial.aeval (jw ω)
        (paperDescendingNumerator n x +
          Polynomial.C ε * Polynomial.X^n) ≠ (0 : ℂ)) :
    paperPolynomialHurwitz
      (paperDescendingNumerator n x +
        Polynomial.C ε * Polynomial.X^n) := by
  let c : ℕ → ℝ := fun i => if i = 0 then 1 else x (i-1) / ε
  let P : Polynomial ℝ :=
    paperDescendingNumerator n x + Polynomial.C ε * Polynomial.X^n
  let A : Polynomial ℝ := paperDescendingDenominator n a
  let B : Polynomial ℝ := paperDescendingDenominator n c
  have hc0 : c 0 = 1 := by simp [c]
  have hP : P = Polynomial.C ε * B := by
    simpa [P, B, c] using
      paperRaisedNumerator_eq_scaled_denominator
        n x ε (ne_of_gt hε)
  have hBimag : ∀ ω : ℝ, Polynomial.aeval (jw ω) B ≠ (0 : ℂ) := by
    intro ω hzero
    apply himag ω
    change Polynomial.aeval (jw ω) P = 0
    rw [hP, Polynomial.aeval_mul,
      Polynomial.aeval_C, hzero]
    simp
  have hratio : ∀ ω : ℝ,
      0 ≤ ((Polynomial.aeval (jw ω) B : ℂ) /
        Polynomial.aeval (jw ω) A).re := by
    intro ω
    have hweak' := hweak ω
    change 0 ≤ ((Polynomial.aeval (jw ω) P : ℂ) /
      Polynomial.aeval (jw ω) A).re at hweak'
    rw [hP, Polynomial.aeval_mul, Polynomial.aeval_C] at hweak'
    have hmul : 0 ≤ ε *
        ((Polynomial.aeval (jw ω) B : ℂ) /
          Polynomial.aeval (jw ω) A).re := by
      simpa [mul_div_assoc, Complex.mul_re] using hweak'
    exact (mul_nonneg_iff_of_pos_left hε).mp hmul
  have hno : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ ω : ℝ,
      Polynomial.aeval (jw ω)
        (paperSegmentDenominator n a c r) ≠ (0 : ℂ) := by
    intro r hr0 hr1 ω
    have hA := paperPolynomialHurwitz_imag_ne_zero A hstable ω
    have hB := hBimag ω
    have hlin := complex_convex_ne_zero_of_re_div_nonneg
      (Polynomial.aeval (jw ω) A)
      (Polynomial.aeval (jw ω) B)
      hA hB (hratio ω) r hr0 hr1
    simpa [paperSegmentDenominator_eval_affine n a c r (jw ω)]
      using hlin
  have hBstable : paperPolynomialHurwitz B := by
    have h := paperMonicSegment_zero_exclusion
      n a c ha0 hc0 hstable hno 1 (by norm_num) (by norm_num)
    simpa [paperSegmentDenominator, B] using h
  intro z hzre
  have hnonzero := hBstable z hzre
  change Polynomial.aeval z P ≠ 0
  rw [hP, Polynomial.aeval_mul, Polynomial.aeval_C]
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hε)
  exact mul_ne_zero (by simpa using hεc) hnonzero

/-- At maximal even contact, the critical supporting numerator is itself
Hurwitz stable, despite only weak positive-real behavior at the endpoints. -/
theorem PaperCriticalCertificate.support_numerator_hurwitz_of_maximal_even_contacts
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (heven : n = 2*(n/2)) :
    paperPolynomialHurwitz
      (paperDescendingNumerator n
        (paperFiniteNumeratorCoeffs n
          (fun j => C.support j.succ)) +
       Polynomial.C (C.support 0) * Polynomial.X^n) := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  have hfull : C.positiveFiniteNodes.card = n :=
    hmax.trans heven.symm
  have hε : 0 < ε :=
    C.support_leading_pos_of_full_contacts
      hn ha0 hb0 hstableA hstableB hfull
  have hweak := C.support_numerator_weak_re_nonneg
    hn hstableA hstableB
  have himag :=
    C.support_numerator_imag_ne_zero_of_maximal_even_contacts
      hn ha0 hb0 hstableA hstableB hmax heven
  exact paperRaisedNumerator_hurwitz_of_weak_re
    n a x ε ha0 hε hstableA
    (by
      intro ω
      simpa [x, ε] using (hweak ω).1)
    (by
      intro ω
      simpa [x, ε] using himag ω)



/-- Full even-order contact forces every balancing atom to lie at a
strictly positive finite frequency. -/
theorem PaperCriticalCertificate.maximal_even_atoms_interior
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (heven : n = 2*(n/2)) :
    ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1 := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  have hfull : C.positiveFiniteNodes.card = n :=
    hmax.trans heven.symm
  have hε : 0 < ε := C.support_leading_pos_of_full_contacts
    hn ha0 hb0 hstableA hstableB hfull
  have hPzero := C.support_numerator_eval_zero_pos_of_maximal_even_contacts
    hn ha0 hb0 hstableA hstableB hmax heven
  have hxzero : 0 < x (n-1) := by
    simpa [x, ε, paperRaisedNumerator_eval_zero n hn] using hPzero
  intro i
  let d : ℕ → ℝ := if C.rightEndpoint i then b else a
  have hd0 : d 0 = 1 := by
    cases h : C.rightEndpoint i <;> simp [d, h, ha0, hb0]
  have hstableD : paperPolynomialHurwitz
      (paperDescendingDenominator n d) := by
    cases h : C.rightEndpoint i
    · simpa [d, h] using hstableA
    · simpa [d, h] using hstableB
  have hdconst : 0 < d n :=
    paperDescendingDenominator_const_pos_of_hurwitz
      n hn d hd0 hstableD
  have hpairzero : 0 <
      paperFeatureDot C.support (paperCompactFeature n d 0) := by
    rw [paperFeatureDot_compactFeature,
      paperHomogenizedPolynomial_zero,
      Polynomial.coeff_zero_eq_eval_zero]
    change 0 < (paperRaisedCrossPolynomial n d x ε).eval 0
    rw [paperRaisedCrossPolynomial_eval_zero n hn d x ε]
    exact mul_pos hdconst hxzero
  have hpairone : 0 <
      paperFeatureDot C.support (paperCompactFeature n d 1) := by
    rw [paperCompactFeature_one n d hd0]
    simpa [paperFeatureDot, Fin.sum_univ_succ, Pi.single_apply]
      using hε
  have hzero : paperFeatureDot C.support
      (paperCompactFeature n d (C.compactFrequency i)) = 0 := by
    simpa [d] using C.support_zero_atom i
  have hu := C.frequency_mem i
  constructor
  · rcases hu.1.eq_or_lt with hz | hp
    · rw [← hz] at hzero
      exact False.elim ((ne_of_gt hpairzero) hzero)
    · exact hp
  · rcases hu.2.eq_or_lt with hz | hp
    · rw [hz] at hzero
      exact False.elim ((ne_of_gt hpairone) hzero)
    · exact hp

/-- All indices in a maximal even-order certificate are positive finite
frequency indices. -/
theorem PaperCriticalCertificate.maximal_even_positiveFiniteIndices_eq_univ
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (heven : n = 2*(n/2)) :
    C.positiveFiniteIndices = Finset.univ := by
  ext i
  simp only [Finset.mem_univ, iff_true]
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ i,
      C.maximal_even_atoms_interior
        hn ha0 hb0 hstableA hstableB hmax heven i⟩



/-- With the optional extra Carathéodory atom, two positive finite atoms
have the same ordinary frequency. -/
theorem PaperCriticalCertificate.maximal_even_extra_atom_duplicate
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (heven : n = 2*(n/2))
    (hatoms : C.atomCount = n+1) :
    ∃ i j : Fin C.atomCount,
      i ≠ j ∧
      C.compactFrequency i / (1-C.compactFrequency i) =
        C.compactFrequency j / (1-C.compactFrequency j) ∧
      C.compactFrequency i = C.compactFrequency j ∧
      C.rightEndpoint i = C.rightEndpoint j := by
  let f : Fin C.atomCount → ℝ :=
    fun i => C.compactFrequency i / (1-C.compactFrequency i)
  have hfull : C.positiveFiniteNodes.card = n :=
    hmax.trans heven.symm
  have hindices := C.maximal_even_positiveFiniteIndices_eq_univ
    hn ha0 hb0 hstableA hstableB hmax heven
  have hcard : (Finset.univ.image f).card = n := by
    change (C.positiveFiniteIndices.image f).card = n at hfull
    rw [hindices] at hfull
    exact hfull
  have hnotinj : ¬ Set.InjOn f (Finset.univ : Finset (Fin C.atomCount)) := by
    intro hinj
    have heq := Finset.card_image_iff.mpr hinj
    simp only [Finset.card_univ, Fintype.card_fin] at heq
    omega
  have hnotinj' : ¬ Function.Injective f := by
    intro hinj
    apply hnotinj
    intro i _ j _ h
    exact hinj h
  simp only [Function.Injective] at hnotinj'
  push_neg at hnotinj'
  obtain ⟨i, j, hf, hij⟩ := hnotinj'
  have hi := C.maximal_even_atoms_interior
    hn ha0 hb0 hstableA hstableB hmax heven i
  have hj := C.maximal_even_atoms_interior
    hn ha0 hb0 hstableA hstableB hmax heven j
  have hiOn : f i ∈ C.positiveFiniteNodesOn (C.rightEndpoint i) := by
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, hi.1, hi.2, rfl⟩
  have hjOn : f j ∈ C.positiveFiniteNodesOn (C.rightEndpoint j) := by
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ j, hj.1, hj.2, rfl⟩
  have hrooti := C.positiveFiniteNodesOn_subset_roots
    hn ha0 hb0 hstableA hstableB (C.rightEndpoint i) hiOn
  have hrootj := C.positiveFiniteNodesOn_subset_roots
    hn ha0 hb0 hstableA hstableB (C.rightEndpoint j) hjOn
  have hstructure := C.maximal_positiveFiniteNodes_structure
    hn ha0 hb0 hstableA hstableB hmax
  have hdisj := hstructure.2.2.1
  have hsame : C.rightEndpoint i = C.rightEndpoint j := by
    cases hri : C.rightEndpoint i <;>
      cases hrj : C.rightEndpoint j
    · rfl
    · exfalso
      have hAi := hrooti
      have hBj := hrootj
      simp only [hri, Bool.false_eq_true, ↓reduceIte] at hAi
      simp only [hrj, ↓reduceIte] at hBj
      have hmem := Finset.mem_inter.mpr
        ⟨hAi, by simpa [f, hf] using hBj⟩
      rw [hdisj] at hmem
      simp at hmem
    · exfalso
      have hBi := hrooti
      have hAj := hrootj
      simp only [hri, ↓reduceIte] at hBi
      simp only [hrj, Bool.false_eq_true, ↓reduceIte] at hAj
      have hmem := Finset.mem_inter.mpr
        ⟨by simpa [f, hf] using hAj, hBi⟩
      rw [hdisj] at hmem
      simp at hmem
    · rfl
  have hfreq : C.compactFrequency i = C.compactFrequency j := by
    have hdi : 1-C.compactFrequency i ≠ 0 :=
      ne_of_gt (sub_pos.mpr hi.2)
    have hdj : 1-C.compactFrequency j ≠ 0 :=
      ne_of_gt (sub_pos.mpr hj.2)
    have hcross := (div_eq_div_iff hdi hdj).mp hf
    nlinarith
  exact ⟨i, j, hij, hf, hfreq, hsame⟩



/-- At maximal positive contact count, the contact nodes on each endpoint
are exactly all positive roots of that endpoint's cross polynomial. -/
theorem PaperCriticalCertificate.maximal_side_nodes_eq_endpoint_roots
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2)) :
    C.positiveFiniteNodesOn false =
      MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n a
          (paperFiniteNumeratorCoeffs n
            (fun j => C.support j.succ)) (C.support 0)) ∧
    C.positiveFiniteNodesOn true =
      MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n b
          (paperFiniteNumeratorCoeffs n
            (fun j => C.support j.succ)) (C.support 0)) := by
  have hside := C.maximal_side_node_counts
    hn ha0 hb0 hstableA hstableB hmax
  have hroots := C.maximal_positiveFiniteNodes_structure
    hn ha0 hb0 hstableA hstableB hmax
  constructor
  · apply Finset.eq_of_subset_of_card_le
      (C.positiveFiniteNodesOn_subset_roots
        hn ha0 hb0 hstableA hstableB false)
    simpa using (hroots.1.trans hside.1.symm).le
  · apply Finset.eq_of_subset_of_card_le
      (C.positiveFiniteNodesOn_subset_roots
        hn ha0 hb0 hstableA hstableB true)
    simpa using (hroots.2.1.trans hside.2.1.symm).le



/-- Arbitrary-order contact interpolation: if both residue sequences have
their first k moments zero, a pointwise contact identity becomes a global
polynomial identity. -/
theorem paperContactResiduePolynomial_identity
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z y : ι → ℝ) (ht : Set.InjOn t s)
    (E O : Polynomial ℝ) (k : ℕ)
    (hE : E.degree ≤ k) (hO : O.degree ≤ k)
    (hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0)
    (hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0)
    (hc : ∀ i ∈ s, E.eval (t i) * z i +
      O.eval (t i) * y i = 0) :
    E * MonicQuinticCoeff.quinticResiduePolynomial s t z +
      O * MonicQuinticCoeff.quinticResiduePolynomial s t y = 0 := by
  apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero s ht
  · exact (Polynomial.degree_add_le _ _).trans_lt (max_lt_iff.mpr
      ⟨MonicQuinticCoeff.degree_mul_quinticResiduePolynomial_lt
          s t z E hE hz,
        MonicQuinticCoeff.degree_mul_quinticResiduePolynomial_lt
          s t y O hO hy⟩)
  · intro i hi
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      MonicQuinticCoeff.eval_quinticResiduePolynomial ht hi]
    rw [← mul_assoc, ← mul_assoc, ← add_mul, hc i hi, zero_mul]

/-- Enough distinct zeros of the odd support component force the even
residue interpolant to vanish. The number of required zeros is controlled
by the moment count. -/
theorem paperContactEvenResidue_zero_of_odd_roots
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z y : ι → ℝ) (ht : Set.InjOn t s)
    (E O : Polynomial ℝ) (k : ℕ)
    (hE : E.degree ≤ k) (hO : O.degree ≤ k)
    (hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0)
    (hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0)
    (hc : ∀ i ∈ s, E.eval (t i) * z i +
      O.eval (t i) * y i = 0)
    (roots : Finset ℝ)
    (hcard : s.card ≤ roots.card + k)
    (hOdd : ∀ r ∈ roots, O.eval r = 0)
    (hEven : ∀ r ∈ roots, E.eval r ≠ 0) :
    MonicQuinticCoeff.quinticResiduePolynomial s t z = 0 := by
  let U := MonicQuinticCoeff.quinticResiduePolynomial s t z
  let V := MonicQuinticCoeff.quinticResiduePolynomial s t y
  have hid : E*U+O*V=0 :=
    paperContactResiduePolynomial_identity
      s t z y ht E O k hE hO hz hy hc
  by_cases hU : U = 0
  · exact hU
  have hdeg := MonicQuinticCoeff.degree_quinticResiduePolynomial_of_moments
    s t z k hz
  change U.degree + k < (s.card : WithBot ℕ) at hdeg
  rw [Polynomial.degree_eq_natDegree hU] at hdeg
  have hnat : U.natDegree + k < s.card := by exact_mod_cast hdeg
  have hlt : U.degree < (roots.card : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hU]
    exact_mod_cast (show U.natDegree < roots.card by omega)
  apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero
    roots Function.injective_id.injOn hlt
  intro r hr
  have heq := congrArg (fun P : Polynomial ℝ => P.eval r) hid
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_zero, hOdd r hr, zero_mul, add_zero] at heq
  exact (mul_eq_zero.mp heq).resolve_left (hEven r hr)

/-- A nonzero residue at one distinct node gives a nonzero interpolation
polynomial on at least one of the two parity components. -/
theorem paperContactResidue_nontrivial
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z y : ι → ℝ) (ht : Set.InjOn t s)
    (hnode : ∃ i ∈ s, z i ≠ 0 ∨ y i ≠ 0) :
    MonicQuinticCoeff.quinticResiduePolynomial s t z ≠ 0 ∨
      MonicQuinticCoeff.quinticResiduePolynomial s t y ≠ 0 := by
  obtain ⟨i, hi, hz | hy⟩ := hnode
  · exact Or.inl
      (MonicQuinticCoeff.quinticResiduePolynomial_ne_zero ht hi hz)
  · exact Or.inr
      (MonicQuinticCoeff.quinticResiduePolynomial_ne_zero ht hi hy)

/-- General high-contact exclusion criterion. The remaining geometric task
in applications is to obtain enough distinct odd-component zeros at which
the even component stays nonzero. -/
theorem paperContactResidue_contradiction_of_many_odd_roots
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z y : ι → ℝ) (ht : Set.InjOn t s)
    (E O : Polynomial ℝ) (k : ℕ)
    (hE : E.degree ≤ k) (hOdegree : O.degree ≤ k)
    (hOne : O ≠ 0)
    (hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0)
    (hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0)
    (hc : ∀ i ∈ s, E.eval (t i) * z i +
      O.eval (t i) * y i = 0)
    (hnode : ∃ i ∈ s, z i ≠ 0 ∨ y i ≠ 0)
    (roots : Finset ℝ)
    (hcard : s.card ≤ roots.card + k)
    (hOdd : ∀ r ∈ roots, O.eval r = 0)
    (hEven : ∀ r ∈ roots, E.eval r ≠ 0) : False := by
  have hU := paperContactEvenResidue_zero_of_odd_roots
    s t z y ht E O k hE hOdegree hz hy hc
      roots hcard hOdd hEven
  have hid := paperContactResiduePolynomial_identity
    s t z y ht E O k hE hOdegree hz hy hc
  rw [hU, mul_zero, zero_add] at hid
  have hV : MonicQuinticCoeff.quinticResiduePolynomial s t y = 0 :=
    (mul_eq_zero.mp hid).resolve_left hOne
  exact (paperContactResidue_nontrivial
    s t z y ht hnode).elim (fun h => h hU) (fun h => h hV)



/-- The uncompactified frequency feature, evaluated at squared frequency t. -/
noncomputable def paperOrdinaryFeature
    (n : ℕ) (a : ℕ → ℝ) (t : ℝ) : Fin (n+1) → ℝ :=
  Fin.cons
    ((paperRaiseCorrection n a).eval t)
    (fun i =>
      (paperGeneralCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n
          (fun j => if i = j then 1 else 0))).eval t)

theorem paperRaiseCorrection_natDegree_le
    (n : ℕ) (a : ℕ → ℝ) :
    (paperRaiseCorrection n a).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [paperRaiseCorrection_coeff, if_neg (not_le.mpr hj)]

theorem paperCompactFeature_eq_scaledOrdinary
    (n : ℕ) (a : ℕ → ℝ) (u : ℝ) (hu : u ≠ 1) :
    paperCompactFeature n a u =
      (1-u)^n • paperOrdinaryFeature n a (u/(1-u)) := by
  ext i
  refine Fin.cases ?_ ?_ i
  · change paperHomogenizedPolynomial n
      (paperRaiseCorrection n a) u =
        (1-u)^n * (paperRaiseCorrection n a).eval (u/(1-u))
    exact paperHomogenizedPolynomial_eq n _
      (paperRaiseCorrection_natDegree_le n a) u hu
  · intro j
    change paperHomogenizedPolynomial n
      (paperGeneralCrossPolynomial n a
        (paperFiniteNumeratorCoeffs n
          (fun k => if j = k then 1 else 0))) u =
      (1-u)^n *
        (paperGeneralCrossPolynomial n a
          (paperFiniteNumeratorCoeffs n
            (fun k => if j = k then 1 else 0))).eval (u/(1-u))
    apply paperHomogenizedPolynomial_eq n _
    exact (paperGeneralCrossPolynomial_natDegree_le n a _).trans
      (Nat.sub_le n 1)
    exact hu

/-- In a maximal even-order certificate, compactification can be removed
from the entire positive barycentric balance. -/
theorem PaperCriticalCertificate.maximal_even_ordinary_balance
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (heven : n = 2*(n/2)) :
    (∀ i : Fin C.atomCount,
      0 < C.weight i * (1-C.compactFrequency i)^n) ∧
    (∑ i : Fin C.atomCount,
      (C.weight i * (1-C.compactFrequency i)^n) •
        paperOrdinaryFeature n
          (if C.rightEndpoint i then b else a)
          (C.compactFrequency i /
            (1-C.compactFrequency i))) = 0 := by
  have hinter := C.maximal_even_atoms_interior
    hn ha0 hb0 hstableA hstableB hmax heven
  constructor
  · intro i
    exact mul_pos (C.weight_pos i)
      (pow_pos (sub_pos.mpr (hinter i).2) n)
  · calc
      _ = ∑ i : Fin C.atomCount,
          C.weight i •
            paperCompactFeature n
              (if C.rightEndpoint i then b else a)
              (C.compactFrequency i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [paperCompactFeature_eq_scaledOrdinary
          n _ _ (ne_of_lt (hinter i).2)]
        simp only [smul_smul, smul_eq_mul]
      _ = 0 := C.balance

/-- The decompactified balance, resolved into the leading coefficient and
all finite numerator coefficient directions. -/
theorem PaperCriticalCertificate.maximal_even_ordinary_coefficient_balance
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (heven : n = 2*(n/2)) :
    (∑ i : Fin C.atomCount,
      C.weight i * (1-C.compactFrequency i)^n *
        (paperRaiseCorrection n
          (if C.rightEndpoint i then b else a)).eval
            (C.compactFrequency i /
              (1-C.compactFrequency i))) = 0 ∧
    (∀ j : Fin n,
      (∑ i : Fin C.atomCount,
        C.weight i * (1-C.compactFrequency i)^n *
          (paperGeneralCrossPolynomial n
            (if C.rightEndpoint i then b else a)
            (paperFiniteNumeratorCoeffs n
              (fun k => if j = k then 1 else 0))).eval
                (C.compactFrequency i /
                  (1-C.compactFrequency i))) = 0) := by
  have hbalance := (C.maximal_even_ordinary_balance
    hn ha0 hb0 hstableA hstableB hmax heven).2
  have hcoord (j : Fin (n+1)) :
      (∑ i : Fin C.atomCount,
        C.weight i * (1-C.compactFrequency i)^n *
          paperOrdinaryFeature n
            (if C.rightEndpoint i then b else a)
            (C.compactFrequency i /
              (1-C.compactFrequency i)) j) = 0 := by
    have h := congrArg (fun v : Fin (n+1) → ℝ => v j) hbalance
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] using h
  constructor
  · simpa [paperOrdinaryFeature] using hcoord 0
  · intro j
    simpa [paperOrdinaryFeature] using hcoord j.succ



theorem jw_pow_even_im (ω : ℝ) (m : ℕ) :
    ((jw ω)^(2*m)).im = 0 := by
  have hsq : (jw ω)^2 = ((-ω^2 : ℝ) : ℂ) := by
    rw [jw, mul_pow, Complex.I_sq]
    norm_num
  rw [pow_mul, hsq]
  rw [← Complex.ofReal_pow (-ω^2) m]
  exact Complex.ofReal_im _

theorem jw_pow_odd_im (ω : ℝ) (m : ℕ) :
    ((jw ω)^(2*m+1)).im = (-1 : ℝ)^m * ω^(2*m+1) := by
  rw [pow_succ, pow_mul]
  have hsq : (jw ω)^2 = ((-ω^2 : ℝ) : ℂ) := by
    rw [jw, mul_pow, Complex.I_sq]
    norm_num
  rw [hsq, Complex.mul_im]
  have hreal : (((((-ω^2 : ℝ) : ℂ)^m)).re) = (-ω^2)^m := by
    rw [← Complex.ofReal_pow (-ω^2) m]
    exact Complex.ofReal_re _
  have himag : (((((-ω^2 : ℝ) : ℂ)^m)).im) = 0 := by
    rw [← Complex.ofReal_pow (-ω^2) m]
    exact Complex.ofReal_im _
  rw [hreal, himag]
  have hjre : (jw ω).re = 0 := by simp [jw]
  have hjim : (jw ω).im = ω := by simp [jw]
  rw [hjre, hjim]
  simp only [zero_mul, add_zero]
  rw [neg_eq_neg_one_mul, mul_pow, ← pow_mul, pow_succ]
  ring

theorem imag_part_aeval_eq_odd_coeff_sum
    (p : Polynomial ℝ) (n : ℕ) (ω : ℝ)
    (hp : p.natDegree < 2*n) :
    (Polynomial.aeval (jw ω) p : ℂ).im =
      ∑ j ∈ Finset.range n,
        p.coeff (2*j+1) * (-1 : ℝ)^j * ω^(2*j+1) := by
  rw [Polynomial.aeval_eq_sum_range' hp]
  rw [Complex.im_sum]
  rw [sum_range_pair]
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.smul_im, jw_pow_even_im,
    jw_pow_odd_im]
  ring

noncomputable def paperAxisEven
    (n : ℕ) (p : Polynomial ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (n+1),
    Polynomial.monomial j (p.coeff (2*j) * (-1 : ℝ)^j)

noncomputable def paperAxisOdd
    (n : ℕ) (p : Polynomial ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (n+1),
    Polynomial.monomial j (p.coeff (2*j+1) * (-1 : ℝ)^j)

theorem paperAxisEven_coeff
    (n : ℕ) (p : Polynomial ℝ) (j : ℕ) :
    (paperAxisEven n p).coeff j =
      if j ≤ n then p.coeff (2*j) * (-1 : ℝ)^j else 0 := by
  simp [paperAxisEven, Polynomial.finset_sum_coeff,
    Polynomial.coeff_monomial, Finset.sum_ite_eq', Nat.lt_succ_iff]

theorem paperAxisOdd_coeff
    (n : ℕ) (p : Polynomial ℝ) (j : ℕ) :
    (paperAxisOdd n p).coeff j =
      if j ≤ n then p.coeff (2*j+1) * (-1 : ℝ)^j else 0 := by
  simp [paperAxisOdd, Polynomial.finset_sum_coeff,
    Polynomial.coeff_monomial, Finset.sum_ite_eq', Nat.lt_succ_iff]

theorem paperAxisEven_natDegree_le
    (n : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ n) :
    (paperAxisEven n p).natDegree ≤ n/2 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [paperAxisEven_coeff]
  by_cases hjn : j ≤ n
  · rw [if_pos hjn]
    have htwice : p.natDegree < 2*j := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt htwice]
    simp
  · rw [if_neg hjn]

theorem paperAxisOdd_natDegree_le
    (n : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ n) :
    (paperAxisOdd n p).natDegree ≤ (n-1)/2 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [paperAxisOdd_coeff]
  by_cases hjn : j ≤ n
  · rw [if_pos hjn]
    have htwice : p.natDegree < 2*j+1 := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt htwice]
    simp
  · rw [if_neg hjn]

theorem paperAxisEven_eval
    (n : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ n) (ω : ℝ) :
    (Polynomial.aeval (jw ω) p : ℂ).re =
      (paperAxisEven n p).eval (ω^2) := by
  have hdegree : p.natDegree < 2*(n+1) := by omega
  rw [real_part_aeval_eq_even_coeff_sum p (n+1) ω hdegree]
  simp only [paperAxisEven, Polynomial.eval_finset_sum,
    Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_mul]

theorem paperAxisOdd_eval
    (n : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ n) (ω : ℝ) :
    (Polynomial.aeval (jw ω) p : ℂ).im =
      ω * (paperAxisOdd n p).eval (ω^2) := by
  have hdegree : p.natDegree < 2*(n+1) := by omega
  rw [imag_part_aeval_eq_odd_coeff_sum
    p (n+1) ω hdegree]
  simp only [paperAxisOdd, Polynomial.eval_finset_sum,
    Polynomial.eval_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ, pow_mul]
  ring

/-- A Hurwitz polynomial's even and odd axis components cannot both
vanish at any nonnegative squared frequency. -/
theorem paperAxisEvenOdd_no_common_nonnegative
    (n : ℕ) (p : Polynomial ℝ)
    (hpdegree : p.natDegree ≤ n)
    (hstable : paperPolynomialHurwitz p)
    (t : ℝ) (ht : 0 ≤ t) :
    (paperAxisEven n p).eval t ≠ 0 ∨
      (paperAxisOdd n p).eval t ≠ 0 := by
  by_contra h
  push_neg at h
  let ω := Real.sqrt t
  have hω : ω^2 = t := Real.sq_sqrt ht
  have hre := paperAxisEven_eval n p hpdegree ω
  have him := paperAxisOdd_eval n p hpdegree ω
  have hz : Polynomial.aeval (jw ω) p = (0 : ℂ) := by
    apply Complex.ext
    · rw [hre, hω, h.1]
      simp
    · rw [him, hω, h.2]
      simp
  exact (paperPolynomialHurwitz_imag_ne_zero p hstable ω) hz

/-- At every squared frequency, the raised real cross polynomial is the
dot product of the numerator and denominator parity components. -/
theorem paperRaisedCross_eval_axis
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) (ε : ℝ)
    (ha0 : a 0 = 1) (hε : 0 < ε)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (ω : ℝ) :
    let P := paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n
    let D := paperDescendingDenominator n a
    (paperRaisedCrossPolynomial n a x ε).eval (ω^2) =
      (paperAxisEven n P).eval (ω^2) *
        (paperAxisEven n D).eval (ω^2) +
      ω^2 * (paperAxisOdd n P).eval (ω^2) *
        (paperAxisOdd n D).eval (ω^2) := by
  dsimp
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let D := paperDescendingDenominator n a
  let Q := paperRaisedCrossPolynomial n a x ε
  have hpdegree : P.natDegree ≤ n := by
    exact (paperDescendingNumerator_raise_natDegree_eq
      n x ε hε).le
  have hddegree : D.natDegree ≤ n := by
    exact (paperDescendingDenominator_natDegree_eq n a ha0).le
  have hDne : Polynomial.aeval (jw ω) D ≠ (0 : ℂ) :=
    paperPolynomialHurwitz_imag_ne_zero D hstable ω
  have hnorm : Complex.normSq
      (Polynomial.aeval (jw ω) D : ℂ) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hDne)
  have hquot : ((Polynomial.aeval (jw ω) P : ℂ) /
      Polynomial.aeval (jw ω) D).re =
      Q.eval (ω^2) /
        Complex.normSq (Polynomial.aeval (jw ω) D : ℂ) := by
    simpa [P, D, Q, paperRaisedCrossPolynomial,
      Polynomial.eval_add, Polynomial.eval_C_mul] using
      paperDescending_degree_raised_re n hn a x ε ω
  rw [complex_div_re_eq] at hquot
  have hnum := congrArg
    (fun y : ℝ =>
      y * Complex.normSq (Polynomial.aeval (jw ω) D : ℂ))
    hquot
  simp only [div_mul_cancel₀ _ hnorm] at hnum
  have hPE := paperAxisEven_eval n P hpdegree ω
  have hPO := paperAxisOdd_eval n P hpdegree ω
  have hDE := paperAxisEven_eval n D hddegree ω
  have hDO := paperAxisOdd_eval n D hddegree ω
  rw [hPE, hPO, hDE, hDO] at hnum
  change Q.eval (ω^2) =
    (paperAxisEven n P).eval (ω^2) *
      (paperAxisEven n D).eval (ω^2) +
    ω^2 * (paperAxisOdd n P).eval (ω^2) *
      (paperAxisOdd n D).eval (ω^2)
  nlinarith [hnum]

/-- Polynomial-level parity identity for the raised cross polynomial.
Equality first holds at every nonnegative squared frequency and then
extends to all real arguments by polynomial identity. -/
theorem paperRaisedCross_axis_identity
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) (ε : ℝ)
    (ha0 : a 0 = 1) (hε : 0 < ε)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a)) :
    let P := paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n
    let D := paperDescendingDenominator n a
    paperRaisedCrossPolynomial n a x ε =
      paperAxisEven n P * paperAxisEven n D +
        Polynomial.X * paperAxisOdd n P *
          paperAxisOdd n D := by
  dsimp
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let D := paperDescendingDenominator n a
  let Q := paperRaisedCrossPolynomial n a x ε
  let R := paperAxisEven n P * paperAxisEven n D +
    Polynomial.X * paperAxisOdd n P *
      paperAxisOdd n D
  have hsub : Set.Ici (0 : ℝ) ⊆
      {t : ℝ | Q.eval t = R.eval t} := by
    intro t ht
    let ω := Real.sqrt t
    have hω : ω^2 = t := Real.sq_sqrt ht
    have heq := paperRaisedCross_eval_axis
      n hn a x ε ha0 hε hstable ω
    change Q.eval (ω^2) =
      (paperAxisEven n P).eval (ω^2) *
        (paperAxisEven n D).eval (ω^2) +
      ω^2 * (paperAxisOdd n P).eval (ω^2) *
        (paperAxisOdd n D).eval (ω^2) at heq
    rw [hω] at heq
    simpa [R, Polynomial.eval_add, Polynomial.eval_mul]
      using heq
  have hinf : Set.Infinite {t : ℝ | Q.eval t = R.eval t} :=
    (Set.Ici_infinite (0 : ℝ)).mono hsub
  exact Polynomial.eq_of_infinite_eval_eq Q R hinf



/-- Recover a real polynomial from the even and odd frequency polynomials
by substituting negative squared arguments. -/
theorem paperAxisEvenOdd_real_eval
    (n : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ n) (s : ℝ) :
    p.eval s =
      (paperAxisEven n p).eval (-s^2) +
        s * (paperAxisOdd n p).eval (-s^2) := by
  have hdegree : p.natDegree < 2*(n+1) := by omega
  rw [Polynomial.eval_eq_sum_range' hdegree,
    sum_range_pair]
  simp only [paperAxisEven, paperAxisOdd,
    Polynomial.eval_finset_sum, Polynomial.eval_monomial,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hpow : (-1 : ℝ)^j * (-s^2)^j = s^(2*j) := by
    rw [← mul_pow]
    norm_num
    rw [pow_mul]
  calc
    _ = p.coeff (2*j) * s^(2*j) +
        s * p.coeff (2*j+1) * s^(2*j) := by
          rw [pow_succ]
          ring
    _ = p.coeff (2*j) * ((-1 : ℝ)^j * (-s^2)^j) +
        s * p.coeff (2*j+1) * ((-1 : ℝ)^j * (-s^2)^j) := by
          rw [hpow]
    _ = _ := by ring

/-- A polynomial is reconstructed algebraically from its even and odd
axis components. -/
theorem paperAxisEvenOdd_polynomial_identity
    (n : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ n) :
    p = (paperAxisEven n p).comp (-Polynomial.X^2) +
      Polynomial.X * (paperAxisOdd n p).comp (-Polynomial.X^2) := by
  let R := (paperAxisEven n p).comp (-Polynomial.X^2) +
    Polynomial.X * (paperAxisOdd n p).comp (-Polynomial.X^2)
  have hsub : Set.univ ⊆ {s : ℝ | p.eval s = R.eval s} := by
    intro s _
    have h := paperAxisEvenOdd_real_eval n p hp s
    simpa [R, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_comp] using h
  have hinf : Set.Infinite {s : ℝ | p.eval s = R.eval s} :=
    Set.infinite_univ.mono hsub
  exact Polynomial.eq_of_infinite_eval_eq p R hinf

/-- Hurwitz stability rules out a common complex root of the two axis
components: a common root would produce symmetric roots of p, one in the
closed right half-plane. -/
theorem paperAxisEvenOdd_no_common_complex
    (n : ℕ) (p : Polynomial ℝ)
    (hpdegree : p.natDegree ≤ n)
    (hstable : paperPolynomialHurwitz p)
    (t : ℂ) :
    Polynomial.aeval t (paperAxisEven n p) ≠ 0 ∨
      Polynomial.aeval t (paperAxisOdd n p) ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨s, hs⟩ :=
    IsAlgClosed.exists_pow_nat_eq (-t) (show 0 < 2 by decide)
  have ht : -s^2 = t := by rw [hs]; ring
  have hzero (u : ℂ) (hu : -u^2 = t) :
      Polynomial.aeval u p = 0 := by
    rw [paperAxisEvenOdd_polynomial_identity n p hpdegree]
    simp only [Polynomial.aeval_add, Polynomial.aeval_mul,
      Polynomial.aeval_comp, map_neg, map_pow,
      Polynomial.aeval_X]
    rw [hu, h.1, h.2]
    ring
  by_cases hre : 0 ≤ s.re
  · exact (hstable s hre) (hzero s ht)
  · have hnegre : 0 ≤ (-s).re := by
      simp only [Complex.neg_re]
      linarith
    have htneg : -(-s)^2 = t := by
      calc
        -(-s)^2 = -s^2 := by ring
        _ = t := ht
    exact (hstable (-s) hnegre) (hzero (-s) htneg)

/-- The parity components of a Hurwitz polynomial are coprime. This
abstract Hermite--Biehler ingredient follows from symmetric-root
exclusion and algebraic closedness of the complex numbers. -/
theorem paperAxisEvenOdd_coprime
    (n : ℕ) (p : Polynomial ℝ)
    (hpdegree : p.natDegree ≤ n)
    (hstable : paperPolynomialHurwitz p) :
    IsCoprime (paperAxisEven n p) (paperAxisOdd n p) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (k := ℝ) ℂ (paperAxisEven n p) (paperAxisOdd n p)).2
  intro t
  exact paperAxisEvenOdd_no_common_complex
    n p hpdegree hstable t

/-- In a maximal even-order contact certificate, the supporting numerator's
even and odd axis components are coprime. -/
theorem PaperCriticalCertificate.support_axis_coprime_of_maximal_even_contacts
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (heven : n = 2*(n/2)) :
    let P := paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ)) +
      Polynomial.C (C.support 0) * Polynomial.X^n
    IsCoprime (paperAxisEven n P) (paperAxisOdd n P) := by
  dsimp
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  have hfull : C.positiveFiniteNodes.card = n :=
    hmax.trans heven.symm
  have hε : 0 < ε :=
    C.support_leading_pos_of_full_contacts
      hn ha0 hb0 hstableA hstableB hfull
  have hpdegree : P.natDegree ≤ n :=
    (paperDescendingNumerator_raise_natDegree_eq n x ε hε).le
  have hpstable : paperPolynomialHurwitz P := by
    simpa [P, x, ε] using
      C.support_numerator_hurwitz_of_maximal_even_contacts
        hn ha0 hb0 hstableA hstableB hmax heven
  exact paperAxisEvenOdd_coprime n P hpdegree hpstable

/-- Coprime parity components exclude a full-contact residue balance:
the even component has degree k, while both residue interpolants have
degree strictly below k after k moments vanish at 2k nodes. -/
theorem paperContactResidue_no_full_even_balance_of_coprime
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z y : ι → ℝ)
    (ht : Set.InjOn t s) (E O : Polynomial ℝ) (k : ℕ)
    (hcard : s.card = 2*k)
    (hEdegree : E.degree = (k : WithBot ℕ))
    (hOdegree : O.degree ≤ k)
    (hcop : IsCoprime E O)
    (hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0)
    (hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0)
    (hc : ∀ i ∈ s, E.eval (t i) * z i +
      O.eval (t i) * y i = 0)
    (hnode : ∃ i ∈ s, z i ≠ 0 ∨ y i ≠ 0) : False := by
  let U := MonicQuinticCoeff.quinticResiduePolynomial s t z
  let V := MonicQuinticCoeff.quinticResiduePolynomial s t y
  have hEne : E ≠ 0 := by
    intro he
    simp [he] at hEdegree
  have hid : E*U+O*V=0 :=
    paperContactResiduePolynomial_identity s t z y ht E O k
      hEdegree.le hOdegree hz hy hc
  obtain ⟨M, hVM, _⟩ :=
    MonicQuinticCoeff.coprime_quintic_contact_multiplier
      hcop hEne hid
  have hVbound := MonicQuinticCoeff.degree_quinticResiduePolynomial_of_moments
    s t y k hy
  change V.degree + k < (s.card : WithBot ℕ) at hVbound
  rw [hcard] at hVbound
  have hVzero : V = 0 := by
    by_contra hv
    have hVnat : V.natDegree + k < 2*k := by
      rw [Polynomial.degree_eq_natDegree hv] at hVbound
      exact_mod_cast hVbound
    have hEnat : E.natDegree = k := by
      rw [Polynomial.degree_eq_natDegree hEne] at hEdegree
      exact_mod_cast hEdegree
    have hdiv : E ∣ V := ⟨M, hVM⟩
    have hle := Polynomial.natDegree_le_of_dvd hdiv hv
    omega
  rw [hVzero, mul_zero, add_zero] at hid
  have hUzero : U = 0 :=
    (mul_eq_zero.mp hid).resolve_left hEne
  exact (paperContactResidue_nontrivial s t z y ht hnode).elim
    (fun h => h hUzero) (fun h => h hVzero)

/-- Both parity components cannot have a common real root when the
original polynomial is Hurwitz stable. -/
theorem paperAxisEvenOdd_no_common_real
    (n : ℕ) (p : Polynomial ℝ)
    (hpdegree : p.natDegree ≤ n)
    (hstable : paperPolynomialHurwitz p)
    (t : ℝ) :
    (paperAxisEven n p).eval t ≠ 0 ∨
      (paperAxisOdd n p).eval t ≠ 0 := by
  by_cases ht : 0 ≤ t
  · exact paperAxisEvenOdd_no_common_nonnegative
      n p hpdegree hstable t ht
  · by_contra h
    push_neg at h
    let s := Real.sqrt (-t)
    have hspos : 0 < s := Real.sqrt_pos.2 (by linarith)
    have hs2 : -s^2 = t := by
      dsimp [s]
      rw [Real.sq_sqrt (by linarith : 0 ≤ -t)]
      ring
    have hpzero : p.eval s = 0 := by
      rw [paperAxisEvenOdd_real_eval n p hpdegree s,
        hs2, h.1, h.2]
      ring
    have hpcomplex : Polynomial.aeval (s : ℂ) p = 0 := by
      have hcast : (algebraMap ℝ ℂ) (p.eval s) = 0 := by
        exact congrArg (algebraMap ℝ ℂ) hpzero
      have hsmap : (algebraMap ℝ ℂ) s = (s : ℂ) := rfl
      rw [Polynomial.aeval_def, ← hsmap,
        Polynomial.eval₂_at_apply]
      exact hcast
    exact (hstable (s : ℂ) (by simpa using hspos.le)) hpcomplex



theorem paperRaisedNumerator_natDegree_le
    (n : ℕ) (x : ℕ → ℝ) (ε : ℝ) :
    (paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [Polynomial.coeff_add, paperDescendingNumerator_coeff,
    if_neg (by omega : ¬ j < n), Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  simp [show j ≠ n by omega]

theorem paperRaisedCross_eval_axis_any
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) (ε : ℝ)
    (ha0 : a 0 = 1)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (ω : ℝ) :
    let P := paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n
    let D := paperDescendingDenominator n a
    (paperRaisedCrossPolynomial n a x ε).eval (ω^2) =
      (paperAxisEven n P).eval (ω^2) *
        (paperAxisEven n D).eval (ω^2) +
      ω^2 * (paperAxisOdd n P).eval (ω^2) *
        (paperAxisOdd n D).eval (ω^2) := by
  dsimp
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let D := paperDescendingDenominator n a
  let Q := paperRaisedCrossPolynomial n a x ε
  have hpdegree : P.natDegree ≤ n :=
    paperRaisedNumerator_natDegree_le n x ε
  have hddegree : D.natDegree ≤ n := by
    exact (paperDescendingDenominator_natDegree_eq n a ha0).le
  have hDne : Polynomial.aeval (jw ω) D ≠ (0 : ℂ) :=
    paperPolynomialHurwitz_imag_ne_zero D hstable ω
  have hnorm : Complex.normSq
      (Polynomial.aeval (jw ω) D : ℂ) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hDne)
  have hquot : ((Polynomial.aeval (jw ω) P : ℂ) /
      Polynomial.aeval (jw ω) D).re =
      Q.eval (ω^2) /
        Complex.normSq (Polynomial.aeval (jw ω) D : ℂ) := by
    simpa [P, D, Q, paperRaisedCrossPolynomial,
      Polynomial.eval_add, Polynomial.eval_C_mul] using
      paperDescending_degree_raised_re n hn a x ε ω
  rw [complex_div_re_eq] at hquot
  have hnum := congrArg
    (fun y : ℝ =>
      y * Complex.normSq (Polynomial.aeval (jw ω) D : ℂ))
    hquot
  simp only [div_mul_cancel₀ _ hnorm] at hnum
  have hPE := paperAxisEven_eval n P hpdegree ω
  have hPO := paperAxisOdd_eval n P hpdegree ω
  have hDE := paperAxisEven_eval n D hddegree ω
  have hDO := paperAxisOdd_eval n D hddegree ω
  rw [hPE, hPO, hDE, hDO] at hnum
  change Q.eval (ω^2) =
    (paperAxisEven n P).eval (ω^2) *
      (paperAxisEven n D).eval (ω^2) +
    ω^2 * (paperAxisOdd n P).eval (ω^2) *
      (paperAxisOdd n D).eval (ω^2)
  nlinarith [hnum]

/-- Polynomial-level parity identity for the raised cross polynomial.
Equality first holds at every nonnegative squared frequency and then
extends to all real arguments by polynomial identity. -/
theorem paperRaisedCross_axis_identity_any
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) (ε : ℝ)
    (ha0 : a 0 = 1)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a)) :
    let P := paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n
    let D := paperDescendingDenominator n a
    paperRaisedCrossPolynomial n a x ε =
      paperAxisEven n P * paperAxisEven n D +
        Polynomial.X * paperAxisOdd n P *
          paperAxisOdd n D := by
  dsimp
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let D := paperDescendingDenominator n a
  let Q := paperRaisedCrossPolynomial n a x ε
  let R := paperAxisEven n P * paperAxisEven n D +
    Polynomial.X * paperAxisOdd n P *
      paperAxisOdd n D
  have hsub : Set.Ici (0 : ℝ) ⊆
      {t : ℝ | Q.eval t = R.eval t} := by
    intro t ht
    let ω := Real.sqrt t
    have hω : ω^2 = t := Real.sq_sqrt ht
    have heq := paperRaisedCross_eval_axis_any
      n hn a x ε ha0 hstable ω
    change Q.eval (ω^2) =
      (paperAxisEven n P).eval (ω^2) *
        (paperAxisEven n D).eval (ω^2) +
      ω^2 * (paperAxisOdd n P).eval (ω^2) *
        (paperAxisOdd n D).eval (ω^2) at heq
    rw [hω] at heq
    simpa [R, Polynomial.eval_add, Polynomial.eval_mul]
      using heq
  have hinf : Set.Infinite {t : ℝ | Q.eval t = R.eval t} :=
    (Set.Ici_infinite (0 : ℝ)).mono hsub
  exact Polynomial.eq_of_infinite_eval_eq Q R hinf





theorem paperDescendingNumerator_basis
    (n : ℕ) (r : Fin n) :
    paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n
        (fun j => if r = j then 1 else 0)) =
      Polynomial.X^(n-1-r.val) := by
  ext m
  rw [paperDescendingNumerator_coeff, Polynomial.coeff_X_pow]
  by_cases hm : m < n
  · rw [if_pos hm]
    have hr : n-1-m < n := by omega
    simp only [paperFiniteNumeratorCoeffs, dif_pos hr]
    by_cases h : r.val = n-1-m
    · have heq : r = (⟨n-1-m, hr⟩ : Fin n) := Fin.ext h
      have hm' : m = n-1-r.val := by omega
      rw [if_pos heq, if_pos hm']
    · have hne : r ≠ (⟨n-1-m, hr⟩ : Fin n) := by
        intro heq
        exact h (congrArg Fin.val heq)
      have hm' : m ≠ n-1-r.val := by omega
      rw [if_neg hne, if_neg hm']
  · rw [if_neg hm]
    have hm' : m ≠ n-1-r.val := by omega
    rw [if_neg hm']

theorem paperAxisEven_X_even
    (n j : ℕ) (hj : 2*j ≤ n) :
    paperAxisEven n (Polynomial.X^(2*j)) =
      Polynomial.C ((-1 : ℝ)^j) * Polynomial.X^j := by
  ext m
  rw [paperAxisEven_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_X_pow]
  by_cases hm : m = j
  · subst m
    simp [show j ≤ n by omega]
  · have htwice : 2*m ≠ 2*j := by omega
    by_cases hmn : m ≤ n
    · simp [hmn, htwice, hm]
    · simp [hmn, hm]

theorem paperAxisOdd_X_even
    (n j : ℕ) :
    paperAxisOdd n (Polynomial.X^(2*j)) = 0 := by
  ext m
  rw [paperAxisOdd_coeff, Polynomial.coeff_zero]
  by_cases hm : m ≤ n
  · rw [if_pos hm, Polynomial.coeff_X_pow,
      if_neg (by omega : 2*m+1 ≠ 2*j)]
    simp
  · rw [if_neg hm]

theorem paperAxisEven_X_odd
    (n j : ℕ) :
    paperAxisEven n (Polynomial.X^(2*j+1)) = 0 := by
  ext m
  rw [paperAxisEven_coeff, Polynomial.coeff_zero]
  by_cases hm : m ≤ n
  · rw [if_pos hm, Polynomial.coeff_X_pow,
      if_neg (by omega : 2*m ≠ 2*j+1)]
    simp
  · rw [if_neg hm]

theorem paperAxisOdd_X_odd
    (n j : ℕ) (hj : 2*j+1 ≤ n) :
    paperAxisOdd n (Polynomial.X^(2*j+1)) =
      Polynomial.C ((-1 : ℝ)^j) * Polynomial.X^j := by
  ext m
  rw [paperAxisOdd_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_X_pow]
  by_cases hm : m = j
  · subst m
    simp [show j ≤ n by omega]
  · have htwice : 2*m+1 ≠ 2*j+1 := by omega
    by_cases hmn : m ≤ n
    · simp [hmn, htwice, hm]
    · simp [hmn, hm]

/-- The general cross polynomial in an even monomial numerator direction. -/
theorem paperGeneralCross_basis_even
    (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (ha0 : a 0 = 1)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (j : ℕ) (hj : 2*j < n) :
    let r : Fin n := ⟨n-1-2*j, by omega⟩
    paperGeneralCrossPolynomial n a
      (paperFiniteNumeratorCoeffs n
        (fun i => if r = i then 1 else 0)) =
      Polynomial.C ((-1 : ℝ)^j) * Polynomial.X^j *
        paperAxisEven n (paperDescendingDenominator n a) := by
  dsimp
  let r : Fin n := ⟨n-1-2*j, by omega⟩
  let x := paperFiniteNumeratorCoeffs n
    (fun i => if r = i then 1 else 0)
  have hpow : n-1-r.val = 2*j := by dsimp [r]; omega
  have hnum : paperDescendingNumerator n x =
      Polynomial.X^(2*j) := by
    simpa [x, hpow] using paperDescendingNumerator_basis n r
  have h := paperRaisedCross_axis_identity_any
    n hn a x 0 ha0 hstable
  simpa [paperRaisedCrossPolynomial, hnum,
    paperAxisEven_X_even n j (by omega),
    paperAxisOdd_X_even, mul_assoc] using h

/-- The general cross polynomial in an odd monomial numerator direction. -/
theorem paperGeneralCross_basis_odd
    (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (ha0 : a 0 = 1)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (j : ℕ) (hj : 2*j+1 < n) :
    let r : Fin n := ⟨n-1-(2*j+1), by omega⟩
    paperGeneralCrossPolynomial n a
      (paperFiniteNumeratorCoeffs n
        (fun i => if r = i then 1 else 0)) =
      Polynomial.X * (Polynomial.C ((-1 : ℝ)^j) *
        Polynomial.X^j) *
        paperAxisOdd n (paperDescendingDenominator n a) := by
  dsimp
  let r : Fin n := ⟨n-1-(2*j+1), by omega⟩
  let x := paperFiniteNumeratorCoeffs n
    (fun i => if r = i then 1 else 0)
  have hpow : n-1-r.val = 2*j+1 := by dsimp [r]; omega
  have hnum : paperDescendingNumerator n x =
      Polynomial.X^(2*j+1) := by
    simpa [x, hpow] using paperDescendingNumerator_basis n r
  have h := paperRaisedCross_axis_identity_any
    n hn a x 0 ha0 hstable
  simpa [paperRaisedCrossPolynomial, hnum,
    paperAxisEven_X_odd,
    paperAxisOdd_X_odd n j (by omega),
    mul_assoc] using h



theorem paperCoefficientBalance_even_moments
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (n : ℕ) (hn : 0 < n)
    (d : ι → ℕ → ℝ) (w t : ι → ℝ)
    (hmonic : ∀ i ∈ s, d i 0 = 1)
    (hstable : ∀ i ∈ s,
      paperPolynomialHurwitz (paperDescendingDenominator n (d i)))
    (hbalance : ∀ r : Fin n,
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial n (d i)
          (paperFiniteNumeratorCoeffs n
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0)
    (j : ℕ) (hj : 2*j < n) :
    (∑ i ∈ s, (t i)^j *
      (w i * (paperAxisEven n
        (paperDescendingDenominator n (d i))).eval (t i))) = 0 := by
  let r : Fin n := ⟨n-1-2*j, by omega⟩
  have hcoord := hbalance r
  have heq :
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial n (d i)
          (paperFiniteNumeratorCoeffs n
            (fun k => if r = k then 1 else 0))).eval (t i)) =
      (-1 : ℝ)^j *
        (∑ i ∈ s, (t i)^j *
          (w i * (paperAxisEven n
            (paperDescendingDenominator n (d i))).eval (t i))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hpoly := paperGeneralCross_basis_even
      n hn (d i) (hmonic i hi) (hstable i hi) j hj
    change paperGeneralCrossPolynomial n (d i)
      (paperFiniteNumeratorCoeffs n
        (fun k => if r = k then 1 else 0)) =
      Polynomial.C ((-1 : ℝ)^j) * Polynomial.X^j *
        paperAxisEven n (paperDescendingDenominator n (d i)) at hpoly
    rw [hpoly]
    simp only [Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    ring
  rw [heq] at hcoord
  exact (mul_eq_zero.mp hcoord).resolve_left
    (pow_ne_zero _ (by norm_num))

theorem paperCoefficientBalance_odd_moments
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (n : ℕ) (hn : 0 < n)
    (d : ι → ℕ → ℝ) (w t : ι → ℝ)
    (hmonic : ∀ i ∈ s, d i 0 = 1)
    (hstable : ∀ i ∈ s,
      paperPolynomialHurwitz (paperDescendingDenominator n (d i)))
    (hbalance : ∀ r : Fin n,
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial n (d i)
          (paperFiniteNumeratorCoeffs n
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0)
    (j : ℕ) (hj : 2*j+1 < n) :
    (∑ i ∈ s, (t i)^j *
      (w i * t i * (paperAxisOdd n
        (paperDescendingDenominator n (d i))).eval (t i))) = 0 := by
  let r : Fin n := ⟨n-1-(2*j+1), by omega⟩
  have hcoord := hbalance r
  have heq :
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial n (d i)
          (paperFiniteNumeratorCoeffs n
            (fun k => if r = k then 1 else 0))).eval (t i)) =
      (-1 : ℝ)^j *
        (∑ i ∈ s, (t i)^j *
          (w i * t i * (paperAxisOdd n
            (paperDescendingDenominator n (d i))).eval (t i))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hpoly := paperGeneralCross_basis_odd
      n hn (d i) (hmonic i hi) (hstable i hi) j hj
    change paperGeneralCrossPolynomial n (d i)
      (paperFiniteNumeratorCoeffs n
        (fun k => if r = k then 1 else 0)) =
      Polynomial.X * (Polynomial.C ((-1 : ℝ)^j) *
        Polynomial.X^j) *
        paperAxisOdd n (paperDescendingDenominator n (d i)) at hpoly
    rw [hpoly]
    simp only [Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    ring
  rw [heq] at hcoord
  exact (mul_eq_zero.mp hcoord).resolve_left
    (pow_ne_zero _ (by norm_num))



/-- Algebraic exclusion of a full-contact even-order certificate when its
frequency atoms are already distinct. -/
theorem paperNoFullEvenDistinctCertificate
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) (hk : 0 < k)
    (d : ι → ℕ → ℝ) (w t : ι → ℝ)
    (x : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hcard : s.card = 2*k)
    (htinj : Set.InjOn t s)
    (htpos : ∀ i ∈ s, 0 < t i)
    (hwpos : ∀ i ∈ s, 0 < w i)
    (hmonic : ∀ i ∈ s, d i 0 = 1)
    (hstable : ∀ i ∈ s,
      paperPolynomialHurwitz
        (paperDescendingDenominator (2*k) (d i)))
    (hPstable : paperPolynomialHurwitz
      (paperDescendingNumerator (2*k) x +
        Polynomial.C ε * Polynomial.X^(2*k)))
    (hbalance : ∀ r : Fin (2*k),
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial (2*k) (d i)
          (paperFiniteNumeratorCoeffs (2*k)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0)
    (hcontact : ∀ i ∈ s,
      (paperRaisedCrossPolynomial (2*k) (d i) x ε).eval (t i) = 0) :
    False := by
  let n := 2*k
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let E := paperAxisEven n P
  let O := paperAxisOdd n P
  let z : ι → ℝ := fun i =>
    w i * (paperAxisEven n
      (paperDescendingDenominator n (d i))).eval (t i)
  let y : ι → ℝ := fun i =>
    w i * t i * (paperAxisOdd n
      (paperDescendingDenominator n (d i))).eval (t i)
  have hn : 0 < n := by dsimp [n]; omega
  have hpdegree : P.natDegree = n := by
    exact paperDescendingNumerator_raise_natDegree_eq n x ε hε
  have hEbound : E.natDegree ≤ k := by
    simpa [E, n] using
      paperAxisEven_natDegree_le n P hpdegree.le
  have hEcoeff : E.coeff k = ε * (-1 : ℝ)^k := by
    have hPtop : P.coeff n = ε := by
      dsimp [P]
      rw [Polynomial.coeff_add, paperDescendingNumerator_coeff,
        if_neg (by omega : ¬ n < n),
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_pos rfl]
      ring
    change (paperAxisEven n P).coeff k = ε * (-1 : ℝ)^k
    rw [paperAxisEven_coeff, if_pos (by dsimp [n]; omega),
      show 2*k = n by rfl, hPtop]
  have hEcoe : E.coeff k ≠ 0 :=
    hEcoeff.symm ▸
      mul_ne_zero (ne_of_gt hε) (pow_ne_zero _ (by norm_num))
  have hEnat : E.natDegree = k :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      hEbound hEcoe
  have hEdegree : E.degree = (k : WithBot ℕ) := by
    have hEne : E ≠ 0 := by
      intro he
      simp [he] at hEcoe
    rw [Polynomial.degree_eq_natDegree hEne, hEnat]
  have hObound : O.natDegree ≤ k := by
    have h := paperAxisOdd_natDegree_le n P hpdegree.le
    change O.natDegree ≤ (n-1)/2 at h
    have hdiv : (n-1)/2 ≤ k := by dsimp [n]; omega
    exact h.trans hdiv
  have hOdegree : O.degree ≤ (k : WithBot ℕ) := by
    by_cases hOzero : O = 0
    · simp [hOzero]
    · rw [Polynomial.degree_eq_natDegree hOzero]
      exact_mod_cast hObound
  have hcop : IsCoprime E O := by
    exact paperAxisEvenOdd_coprime n P hpdegree.le hPstable
  have hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0 := by
    intro j hj
    have hsmall : 2*j < n := by dsimp [n]; omega
    exact paperCoefficientBalance_even_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0 := by
    intro j hj
    have hsmall : 2*j+1 < n := by dsimp [n]; omega
    exact paperCoefficientBalance_odd_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hc : ∀ i ∈ s,
      E.eval (t i) * z i + O.eval (t i) * y i = 0 := by
    intro i hi
    have hid := paperRaisedCross_axis_identity_any
      n hn (d i) x ε (hmonic i hi) (hstable i hi)
    have hzero := hcontact i hi
    rw [hid] at hzero
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] at hzero
    calc
      E.eval (t i) * z i + O.eval (t i) * y i =
          w i * ((paperAxisEven n P).eval (t i) *
            (paperAxisEven n
              (paperDescendingDenominator n (d i))).eval (t i) +
            t i * (paperAxisOdd n P).eval (t i) *
              (paperAxisOdd n
                (paperDescendingDenominator n (d i))).eval (t i)) := by
          dsimp [E, O, z, y]
          ring
      _ = 0 := by
          rw [hzero]
          ring
  have hnode : ∃ i ∈ s, z i ≠ 0 ∨ y i ≠ 0 := by
    have hsne : s.Nonempty := by
      apply Finset.card_pos.mp
      rw [hcard]
      omega
    obtain ⟨i, hi⟩ := hsne
    refine ⟨i, hi, ?_⟩
    have hparity := paperAxisEvenOdd_no_common_nonnegative
      n (paperDescendingDenominator n (d i))
      (paperDescendingDenominator_natDegree_eq
        n (d i) (hmonic i hi)).le
      (hstable i hi) (t i) (htpos i hi).le
    rcases hparity with he | ho
    · exact Or.inl (mul_ne_zero (ne_of_gt (hwpos i hi)) he)
    · exact Or.inr (mul_ne_zero
        (mul_ne_zero (ne_of_gt (hwpos i hi))
          (ne_of_gt (htpos i hi))) ho)
  exact paperContactResidue_no_full_even_balance_of_coprime
    s t z y htinj E O k hcard hEdegree hOdegree hcop
    hz hy hc hnode



theorem PaperCriticalCertificate.no_maximal_even_distinct_atoms
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (heven : n = 2*(n/2))
    (hatoms : C.atomCount = n) : False := by
  let k := n/2
  let d : Fin C.atomCount → ℕ → ℝ :=
    fun i => if C.rightEndpoint i then b else a
  let w : Fin C.atomCount → ℝ :=
    fun i => C.weight i * (1-C.compactFrequency i)^n
  let t : Fin C.atomCount → ℝ :=
    fun i => C.compactFrequency i /
      (1-C.compactFrequency i)
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  have hk : 0 < k := by
    dsimp [k]
    omega
  have hnval : n = 2*k := heven
  have hfull : C.positiveFiniteNodes.card = n :=
    hmax.trans heven.symm
  have hε : 0 < ε :=
    C.support_leading_pos_of_full_contacts
      hn ha0 hb0 hstableA hstableB hfull
  have hindices := C.maximal_even_positiveFiniteIndices_eq_univ
    hn ha0 hb0 hstableA hstableB hmax heven
  have hcardimage : (Finset.univ.image t).card =
      (Finset.univ : Finset (Fin C.atomCount)).card := by
    have hnodes : (Finset.univ.image t).card = n := by
      simpa [PaperCriticalCertificate.positiveFiniteNodes,
        t, hindices] using hfull
    simpa [hatoms] using hnodes
  have htinj : Set.InjOn t
      (Finset.univ : Finset (Fin C.atomCount)) :=
    Finset.card_image_iff.mp hcardimage
  have hcard : (Finset.univ : Finset (Fin C.atomCount)).card =
      2*k := by
    simp [hatoms, hnval]
  have hinter := C.maximal_even_atoms_interior
    hn ha0 hb0 hstableA hstableB hmax heven
  have htpos : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      0 < t i := by
    intro i _
    exact div_pos (hinter i).1 (sub_pos.mpr (hinter i).2)
  have hwpos : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      0 < w i := by
    intro i _
    exact mul_pos (C.weight_pos i)
      (pow_pos (sub_pos.mpr (hinter i).2) n)
  have hmonic : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      d i 0 = 1 := by
    intro i _
    by_cases hi : C.rightEndpoint i
    · simp [d, hi, hb0]
    · simp [d, hi, ha0]
  have hstable : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      paperPolynomialHurwitz
        (paperDescendingDenominator (2*k) (d i)) := by
    intro i _
    rw [←hnval]
    by_cases hi : C.rightEndpoint i
    · simpa [d, hi] using hstableB
    · simpa [d, hi] using hstableA
  have hPstable : paperPolynomialHurwitz
      (paperDescendingNumerator (2*k) x +
        Polynomial.C ε * Polynomial.X^(2*k)) := by
    rw [←hnval]
    simpa [x, ε] using
      C.support_numerator_hurwitz_of_maximal_even_contacts
        hn ha0 hb0 hstableA hstableB hmax heven
  have hbalance : ∀ r : Fin (2*k),
      (∑ i ∈ Finset.univ, w i *
        (paperGeneralCrossPolynomial (2*k) (d i)
          (paperFiniteNumeratorCoeffs (2*k)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0 := by
    have hb := (C.maximal_even_ordinary_coefficient_balance
      hn ha0 hb0 hstableA hstableB hmax heven).2
    rw [←hnval]
    intro r
    simpa [d, w, t] using hb r
  have hcontact : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      (paperRaisedCrossPolynomial (2*k) (d i) x ε).eval (t i) = 0 := by
    intro i _
    rw [←hnval]
    simpa [d, x, ε, t] using
      (C.positive_contact_root_and_deriv
        i (hinter i).1 (hinter i).2).1
  exact paperNoFullEvenDistinctCertificate
    Finset.univ k hk d w t x ε hε hcard htinj
    htpos hwpos hmonic hstable hPstable hbalance hcontact



theorem paperWeightedSum_erase_duplicate
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (i j : ι)
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (w f : ι → ℝ) (hf : f i = f j) :
    (∑ l ∈ s.erase j,
      (if l = i then w i + w j else w l) * f l) =
      ∑ l ∈ s, w l * f l := by
  have hi' : i ∈ s.erase j := Finset.mem_erase.mpr ⟨hij, hi⟩
  have hsum :
      (∑ l ∈ s.erase j,
        (if l = i then w i + w j else w l) * f l) =
      (∑ l ∈ s.erase j, w l * f l) + w j * f i := by
    have hsplit (g : ι → ℝ) :
        (∑ l ∈ s.erase j, g l) =
          g i + ∑ l ∈ (s.erase j).erase i, g l := by
      calc
        (∑ l ∈ s.erase j, g l) =
            ∑ l ∈ insert i ((s.erase j).erase i), g l := by
              rw [Finset.insert_erase hi']
        _ = g i + ∑ l ∈ (s.erase j).erase i, g l := by
              rw [Finset.sum_insert
                (Finset.not_mem_erase i (s.erase j))]
    rw [hsplit, hsplit]
    have hrest :
        (∑ l ∈ (s.erase j).erase i,
          (if l = i then w i + w j else w l) * f l) =
        ∑ l ∈ (s.erase j).erase i, w l * f l := by
      apply Finset.sum_congr rfl
      intro l hl
      simp [(Finset.mem_erase.mp hl).1]
    rw [hrest]
    simp
    ring
  rw [hsum, hf]
  have hrestore : insert j (s.erase j) = s :=
    Finset.insert_erase hj
  calc
    (∑ l ∈ s.erase j, w l * f l) + w j * f j =
        ∑ l ∈ insert j (s.erase j), w l * f l := by
          rw [Finset.sum_insert (Finset.not_mem_erase j s)]
          ring
    _ = ∑ l ∈ s, w l * f l := by rw [hrestore]

theorem paperNoFullEvenOneDuplicateCertificate
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) (hk : 0 < k)
    (d : ι → ℕ → ℝ) (w t : ι → ℝ)
    (x : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hcard : s.card = 2*k+1)
    (himage : (s.image t).card = 2*k)
    (hi : ι) (hii : hi ∈ s)
    (hj : ι) (hjj : hj ∈ s)
    (hij : hi ≠ hj)
    (htie : t hi = t hj)
    (hdsame : d hi = d hj)
    (htpos : ∀ i ∈ s, 0 < t i)
    (hwpos : ∀ i ∈ s, 0 < w i)
    (hmonic : ∀ i ∈ s, d i 0 = 1)
    (hstable : ∀ i ∈ s,
      paperPolynomialHurwitz
        (paperDescendingDenominator (2*k) (d i)))
    (hPstable : paperPolynomialHurwitz
      (paperDescendingNumerator (2*k) x +
        Polynomial.C ε * Polynomial.X^(2*k)))
    (hbalance : ∀ r : Fin (2*k),
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial (2*k) (d i)
          (paperFiniteNumeratorCoeffs (2*k)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0)
    (hcontact : ∀ i ∈ s,
      (paperRaisedCrossPolynomial (2*k) (d i) x ε).eval (t i) = 0) :
    False := by
  let s' := s.erase hj
  let w' : ι → ℝ :=
    fun l => if l = hi then w hi + w hj else w l
  have himem : hi ∈ s' := Finset.mem_erase.mpr ⟨hij, hii⟩
  have hscard : s'.card = 2*k := by
    dsimp [s']
    rw [Finset.card_erase_of_mem hjj, hcard]
    omega
  have himage_eq : s'.image t = s.image t := by
    apply Finset.Subset.antisymm
    · intro r hr
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hr
      exact Finset.mem_image.mpr
        ⟨l, Finset.mem_of_mem_erase hl, rfl⟩
    · intro r hr
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hr
      by_cases hlj : l = hj
      · subst l
        exact Finset.mem_image.mpr
          ⟨hi, himem, htie⟩
      · exact Finset.mem_image.mpr
          ⟨l, Finset.mem_erase.mpr ⟨hlj, hl⟩, rfl⟩
  have htinj : Set.InjOn t s' := by
    apply Finset.card_image_iff.mp
    rw [himage_eq, himage, hscard]
  have hwpos' : ∀ i ∈ s', 0 < w' i := by
    intro l hl
    by_cases hli : l = hi
    · subst l
      simpa [w'] using add_pos
        (hwpos hi hii) (hwpos hj hjj)
    · simpa [w', hli] using
        hwpos l (Finset.mem_of_mem_erase hl)
  have hbalance' : ∀ r : Fin (2*k),
      (∑ i ∈ s', w' i *
        (paperGeneralCrossPolynomial (2*k) (d i)
          (paperFiniteNumeratorCoeffs (2*k)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0 := by
    intro r
    have hf : (paperGeneralCrossPolynomial (2*k) (d hi)
        (paperFiniteNumeratorCoeffs (2*k)
          (fun j => if r = j then 1 else 0))).eval (t hi) =
      (paperGeneralCrossPolynomial (2*k) (d hj)
        (paperFiniteNumeratorCoeffs (2*k)
          (fun j => if r = j then 1 else 0))).eval (t hj) := by
      rw [hdsame, htie]
    have heq := paperWeightedSum_erase_duplicate
      s hi hj hii hjj hij w
      (fun l => (paperGeneralCrossPolynomial (2*k) (d l)
        (paperFiniteNumeratorCoeffs (2*k)
          (fun j => if r = j then 1 else 0))).eval (t l)) hf
    exact heq.trans (hbalance r)
  exact paperNoFullEvenDistinctCertificate
    s' k hk d w' t x ε hε hscard htinj
    (fun i hi => htpos i (Finset.mem_of_mem_erase hi))
    hwpos'
    (fun i hi => hmonic i (Finset.mem_of_mem_erase hi))
    (fun i hi => hstable i (Finset.mem_of_mem_erase hi))
    hPstable hbalance'
    (fun i hi => hcontact i (Finset.mem_of_mem_erase hi))



theorem PaperCriticalCertificate.no_maximal_even_duplicate_atoms
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (heven : n = 2*(n/2))
    (hatoms : C.atomCount = n+1) : False := by
  let k := n/2
  let d : Fin C.atomCount → ℕ → ℝ :=
    fun i => if C.rightEndpoint i then b else a
  let w : Fin C.atomCount → ℝ :=
    fun i => C.weight i * (1-C.compactFrequency i)^n
  let t : Fin C.atomCount → ℝ :=
    fun i => C.compactFrequency i /
      (1-C.compactFrequency i)
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  have hk : 0 < k := by
    dsimp [k]
    omega
  have hnval : n = 2*k := heven
  have hfull : C.positiveFiniteNodes.card = n :=
    hmax.trans heven.symm
  have hε : 0 < ε :=
    C.support_leading_pos_of_full_contacts
      hn ha0 hb0 hstableA hstableB hfull
  have hindices := C.maximal_even_positiveFiniteIndices_eq_univ
    hn ha0 hb0 hstableA hstableB hmax heven
  have hcardimage : (Finset.univ.image t).card = 2*k := by
    have hnodes : (Finset.univ.image t).card = n := by
      simpa [PaperCriticalCertificate.positiveFiniteNodes,
        t, hindices] using hfull
    exact hnodes.trans hnval
  have hcard : (Finset.univ : Finset (Fin C.atomCount)).card =
      2*k+1 := by
    simp [hatoms, hnval]
  obtain ⟨i, j, hij, htie, _, hside⟩ :=
    C.maximal_even_extra_atom_duplicate
      hn ha0 hb0 hstableA hstableB hmax heven hatoms
  have hdsame : d i = d j := by simp [d, hside]
  have hinter := C.maximal_even_atoms_interior
    hn ha0 hb0 hstableA hstableB hmax heven
  have htpos : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      0 < t i := by
    intro i _
    exact div_pos (hinter i).1 (sub_pos.mpr (hinter i).2)
  have hwpos : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      0 < w i := by
    intro i _
    exact mul_pos (C.weight_pos i)
      (pow_pos (sub_pos.mpr (hinter i).2) n)
  have hmonic : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      d i 0 = 1 := by
    intro i _
    by_cases hi : C.rightEndpoint i
    · simp [d, hi, hb0]
    · simp [d, hi, ha0]
  have hstable : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      paperPolynomialHurwitz
        (paperDescendingDenominator (2*k) (d i)) := by
    intro i _
    rw [←hnval]
    by_cases hi : C.rightEndpoint i
    · simpa [d, hi] using hstableB
    · simpa [d, hi] using hstableA
  have hPstable : paperPolynomialHurwitz
      (paperDescendingNumerator (2*k) x +
        Polynomial.C ε * Polynomial.X^(2*k)) := by
    rw [←hnval]
    simpa [x, ε] using
      C.support_numerator_hurwitz_of_maximal_even_contacts
        hn ha0 hb0 hstableA hstableB hmax heven
  have hbalance : ∀ r : Fin (2*k),
      (∑ i ∈ Finset.univ, w i *
        (paperGeneralCrossPolynomial (2*k) (d i)
          (paperFiniteNumeratorCoeffs (2*k)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0 := by
    have hb := (C.maximal_even_ordinary_coefficient_balance
      hn ha0 hb0 hstableA hstableB hmax heven).2
    rw [←hnval]
    intro r
    simpa [d, w, t] using hb r
  have hcontact : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      (paperRaisedCrossPolynomial (2*k) (d i) x ε).eval (t i) = 0 := by
    intro i _
    rw [←hnval]
    simpa [d, x, ε, t] using
      (C.positive_contact_root_and_deriv
        i (hinter i).1 (hinter i).2).1
  exact paperNoFullEvenOneDuplicateCertificate
    Finset.univ k hk d w t x ε hε hcard hcardimage
    i (Finset.mem_univ i) j (Finset.mem_univ j)
    hij (by simpa [t] using htie) hdsame
    htpos hwpos hmonic hstable hPstable hbalance hcontact





/-- No maximal positive-contact certificate exists at any positive even
order. The extra Carathéodory atom is absorbed into its identical contact. -/
theorem PaperCriticalCertificate.no_maximal_even_contacts
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (heven : n = 2*(n/2)) : False := by
  have hfull : C.positiveFiniteNodes.card = n :=
    hmax.trans heven.symm
  rcases C.full_contacts_atomCount_dichotomy hfull with hatoms | hatoms
  · exact C.no_maximal_even_distinct_atoms
      hn ha0 hb0 hstableA hstableB hmax heven hatoms
  · exact C.no_maximal_even_duplicate_atoms
      hn ha0 hb0 hstableA hstableB hmax heven hatoms

/-- Even-order critical certificates have strictly fewer positive contacts
than the polynomial order. -/
theorem PaperCriticalCertificate.even_positiveFiniteNodes_card_lt_order
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (heven : n = 2*(n/2)) :
    C.positiveFiniteNodes.card < n := by
  have hle := C.positiveFiniteNodes_card_le_order
    hn ha0 hb0 hstableA hstableB
  have hne : C.positiveFiniteNodes.card ≠ n := by
    intro hcard
    exact C.no_maximal_even_contacts
      hn ha0 hb0 hstableA hstableB (hcard.trans heven) heven
  omega


theorem paperContactResidue_no_even_balance_of_coprime_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z y : ι → ℝ)
    (ht : Set.InjOn t s) (E O : Polynomial ℝ) (k : ℕ)
    (hcard : s.card ≤ 2*k)
    (hEdegree : E.degree = (k : WithBot ℕ))
    (hOdegree : O.degree ≤ k)
    (hcop : IsCoprime E O)
    (hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0)
    (hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0)
    (hc : ∀ i ∈ s, E.eval (t i) * z i +
      O.eval (t i) * y i = 0)
    (hnode : ∃ i ∈ s, z i ≠ 0 ∨ y i ≠ 0) : False := by
  let U := MonicQuinticCoeff.quinticResiduePolynomial s t z
  let V := MonicQuinticCoeff.quinticResiduePolynomial s t y
  have hEne : E ≠ 0 := by
    intro he
    simp [he] at hEdegree
  have hid : E*U+O*V=0 :=
    paperContactResiduePolynomial_identity s t z y ht E O k
      hEdegree.le hOdegree hz hy hc
  obtain ⟨M, hVM, _⟩ :=
    MonicQuinticCoeff.coprime_quintic_contact_multiplier
      hcop hEne hid
  have hVbound := MonicQuinticCoeff.degree_quinticResiduePolynomial_of_moments
    s t y k hy
  change V.degree + k < (s.card : WithBot ℕ) at hVbound
  have hVbound' : V.degree + k < (2*k : WithBot ℕ) :=
    lt_of_lt_of_le hVbound (by exact_mod_cast hcard)
  have hVzero : V = 0 := by
    by_contra hv
    have hVnat : V.natDegree + k < 2*k := by
      rw [Polynomial.degree_eq_natDegree hv] at hVbound'
      exact_mod_cast hVbound'
    have hEnat : E.natDegree = k := by
      rw [Polynomial.degree_eq_natDegree hEne] at hEdegree
      exact_mod_cast hEdegree
    have hdiv : E ∣ V := ⟨M, hVM⟩
    have hle := Polynomial.natDegree_le_of_dvd hdiv hv
    omega
  rw [hVzero, mul_zero, add_zero] at hid
  have hUzero : U = 0 :=
    (mul_eq_zero.mp hid).resolve_left hEne
  exact (paperContactResidue_nontrivial s t z y ht hnode).elim
    (fun h => h hUzero) (fun h => h hVzero)

/-- The same obstruction when the odd parity polynomial has top degree. -/
theorem paperContactResidue_no_odd_balance_of_coprime_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z y : ι → ℝ)
    (ht : Set.InjOn t s) (E O : Polynomial ℝ) (k : ℕ)
    (hcard : s.card ≤ 2*k)
    (hEdegree : E.degree ≤ k)
    (hOdegree : O.degree = (k : WithBot ℕ))
    (hcop : IsCoprime E O)
    (hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0)
    (hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0)
    (hc : ∀ i ∈ s, E.eval (t i) * z i +
      O.eval (t i) * y i = 0)
    (hnode : ∃ i ∈ s, z i ≠ 0 ∨ y i ≠ 0) : False := by
  have hcop' : IsCoprime O E := hcop.symm
  apply paperContactResidue_no_even_balance_of_coprime_le
    s t y z ht O E k hcard hOdegree hEdegree hcop' hy hz
  · intro i hi
    simpa [add_comm] using hc i hi
  · obtain ⟨i, hi, h⟩ := hnode
    exact ⟨i, hi, h.symm⟩



theorem paperNoEvenDistinctCertificate_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) (hk : 0 < k)
    (d : ι → ℕ → ℝ) (w t : ι → ℝ)
    (x : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hcard : s.card ≤ 2*k)
    (hsne : s.Nonempty)
    (htinj : Set.InjOn t s)
    (htpos : ∀ i ∈ s, 0 < t i)
    (hwpos : ∀ i ∈ s, 0 < w i)
    (hmonic : ∀ i ∈ s, d i 0 = 1)
    (hstable : ∀ i ∈ s,
      paperPolynomialHurwitz
        (paperDescendingDenominator (2*k) (d i)))
    (hPstable : paperPolynomialHurwitz
      (paperDescendingNumerator (2*k) x +
        Polynomial.C ε * Polynomial.X^(2*k)))
    (hbalance : ∀ r : Fin (2*k),
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial (2*k) (d i)
          (paperFiniteNumeratorCoeffs (2*k)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0)
    (hcontact : ∀ i ∈ s,
      (paperRaisedCrossPolynomial (2*k) (d i) x ε).eval (t i) = 0) :
    False := by
  let n := 2*k
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let E := paperAxisEven n P
  let O := paperAxisOdd n P
  let z : ι → ℝ := fun i =>
    w i * (paperAxisEven n
      (paperDescendingDenominator n (d i))).eval (t i)
  let y : ι → ℝ := fun i =>
    w i * t i * (paperAxisOdd n
      (paperDescendingDenominator n (d i))).eval (t i)
  have hn : 0 < n := by dsimp [n]; omega
  have hpdegree : P.natDegree = n := by
    exact paperDescendingNumerator_raise_natDegree_eq n x ε hε
  have hEbound : E.natDegree ≤ k := by
    simpa [E, n] using
      paperAxisEven_natDegree_le n P hpdegree.le
  have hEcoeff : E.coeff k = ε * (-1 : ℝ)^k := by
    have hPtop : P.coeff n = ε := by
      dsimp [P]
      rw [Polynomial.coeff_add, paperDescendingNumerator_coeff,
        if_neg (by omega : ¬ n < n),
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_pos rfl]
      ring
    change (paperAxisEven n P).coeff k = ε * (-1 : ℝ)^k
    rw [paperAxisEven_coeff, if_pos (by dsimp [n]; omega),
      show 2*k = n by rfl, hPtop]
  have hEcoe : E.coeff k ≠ 0 :=
    hEcoeff.symm ▸
      mul_ne_zero (ne_of_gt hε) (pow_ne_zero _ (by norm_num))
  have hEnat : E.natDegree = k :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      hEbound hEcoe
  have hEdegree : E.degree = (k : WithBot ℕ) := by
    have hEne : E ≠ 0 := by
      intro he
      simp [he] at hEcoe
    rw [Polynomial.degree_eq_natDegree hEne, hEnat]
  have hObound : O.natDegree ≤ k := by
    have h := paperAxisOdd_natDegree_le n P hpdegree.le
    change O.natDegree ≤ (n-1)/2 at h
    have hdiv : (n-1)/2 ≤ k := by dsimp [n]; omega
    exact h.trans hdiv
  have hOdegree : O.degree ≤ (k : WithBot ℕ) := by
    by_cases hOzero : O = 0
    · simp [hOzero]
    · rw [Polynomial.degree_eq_natDegree hOzero]
      exact_mod_cast hObound
  have hcop : IsCoprime E O := by
    exact paperAxisEvenOdd_coprime n P hpdegree.le hPstable
  have hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0 := by
    intro j hj
    have hsmall : 2*j < n := by dsimp [n]; omega
    exact paperCoefficientBalance_even_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0 := by
    intro j hj
    have hsmall : 2*j+1 < n := by dsimp [n]; omega
    exact paperCoefficientBalance_odd_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hc : ∀ i ∈ s,
      E.eval (t i) * z i + O.eval (t i) * y i = 0 := by
    intro i hi
    have hid := paperRaisedCross_axis_identity_any
      n hn (d i) x ε (hmonic i hi) (hstable i hi)
    have hzero := hcontact i hi
    rw [hid] at hzero
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] at hzero
    calc
      E.eval (t i) * z i + O.eval (t i) * y i =
          w i * ((paperAxisEven n P).eval (t i) *
            (paperAxisEven n
              (paperDescendingDenominator n (d i))).eval (t i) +
            t i * (paperAxisOdd n P).eval (t i) *
              (paperAxisOdd n
                (paperDescendingDenominator n (d i))).eval (t i)) := by
          dsimp [E, O, z, y]
          ring
      _ = 0 := by
          rw [hzero]
          ring
  have hnode : ∃ i ∈ s, z i ≠ 0 ∨ y i ≠ 0 := by
    obtain ⟨i, hi⟩ := hsne
    refine ⟨i, hi, ?_⟩
    have hparity := paperAxisEvenOdd_no_common_nonnegative
      n (paperDescendingDenominator n (d i))
      (paperDescendingDenominator_natDegree_eq
        n (d i) (hmonic i hi)).le
      (hstable i hi) (t i) (htpos i hi).le
    rcases hparity with he | ho
    · exact Or.inl (mul_ne_zero (ne_of_gt (hwpos i hi)) he)
    · exact Or.inr (mul_ne_zero
        (mul_ne_zero (ne_of_gt (hwpos i hi))
          (ne_of_gt (htpos i hi))) ho)
  exact paperContactResidue_no_even_balance_of_coprime_le
    s t z y htinj E O k hcard hEdegree hOdegree hcop
    hz hy hc hnode





theorem paperNoOddDistinctCertificate_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) (hk : 0 < k)
    (d : ι → ℕ → ℝ) (w t : ι → ℝ)
    (x : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hcard : s.card ≤ 2*k)
    (hsne : s.Nonempty)
    (htinj : Set.InjOn t s)
    (htpos : ∀ i ∈ s, 0 < t i)
    (hwpos : ∀ i ∈ s, 0 < w i)
    (hmonic : ∀ i ∈ s, d i 0 = 1)
    (hstable : ∀ i ∈ s,
      paperPolynomialHurwitz
        (paperDescendingDenominator (2*k+1) (d i)))
    (hPstable : paperPolynomialHurwitz
      (paperDescendingNumerator (2*k+1) x +
        Polynomial.C ε * Polynomial.X^(2*k+1)))
    (hbalance : ∀ r : Fin (2*k+1),
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial (2*k+1) (d i)
          (paperFiniteNumeratorCoeffs (2*k+1)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0)
    (hcontact : ∀ i ∈ s,
      (paperRaisedCrossPolynomial (2*k+1) (d i) x ε).eval (t i) = 0) :
    False := by
  let n := 2*k+1
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let E := paperAxisEven n P
  let O := paperAxisOdd n P
  let z : ι → ℝ := fun i =>
    w i * (paperAxisEven n
      (paperDescendingDenominator n (d i))).eval (t i)
  let y : ι → ℝ := fun i =>
    w i * t i * (paperAxisOdd n
      (paperDescendingDenominator n (d i))).eval (t i)
  have hn : 0 < n := by dsimp [n]; omega
  have hpdegree : P.natDegree = n := by
    exact paperDescendingNumerator_raise_natDegree_eq n x ε hε
  have hEbound : E.natDegree ≤ k := by
    have h := paperAxisEven_natDegree_le n P hpdegree.le
    change E.natDegree ≤ n/2 at h
    have hdiv : n/2 ≤ k := by dsimp [n]; omega
    exact h.trans hdiv
  have hEdegree : E.degree ≤ (k : WithBot ℕ) := by
    by_cases hEzero : E = 0
    · simp [hEzero]
    · rw [Polynomial.degree_eq_natDegree hEzero]
      exact_mod_cast hEbound
  have hObound : O.natDegree ≤ k := by
    have h := paperAxisOdd_natDegree_le n P hpdegree.le
    change O.natDegree ≤ (n-1)/2 at h
    have hdiv : (n-1)/2 ≤ k := by dsimp [n]; omega
    exact h.trans hdiv
  have hOcoeff : O.coeff k = ε * (-1 : ℝ)^k := by
    have hPtop : P.coeff n = ε := by
      dsimp [P]
      rw [Polynomial.coeff_add, paperDescendingNumerator_coeff,
        if_neg (by omega : ¬ n < n),
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_pos rfl]
      ring
    change (paperAxisOdd n P).coeff k = ε * (-1 : ℝ)^k
    rw [paperAxisOdd_coeff, if_pos (by dsimp [n]; omega),
      show 2*k+1 = n by rfl, hPtop]
  have hOcoe : O.coeff k ≠ 0 := by
    rw [hOcoeff]
    exact mul_ne_zero (ne_of_gt hε) (pow_ne_zero _ (by norm_num))
  have hOnat : O.natDegree = k :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      hObound hOcoe
  have hOdegree : O.degree = (k : WithBot ℕ) := by
    have hOne : O ≠ 0 := by
      intro he
      simp [he] at hOcoe
    rw [Polynomial.degree_eq_natDegree hOne, hOnat]
  have hcop : IsCoprime E O := by
    exact paperAxisEvenOdd_coprime n P hpdegree.le hPstable
  have hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0 := by
    intro j hj
    have hsmall : 2*j < n := by dsimp [n]; omega
    exact paperCoefficientBalance_even_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0 := by
    intro j hj
    have hsmall : 2*j+1 < n := by dsimp [n]; omega
    exact paperCoefficientBalance_odd_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hc : ∀ i ∈ s,
      E.eval (t i) * z i + O.eval (t i) * y i = 0 := by
    intro i hi
    have hid := paperRaisedCross_axis_identity_any
      n hn (d i) x ε (hmonic i hi) (hstable i hi)
    have hzero := hcontact i hi
    rw [hid] at hzero
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] at hzero
    calc
      E.eval (t i) * z i + O.eval (t i) * y i =
          w i * ((paperAxisEven n P).eval (t i) *
            (paperAxisEven n
              (paperDescendingDenominator n (d i))).eval (t i) +
            t i * (paperAxisOdd n P).eval (t i) *
              (paperAxisOdd n
                (paperDescendingDenominator n (d i))).eval (t i)) := by
          dsimp [E, O, z, y]
          ring
      _ = 0 := by
          rw [hzero]
          ring
  have hnode : ∃ i ∈ s, z i ≠ 0 ∨ y i ≠ 0 := by
    obtain ⟨i, hi⟩ := hsne
    refine ⟨i, hi, ?_⟩
    have hparity := paperAxisEvenOdd_no_common_nonnegative
      n (paperDescendingDenominator n (d i))
      (paperDescendingDenominator_natDegree_eq
        n (d i) (hmonic i hi)).le
      (hstable i hi) (t i) (htpos i hi).le
    rcases hparity with he | ho
    · exact Or.inl (mul_ne_zero (ne_of_gt (hwpos i hi)) he)
    · exact Or.inr (mul_ne_zero
        (mul_ne_zero (ne_of_gt (hwpos i hi))
          (ne_of_gt (htpos i hi))) ho)
  exact paperContactResidue_no_odd_balance_of_coprime_le
    s t z y htinj E O k hcard hEdegree hOdegree hcop
    hz hy hc hnode






noncomputable def paperGroupedResidue
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t f : ι → ℝ) (r : ℝ) : ℝ :=
  ∑ i ∈ s.filter (fun i => t i = r), f i

theorem paperGroupedResidue_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t f : ι → ℝ) :
    (∑ r ∈ s.image t,
      paperGroupedResidue s t f r) =
      ∑ i ∈ s, f i := by
  classical
  have h := Finset.sum_fiberwise_eq_sum_filter
    s (s.image t) t f
  have hfilter : s.filter (fun i => t i ∈ s.image t) = s := by
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  rw [hfilter] at h
  simpa only [paperGroupedResidue] using h

theorem paperGroupedResidue_moment
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t f : ι → ℝ) (j : ℕ) :
    (∑ r ∈ s.image t,
      r^j * paperGroupedResidue s t f r) =
      ∑ i ∈ s, (t i)^j * f i := by
  classical
  rw [←paperGroupedResidue_sum s t
    (fun i => (t i)^j * f i)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [paperGroupedResidue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hti : t i = r := (Finset.mem_filter.mp hi).2
  change r^j * f i = (t i)^j * f i
  rw [hti]

theorem paperGroupedResidue_contact
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z y : ι → ℝ)
    (E O : Polynomial ℝ)
    (hc : ∀ i ∈ s,
      E.eval (t i) * z i + O.eval (t i) * y i = 0)
    (r : ℝ) :
    E.eval r * paperGroupedResidue s t z r +
      O.eval r * paperGroupedResidue s t y r = 0 := by
  classical
  simp only [paperGroupedResidue,
    Finset.mul_sum, ←Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i hi
  have hmem : i ∈ s := (Finset.mem_filter.mp hi).1
  have hti : t i = r := (Finset.mem_filter.mp hi).2
  simpa [hti] using hc i hmem

theorem paperContactResidue_no_grouped_even_balance
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z y : ι → ℝ)
    (E O : Polynomial ℝ) (k : ℕ)
    (hcard : (s.image t).card ≤ 2*k)
    (hEdegree : E.degree = (k : WithBot ℕ))
    (hOdegree : O.degree ≤ k)
    (hcop : IsCoprime E O)
    (hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0)
    (hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0)
    (hc : ∀ i ∈ s, E.eval (t i) * z i +
      O.eval (t i) * y i = 0)
    (hnode : ∃ r ∈ s.image t,
      paperGroupedResidue s t z r ≠ 0 ∨
        paperGroupedResidue s t y r ≠ 0) : False := by
  classical
  let u : ℝ → ℝ := paperGroupedResidue s t z
  let v : ℝ → ℝ := paperGroupedResidue s t y
  apply paperContactResidue_no_even_balance_of_coprime_le
    (s.image t) id u v
    (by intro r _ q _ h; exact h)
    E O k hcard hEdegree hOdegree hcop
  · intro j hj
    simpa [u] using
      (paperGroupedResidue_moment s t z j).trans (hz j hj)
  · intro j hj
    simpa [v] using
      (paperGroupedResidue_moment s t y j).trans (hy j hj)
  · intro r hr
    exact paperGroupedResidue_contact s t z y E O hc r
  · exact hnode

theorem paperContactResidue_no_grouped_odd_balance
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z y : ι → ℝ)
    (E O : Polynomial ℝ) (k : ℕ)
    (hcard : (s.image t).card ≤ 2*k)
    (hEdegree : E.degree ≤ k)
    (hOdegree : O.degree = (k : WithBot ℕ))
    (hcop : IsCoprime E O)
    (hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0)
    (hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0)
    (hc : ∀ i ∈ s, E.eval (t i) * z i +
      O.eval (t i) * y i = 0)
    (hnode : ∃ r ∈ s.image t,
      paperGroupedResidue s t z r ≠ 0 ∨
        paperGroupedResidue s t y r ≠ 0) : False := by
  classical
  let u : ℝ → ℝ := paperGroupedResidue s t z
  let v : ℝ → ℝ := paperGroupedResidue s t y
  apply paperContactResidue_no_odd_balance_of_coprime_le
    (s.image t) id u v
    (by intro r _ q _ h; exact h)
    E O k hcard hEdegree hOdegree hcop
  · intro j hj
    simpa [u] using
      (paperGroupedResidue_moment s t z j).trans (hz j hj)
  · intro j hj
    simpa [v] using
      (paperGroupedResidue_moment s t y j).trans (hy j hj)
  · intro r hr
    exact paperGroupedResidue_contact s t z y E O hc r
  · exact hnode



theorem paperComplexPositiveCombination_ne_zero
    (A B : ℂ) (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hsum : 0 < u+v)
    (hseg : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      ((1-r : ℝ) : ℂ)*A + (r : ℂ)*B ≠ 0) :
    (u : ℂ)*A + (v : ℂ)*B ≠ 0 := by
  let r := v/(u+v)
  have hr0 : 0 ≤ r := div_nonneg hv hsum.le
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact (div_le_one hsum).mpr (by linarith)
  have hden : u+v ≠ 0 := ne_of_gt hsum
  have hu' : (1-r)*(u+v) = u := by
    dsimp [r]
    field_simp
  have hv' : r*(u+v) = v := by
    dsimp [r]
    field_simp
  have hfactor :
      (((u+v : ℝ) : ℂ) *
        (((1-r : ℝ) : ℂ)*A + (r : ℂ)*B)) =
      (u : ℂ)*A + (v : ℂ)*B := by
    calc
      _ = (((1-r)*(u+v) : ℝ) : ℂ)*A +
          ((r*(u+v) : ℝ) : ℂ)*B := by
            push_cast
            ring
      _ = (u : ℂ)*A + (v : ℂ)*B := by rw [hu', hv']
  intro hzero
  have hdenC : (((u+v : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hden
  exact (hseg r hr0 hr1)
    ((mul_eq_zero.mp (hfactor.trans hzero)).resolve_left hdenC)

theorem paperWeightedTwoSide_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℝ) (side : ι → Bool)
    (A B : ℂ) :
    (∑ i ∈ s, (w i : ℂ) * (if side i then B else A)) =
      ((∑ i ∈ s, if side i then 0 else w i : ℝ) : ℂ)*A +
        ((∑ i ∈ s, if side i then w i else 0 : ℝ) : ℂ)*B := by
  have hterm (i : ι) :
      (w i : ℂ) * (if side i then B else A) =
        ((if side i then 0 else w i : ℝ) : ℂ)*A +
          ((if side i then w i else 0 : ℝ) : ℂ)*B := by
    cases h : side i <;> simp [h]
  conv_lhs => arg 2; ext i; rw [hterm i]
  rw [Finset.sum_add_distrib]
  simp only [←Finset.sum_mul]
  push_cast
  rfl

theorem paperWeightedDenominatorFiber_ne_zero
    {ι : Type*} [DecidableEq ι]
    (n : ℕ) (a b : ℕ → ℝ)
    (s : Finset ι) (t w : ι → ℝ) (side : ι → Bool)
    (hw : ∀ i ∈ s, 0 < w i)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (r : ℝ) (hr : r ∈ s.image t) (ω : ℝ) :
    (∑ i ∈ s.filter (fun i => t i = r),
      (w i : ℂ) *
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n
            (if side i then b else a))) ≠ 0 := by
  classical
  let s' := s.filter (fun i => t i = r)
  let u : ℝ := ∑ i ∈ s', if side i then 0 else w i
  let v : ℝ := ∑ i ∈ s', if side i then w i else 0
  let A : ℂ := Polynomial.aeval (jw ω)
    (paperDescendingDenominator n a)
  let B : ℂ := Polynomial.aeval (jw ω)
    (paperDescendingDenominator n b)
  have hu : 0 ≤ u := by
    apply Finset.sum_nonneg
    intro i hi
    by_cases h : side i
    · simp [h]
    · simpa [h] using (hw i (Finset.mem_filter.mp hi).1).le
  have hv : 0 ≤ v := by
    apply Finset.sum_nonneg
    intro i hi
    by_cases h : side i
    · simpa [h] using (hw i (Finset.mem_filter.mp hi).1).le
    · simp [h]
  have hplus : u+v = ∑ i ∈ s', w i := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : side i <;> simp [h]
  have hs'ne : s'.Nonempty := by
    obtain ⟨i, hi, hit⟩ := Finset.mem_image.mp hr
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hit⟩⟩
  have hsumpos : 0 < u+v := by
    rw [hplus]
    exact Finset.sum_pos
      (fun i hi => hw i (Finset.mem_filter.mp hi).1) hs'ne
  have hseg : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      ((1-q : ℝ) : ℂ)*A + (q : ℂ)*B ≠ 0 := by
    intro q hq0 hq1
    rw [←paperSegmentDenominator_eval_affine]
    exact paperPolynomialHurwitz_imag_ne_zero
      _ (hsegment q hq0 hq1) ω
  have hcombo : (u : ℂ)*A + (v : ℂ)*B ≠ 0 :=
    paperComplexPositiveCombination_ne_zero
      A B u v hu hv hsumpos hseg
  have hsum :
      (∑ i ∈ s',
        (w i : ℂ) *
          Polynomial.aeval (jw ω)
            (paperDescendingDenominator n
              (if side i then b else a))) =
        (u : ℂ)*A + (v : ℂ)*B := by
    calc
      _ = ∑ i ∈ s', (w i : ℂ) * (if side i then B else A) := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases h : side i <;> simp [h, A, B]
      _ = (u : ℂ)*A + (v : ℂ)*B :=
            paperWeightedTwoSide_sum s' w side A B
  exact hsum ▸ hcombo

theorem paperAxisComplex_eval
    (n : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ n) (ω : ℝ) :
    Polynomial.aeval (jw ω) p =
      ((Polynomial.eval (ω^2) (paperAxisEven n p) : ℝ) : ℂ) +
        (jw ω) *
          ((Polynomial.eval (ω^2) (paperAxisOdd n p) : ℝ) : ℂ) := by
  apply Complex.ext
  · have h := paperAxisEven_eval n p hp ω
    simp only [Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, add_zero] 
    simp [jw]
    exact h
  · have h := paperAxisOdd_eval n p hp ω
    simp [jw, Complex.add_im, Complex.mul_im] at *
    exact h

theorem paperGroupedAxisResidue_nontrivial
    {ι : Type*} [DecidableEq ι]
    (n : ℕ) (a b : ℕ → ℝ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (s : Finset ι) (t w : ι → ℝ) (side : ι → Bool)
    (htpos : ∀ i ∈ s, 0 < t i)
    (hwpos : ∀ i ∈ s, 0 < w i)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (r : ℝ) (hr : r ∈ s.image t) :
    paperGroupedResidue s t
      (fun i => w i * (paperAxisEven n
        (paperDescendingDenominator n
          (if side i then b else a))).eval (t i)) r ≠ 0 ∨
    paperGroupedResidue s t
      (fun i => w i * t i * (paperAxisOdd n
        (paperDescendingDenominator n
          (if side i then b else a))).eval (t i)) r ≠ 0 := by
  classical
  let d : ι → Polynomial ℝ := fun i =>
    paperDescendingDenominator n (if side i then b else a)
  let s' := s.filter (fun i => t i = r)
  let Z : ℝ := paperGroupedResidue s t
    (fun i => w i * (paperAxisEven n (d i)).eval (t i)) r
  let Y : ℝ := paperGroupedResidue s t
    (fun i => w i * t i *
      (paperAxisOdd n (d i)).eval (t i)) r
  let T : ℝ := ∑ i ∈ s', w i * (paperAxisOdd n (d i)).eval r
  obtain ⟨j, hj, hjr⟩ := Finset.mem_image.mp hr
  have hrpos : 0 < r := hjr ▸ htpos j hj
  let ω := Real.sqrt r
  have hω : ω^2 = r := Real.sq_sqrt hrpos.le
  have hddegree (i : ι) : (d i).natDegree ≤ n := by
    by_cases h : side i
    · simpa [d, h] using
        (paperDescendingDenominator_natDegree_eq n b hb0).le
    · simpa [d, h] using
        (paperDescendingDenominator_natDegree_eq n a ha0).le
  have hY : Y = r*T := by
    dsimp [Y, T, paperGroupedResidue]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hti : t i = r := (Finset.mem_filter.mp hi).2
    rw [hti]
    ring
  let S : ℂ := ∑ i ∈ s', (w i : ℂ) *
    Polynomial.aeval (jw ω) (d i)
  have hSre : S.re = Z := by
    dsimp [S, Z, paperGroupedResidue]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hti : t i = r := (Finset.mem_filter.mp hi).2
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rw [paperAxisEven_eval n (d i) (hddegree i) ω,
      hω, hti]
  have hSim : S.im = ω*T := by
    dsimp [S, T]
    rw [Complex.im_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    rw [paperAxisOdd_eval n (d i) (hddegree i) ω, hω]
    ring
  have hSnonzero : S ≠ 0 := by
    exact paperWeightedDenominatorFiber_ne_zero
      n a b s t w side hwpos hsegment r hr ω
  by_contra h
  push_neg at h
  change Z = 0 ∧ Y = 0 at h
  have hTzero : T = 0 := by
    rw [h.2] at hY
    exact (mul_eq_zero.mp hY.symm).resolve_left (ne_of_gt hrpos)
  have hSzero : S = 0 := by
    apply Complex.ext
    · simpa [Z, h.1] using hSre
    · simpa [hTzero] using hSim
  exact hSnonzero hSzero



theorem PaperCriticalCertificate.ordinary_balance_of_atoms_interior
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b)
    (hinter : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1) :
    (∀ i : Fin C.atomCount,
      0 < C.weight i * (1-C.compactFrequency i)^n) ∧
    (∑ i : Fin C.atomCount,
      (C.weight i * (1-C.compactFrequency i)^n) •
        paperOrdinaryFeature n
          (if C.rightEndpoint i then b else a)
          (C.compactFrequency i /
            (1-C.compactFrequency i))) = 0 := by
  constructor
  · intro i
    exact mul_pos (C.weight_pos i)
      (pow_pos (sub_pos.mpr (hinter i).2) n)
  · calc
      _ = ∑ i : Fin C.atomCount,
          C.weight i •
            paperCompactFeature n
              (if C.rightEndpoint i then b else a)
              (C.compactFrequency i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [paperCompactFeature_eq_scaledOrdinary
          n _ _ (ne_of_lt (hinter i).2)]
        simp only [smul_smul, smul_eq_mul]
      _ = 0 := C.balance

/-- The decompactified balance, resolved into the leading coefficient and
all finite numerator coefficient directions. -/
theorem PaperCriticalCertificate.ordinary_coefficient_balance_of_atoms_interior
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b)
    (hinter : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1) :
    (∑ i : Fin C.atomCount,
      C.weight i * (1-C.compactFrequency i)^n *
        (paperRaiseCorrection n
          (if C.rightEndpoint i then b else a)).eval
            (C.compactFrequency i /
              (1-C.compactFrequency i))) = 0 ∧
    (∀ j : Fin n,
      (∑ i : Fin C.atomCount,
        C.weight i * (1-C.compactFrequency i)^n *
          (paperGeneralCrossPolynomial n
            (if C.rightEndpoint i then b else a)
            (paperFiniteNumeratorCoeffs n
              (fun k => if j = k then 1 else 0))).eval
                (C.compactFrequency i /
                  (1-C.compactFrequency i))) = 0) := by
  have hbalance := (C.ordinary_balance_of_atoms_interior hinter).2
  have hcoord (j : Fin (n+1)) :
      (∑ i : Fin C.atomCount,
        C.weight i * (1-C.compactFrequency i)^n *
          paperOrdinaryFeature n
            (if C.rightEndpoint i then b else a)
            (C.compactFrequency i /
              (1-C.compactFrequency i)) j) = 0 := by
    have h := congrArg (fun v : Fin (n+1) → ℝ => v j) hbalance
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] using h
  constructor
  · simpa [paperOrdinaryFeature] using hcoord 0
  · intro j
    simpa [paperOrdinaryFeature] using hcoord j.succ






theorem paperNoEvenGroupedCertificate_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) (hk : 0 < k)
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (side : ι → Bool) (w t : ι → ℝ)
    (x : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hcard : (s.image t).card ≤ 2*k)
    (hsne : s.Nonempty)
    (htpos : ∀ i ∈ s, 0 < t i)
    (hwpos : ∀ i ∈ s, 0 < w i)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k) a b q))
    (hPstable : paperPolynomialHurwitz
      (paperDescendingNumerator (2*k) x +
        Polynomial.C ε * Polynomial.X^(2*k)))
    (hbalance : ∀ r : Fin (2*k),
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial (2*k)
          (if side i then b else a)
          (paperFiniteNumeratorCoeffs (2*k)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0)
    (hcontact : ∀ i ∈ s,
      (paperRaisedCrossPolynomial (2*k)
        (if side i then b else a) x ε).eval (t i) = 0) :
    False := by
  let n := 2*k
  let d : ι → ℕ → ℝ := fun i =>
    if side i then b else a
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let E := paperAxisEven n P
  let O := paperAxisOdd n P
  let z : ι → ℝ := fun i =>
    w i * (paperAxisEven n
      (paperDescendingDenominator n (d i))).eval (t i)
  let y : ι → ℝ := fun i =>
    w i * t i * (paperAxisOdd n
      (paperDescendingDenominator n (d i))).eval (t i)
  have hn : 0 < n := by dsimp [n]; omega
  have hmonic : ∀ i ∈ s, d i 0 = 1 := by
    intro i hi
    by_cases h : side i
    · simp [d, h, hb0]
    · simp [d, h, ha0]
  have hstable : ∀ i ∈ s,
      paperPolynomialHurwitz
        (paperDescendingDenominator n (d i)) := by
    intro i hi
    by_cases h : side i
    · simpa [d, h, paperSegmentDenominator] using
        (hsegment 1 (by norm_num) (by norm_num))
    · simpa [d, h, paperSegmentDenominator] using
        (hsegment 0 (by norm_num) (by norm_num))
  have hpdegree : P.natDegree = n := by
    exact paperDescendingNumerator_raise_natDegree_eq n x ε hε
  have hEbound : E.natDegree ≤ k := by
    simpa [E, n] using
      paperAxisEven_natDegree_le n P hpdegree.le
  have hEcoeff : E.coeff k = ε * (-1 : ℝ)^k := by
    have hPtop : P.coeff n = ε := by
      dsimp [P]
      rw [Polynomial.coeff_add, paperDescendingNumerator_coeff,
        if_neg (by omega : ¬ n < n),
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_pos rfl]
      ring
    change (paperAxisEven n P).coeff k = ε * (-1 : ℝ)^k
    rw [paperAxisEven_coeff, if_pos (by dsimp [n]; omega),
      show 2*k = n by rfl, hPtop]
  have hEcoe : E.coeff k ≠ 0 :=
    hEcoeff.symm ▸
      mul_ne_zero (ne_of_gt hε) (pow_ne_zero _ (by norm_num))
  have hEnat : E.natDegree = k :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      hEbound hEcoe
  have hEdegree : E.degree = (k : WithBot ℕ) := by
    have hEne : E ≠ 0 := by
      intro he
      simp [he] at hEcoe
    rw [Polynomial.degree_eq_natDegree hEne, hEnat]
  have hObound : O.natDegree ≤ k := by
    have h := paperAxisOdd_natDegree_le n P hpdegree.le
    change O.natDegree ≤ (n-1)/2 at h
    have hdiv : (n-1)/2 ≤ k := by dsimp [n]; omega
    exact h.trans hdiv
  have hOdegree : O.degree ≤ (k : WithBot ℕ) := by
    by_cases hOzero : O = 0
    · simp [hOzero]
    · rw [Polynomial.degree_eq_natDegree hOzero]
      exact_mod_cast hObound
  have hcop : IsCoprime E O := by
    exact paperAxisEvenOdd_coprime n P hpdegree.le hPstable
  have hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0 := by
    intro j hj
    have hsmall : 2*j < n := by dsimp [n]; omega
    exact paperCoefficientBalance_even_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0 := by
    intro j hj
    have hsmall : 2*j+1 < n := by dsimp [n]; omega
    exact paperCoefficientBalance_odd_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hc : ∀ i ∈ s,
      E.eval (t i) * z i + O.eval (t i) * y i = 0 := by
    intro i hi
    have hid := paperRaisedCross_axis_identity_any
      n hn (d i) x ε (hmonic i hi) (hstable i hi)
    have hzero := hcontact i hi
    rw [hid] at hzero
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] at hzero
    calc
      E.eval (t i) * z i + O.eval (t i) * y i =
          w i * ((paperAxisEven n P).eval (t i) *
            (paperAxisEven n
              (paperDescendingDenominator n (d i))).eval (t i) +
            t i * (paperAxisOdd n P).eval (t i) *
              (paperAxisOdd n
                (paperDescendingDenominator n (d i))).eval (t i)) := by
          dsimp [E, O, z, y]
          ring
      _ = 0 := by
          rw [hzero]
          ring
  have hnode : ∃ r ∈ s.image t,
      paperGroupedResidue s t z r ≠ 0 ∨
        paperGroupedResidue s t y r ≠ 0 := by
    obtain ⟨i, hi⟩ := hsne
    have hr : t i ∈ s.image t :=
      Finset.mem_image.mpr ⟨i, hi, rfl⟩
    refine ⟨t i, hr, ?_⟩
    simpa [z, y, d] using
      (paperGroupedAxisResidue_nontrivial
        n a b ha0 hb0 s t w side htpos hwpos
        hsegment (t i) hr)
  exact paperContactResidue_no_grouped_even_balance
    s t z y E O k hcard hEdegree hOdegree hcop
    hz hy hc hnode









theorem paperNoOddGroupedCertificate_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) (hk : 0 < k)
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (side : ι → Bool) (w t : ι → ℝ)
    (x : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hcard : (s.image t).card ≤ 2*k)
    (hsne : s.Nonempty)
    (htpos : ∀ i ∈ s, 0 < t i)
    (hwpos : ∀ i ∈ s, 0 < w i)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k+1) a b q))
    (hPstable : paperPolynomialHurwitz
      (paperDescendingNumerator (2*k+1) x +
        Polynomial.C ε * Polynomial.X^(2*k+1)))
    (hbalance : ∀ r : Fin (2*k+1),
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial (2*k+1)
          (if side i then b else a)
          (paperFiniteNumeratorCoeffs (2*k+1)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0)
    (hcontact : ∀ i ∈ s,
      (paperRaisedCrossPolynomial (2*k+1)
        (if side i then b else a) x ε).eval (t i) = 0) :
    False := by
  let n := 2*k+1
  let d : ι → ℕ → ℝ := fun i =>
    if side i then b else a
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let E := paperAxisEven n P
  let O := paperAxisOdd n P
  let z : ι → ℝ := fun i =>
    w i * (paperAxisEven n
      (paperDescendingDenominator n (d i))).eval (t i)
  let y : ι → ℝ := fun i =>
    w i * t i * (paperAxisOdd n
      (paperDescendingDenominator n (d i))).eval (t i)
  have hn : 0 < n := by dsimp [n]; omega
  have hmonic : ∀ i ∈ s, d i 0 = 1 := by
    intro i hi
    by_cases h : side i
    · simp [d, h, hb0]
    · simp [d, h, ha0]
  have hstable : ∀ i ∈ s,
      paperPolynomialHurwitz
        (paperDescendingDenominator n (d i)) := by
    intro i hi
    by_cases h : side i
    · simpa [d, h, paperSegmentDenominator] using
        (hsegment 1 (by norm_num) (by norm_num))
    · simpa [d, h, paperSegmentDenominator] using
        (hsegment 0 (by norm_num) (by norm_num))
  have hpdegree : P.natDegree = n := by
    exact paperDescendingNumerator_raise_natDegree_eq n x ε hε
  have hEbound : E.natDegree ≤ k := by
    have h := paperAxisEven_natDegree_le n P hpdegree.le
    change E.natDegree ≤ n/2 at h
    have hdiv : n/2 ≤ k := by dsimp [n]; omega
    exact h.trans hdiv
  have hEdegree : E.degree ≤ (k : WithBot ℕ) := by
    by_cases hEzero : E = 0
    · simp [hEzero]
    · rw [Polynomial.degree_eq_natDegree hEzero]
      exact_mod_cast hEbound
  have hObound : O.natDegree ≤ k := by
    have h := paperAxisOdd_natDegree_le n P hpdegree.le
    change O.natDegree ≤ (n-1)/2 at h
    have hdiv : (n-1)/2 ≤ k := by dsimp [n]; omega
    exact h.trans hdiv
  have hOcoeff : O.coeff k = ε * (-1 : ℝ)^k := by
    have hPtop : P.coeff n = ε := by
      dsimp [P]
      rw [Polynomial.coeff_add, paperDescendingNumerator_coeff,
        if_neg (by omega : ¬ n < n),
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_pos rfl]
      ring
    change (paperAxisOdd n P).coeff k = ε * (-1 : ℝ)^k
    rw [paperAxisOdd_coeff, if_pos (by dsimp [n]; omega),
      show 2*k+1 = n by rfl, hPtop]
  have hOcoe : O.coeff k ≠ 0 := by
    rw [hOcoeff]
    exact mul_ne_zero (ne_of_gt hε) (pow_ne_zero _ (by norm_num))
  have hOnat : O.natDegree = k :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      hObound hOcoe
  have hOdegree : O.degree = (k : WithBot ℕ) := by
    have hOne : O ≠ 0 := by
      intro he
      simp [he] at hOcoe
    rw [Polynomial.degree_eq_natDegree hOne, hOnat]
  have hcop : IsCoprime E O := by
    exact paperAxisEvenOdd_coprime n P hpdegree.le hPstable
  have hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0 := by
    intro j hj
    have hsmall : 2*j < n := by dsimp [n]; omega
    exact paperCoefficientBalance_even_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0 := by
    intro j hj
    have hsmall : 2*j+1 < n := by dsimp [n]; omega
    exact paperCoefficientBalance_odd_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hc : ∀ i ∈ s,
      E.eval (t i) * z i + O.eval (t i) * y i = 0 := by
    intro i hi
    have hid := paperRaisedCross_axis_identity_any
      n hn (d i) x ε (hmonic i hi) (hstable i hi)
    have hzero := hcontact i hi
    rw [hid] at hzero
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] at hzero
    calc
      E.eval (t i) * z i + O.eval (t i) * y i =
          w i * ((paperAxisEven n P).eval (t i) *
            (paperAxisEven n
              (paperDescendingDenominator n (d i))).eval (t i) +
            t i * (paperAxisOdd n P).eval (t i) *
              (paperAxisOdd n
                (paperDescendingDenominator n (d i))).eval (t i)) := by
          dsimp [E, O, z, y]
          ring
      _ = 0 := by
          rw [hzero]
          ring
  have hnode : ∃ r ∈ s.image t,
      paperGroupedResidue s t z r ≠ 0 ∨
        paperGroupedResidue s t y r ≠ 0 := by
    obtain ⟨i, hi⟩ := hsne
    have hr : t i ∈ s.image t :=
      Finset.mem_image.mpr ⟨i, hi, rfl⟩
    refine ⟨t i, hr, ?_⟩
    simpa [z, y, d] using
      (paperGroupedAxisResidue_nontrivial
        n a b ha0 hb0 s t w side htpos hwpos
        hsegment (t i) hr)
  exact paperContactResidue_no_grouped_odd_balance
    s t z y E O k hcard hEdegree hOdegree hcop
    hz hy hc hnode









theorem PaperCriticalCertificate.no_interior_even_certificate_of_stable_support
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hinter : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1)
    (hε : 0 < C.support 0)
    (hPstable : paperPolynomialHurwitz
      (paperDescendingNumerator n
        (paperFiniteNumeratorCoeffs n
          (fun j => C.support j.succ)) +
       Polynomial.C (C.support 0) * Polynomial.X^n)) :
    False := by
  let k := n/2
  let w : Fin C.atomCount → ℝ :=
    fun i => C.weight i * (1-C.compactFrequency i)^n
  let t : Fin C.atomCount → ℝ :=
    fun i => C.compactFrequency i /
      (1-C.compactFrequency i)
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  have hk : 0 < k := by dsimp [k]; omega
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hindices : C.positiveFiniteIndices = Finset.univ := by
    ext i
    simp [PaperCriticalCertificate.positiveFiniteIndices,
      (hinter i).1, (hinter i).2]
  have hcard : (Finset.univ.image t).card ≤ 2*k := by
    have h := C.positiveFiniteNodes_card_le_even_part
      hn ha0 hb0 hstableA hstableB
    simpa [PaperCriticalCertificate.positiveFiniteNodes,
      hindices, t, k] using h
  have hsne : (Finset.univ : Finset (Fin C.atomCount)).Nonempty := by
    obtain ⟨r, hr⟩ :=
      C.positiveFiniteNodes_nonempty
        hn ha0 hb0 hstableA hstableB
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hr
    exact ⟨i, Finset.mem_univ i⟩
  have htpos : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      0 < t i := by
    intro i _
    exact div_pos (hinter i).1 (sub_pos.mpr (hinter i).2)
  have hwpos : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      0 < w i := by
    intro i _
    exact mul_pos (C.weight_pos i)
      (pow_pos (sub_pos.mpr (hinter i).2) n)
  have hsegment' : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k) a b q) := by
    rw [←heven]
    exact hsegment
  have hPstable' : paperPolynomialHurwitz
      (paperDescendingNumerator (2*k) x +
        Polynomial.C ε * Polynomial.X^(2*k)) := by
    rw [←heven]
    simpa [x, ε] using hPstable
  have hbalance : ∀ r : Fin (2*k),
      (∑ i ∈ Finset.univ, w i *
        (paperGeneralCrossPolynomial (2*k)
          (if C.rightEndpoint i then b else a)
          (paperFiniteNumeratorCoeffs (2*k)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0 := by
    have hb := (C.ordinary_coefficient_balance_of_atoms_interior
      hinter).2
    rw [←heven]
    intro r
    simpa [w, t] using hb r
  have hcontact : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      (paperRaisedCrossPolynomial (2*k)
        (if C.rightEndpoint i then b else a)
        x ε).eval (t i) = 0 := by
    intro i _
    rw [←heven]
    simpa [x, ε, t] using
      (C.positive_contact_root_and_deriv
        i (hinter i).1 (hinter i).2).1
  exact paperNoEvenGroupedCertificate_le
    Finset.univ k hk a b ha0 hb0 C.rightEndpoint
    w t x ε hε hcard hsne htpos hwpos
    hsegment' hPstable' hbalance hcontact




theorem PaperCriticalCertificate.no_interior_odd_certificate_of_stable_support
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hodd : n = 2*(n/2)+1)
    (hn3 : 3 ≤ n)
    (hinter : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1)
    (hε : 0 < C.support 0)
    (hPstable : paperPolynomialHurwitz
      (paperDescendingNumerator n
        (paperFiniteNumeratorCoeffs n
          (fun j => C.support j.succ)) +
       Polynomial.C (C.support 0) * Polynomial.X^n)) :
    False := by
  let k := n/2
  let w : Fin C.atomCount → ℝ :=
    fun i => C.weight i * (1-C.compactFrequency i)^n
  let t : Fin C.atomCount → ℝ :=
    fun i => C.compactFrequency i /
      (1-C.compactFrequency i)
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  have hk : 0 < k := by dsimp [k]; omega
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hindices : C.positiveFiniteIndices = Finset.univ := by
    ext i
    simp [PaperCriticalCertificate.positiveFiniteIndices,
      (hinter i).1, (hinter i).2]
  have hcard : (Finset.univ.image t).card ≤ 2*k := by
    have h := C.positiveFiniteNodes_card_le_even_part
      hn ha0 hb0 hstableA hstableB
    simpa [PaperCriticalCertificate.positiveFiniteNodes,
      hindices, t, k] using h
  have hsne : (Finset.univ : Finset (Fin C.atomCount)).Nonempty := by
    obtain ⟨r, hr⟩ :=
      C.positiveFiniteNodes_nonempty
        hn ha0 hb0 hstableA hstableB
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hr
    exact ⟨i, Finset.mem_univ i⟩
  have htpos : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      0 < t i := by
    intro i _
    exact div_pos (hinter i).1 (sub_pos.mpr (hinter i).2)
  have hwpos : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      0 < w i := by
    intro i _
    exact mul_pos (C.weight_pos i)
      (pow_pos (sub_pos.mpr (hinter i).2) n)
  have hsegment' : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k+1) a b q) := by
    rw [←hodd]
    exact hsegment
  have hPstable' : paperPolynomialHurwitz
      (paperDescendingNumerator (2*k+1) x +
        Polynomial.C ε * Polynomial.X^(2*k+1)) := by
    rw [←hodd]
    simpa [x, ε] using hPstable
  have hbalance : ∀ r : Fin (2*k+1),
      (∑ i ∈ Finset.univ, w i *
        (paperGeneralCrossPolynomial (2*k+1)
          (if C.rightEndpoint i then b else a)
          (paperFiniteNumeratorCoeffs (2*k+1)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0 := by
    have hb := (C.ordinary_coefficient_balance_of_atoms_interior
      hinter).2
    rw [←hodd]
    intro r
    simpa [w, t] using hb r
  have hcontact : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      (paperRaisedCrossPolynomial (2*k+1)
        (if C.rightEndpoint i then b else a)
        x ε).eval (t i) = 0 := by
    intro i _
    rw [←hodd]
    simpa [x, ε, t] using
      (C.positive_contact_root_and_deriv
        i (hinter i).1 (hinter i).2).1
  exact paperNoOddGroupedCertificate_le
    Finset.univ k hk a b ha0 hb0 C.rightEndpoint
    w t x ε hε hcard hsne htpos hwpos
    hsegment' hPstable' hbalance hcontact



/-- At every order at least two, a critical certificate with positive leading
support coefficient and Hurwitz supporting numerator must have a frequency
endpoint atom. The argument allows arbitrarily repeated interior frequencies. -/
theorem PaperCriticalCertificate.stable_support_requires_frequency_endpoint
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn2 : 2 ≤ n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hε : 0 < C.support 0)
    (hPstable : paperPolynomialHurwitz
      (paperDescendingNumerator n
        (paperFiniteNumeratorCoeffs n
          (fun j => C.support j.succ)) +
       Polynomial.C (C.support 0) * Polynomial.X^n)) :
    ∃ i : Fin C.atomCount,
      C.compactFrequency i = 0 ∨ C.compactFrequency i = 1 := by
  by_contra h
  push_neg at h
  have hinter : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1 := by
    intro i
    have hi := C.frequency_mem i
    have h0 : C.compactFrequency i ≠ 0 := (h i).1
    have h1 : C.compactFrequency i ≠ 1 := (h i).2
    constructor
    · exact lt_of_le_of_ne hi.1 (Ne.symm h0)
    · exact lt_of_le_of_ne hi.2 h1
  have hn : 0 < n := by omega
  have hparity : n = 2*(n/2) ∨ n = 2*(n/2)+1 := by omega
  rcases hparity with heven | hodd
  · exact C.no_interior_even_certificate_of_stable_support
      hn ha0 hb0 hsegment heven hinter hε hPstable
  · have hn3 : 3 ≤ n := by omega
    exact C.no_interior_odd_certificate_of_stable_support
      hn ha0 hb0 hsegment hodd hn3 hinter hε hPstable


theorem PaperCriticalCertificate.no_stable_support_positive_leading
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn2 : 2 ≤ n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hε : 0 < C.support 0)
    (hPstable : paperPolynomialHurwitz
      (paperDescendingNumerator n
        (paperFiniteNumeratorCoeffs n
          (fun j => C.support j.succ)) +
       Polynomial.C (C.support 0) * Polynomial.X^n)) :
    False := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  have hn : 0 < n := by omega
  obtain ⟨i, hendpoint⟩ :=
    C.stable_support_requires_frequency_endpoint
      hn2 ha0 hb0 hsegment hε hPstable
  let d := if C.rightEndpoint i then b else a
  have hd0 : d 0 = 1 := by
    by_cases h : C.rightEndpoint i
    · simp [d, h, hb0]
    · simp [d, h, ha0]
  have hstableD : paperPolynomialHurwitz
      (paperDescendingDenominator n d) := by
    by_cases h : C.rightEndpoint i
    · simpa [d, h, paperSegmentDenominator] using
        (hsegment 1 (by norm_num) (by norm_num))
    · simpa [d, h, paperSegmentDenominator] using
        (hsegment 0 (by norm_num) (by norm_num))
  rcases hendpoint with hzero | hone
  · have hfeature := C.support_zero_atom i
    rw [hzero, paperFeatureDot_compactFeature,
      paperHomogenizedPolynomial_zero,
      Polynomial.coeff_zero_eq_eval_zero] at hfeature
    change (paperRaisedCrossPolynomial n d x ε).eval 0 = 0
      at hfeature
    rw [paperRaisedCrossPolynomial_eval_zero n hn d x ε] at hfeature
    have hdconst : 0 < d n :=
      paperDescendingDenominator_const_pos_of_hurwitz
        n hn d hd0 hstableD
    have hxzero : x (n-1) = 0 :=
      (mul_eq_zero.mp hfeature).resolve_left (ne_of_gt hdconst)
    have hpzero : P.eval 0 = 0 := by
      rw [paperRaisedNumerator_eval_zero n hn x ε]
      exact hxzero
    have hpcomplex : Polynomial.aeval (0 : ℂ) P = 0 := by
      have hcoeff : P.coeff 0 = 0 := by
        simpa only [Polynomial.coeff_zero_eq_eval_zero] using hpzero
      simpa [Polynomial.aeval_def] using
        congrArg (algebraMap ℝ ℂ) hcoeff
    exact (hPstable 0 (by norm_num)) hpcomplex
  · have hfeature := C.support_zero_atom i
    rw [hone, paperCompactFeature_one n d hd0] at hfeature
    have hεzero : C.support 0 = 0 := by
      simpa [paperFeatureDot, Fin.sum_univ_succ,
        Pi.single_apply] using hfeature
    exact (ne_of_gt hε) hεzero



theorem PaperCriticalCertificate.positive_leading_support_has_imag_zero
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn2 : 2 ≤ n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hε : 0 < C.support 0) :
    ∃ ω : ℝ,
      Polynomial.aeval (jw ω)
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n
            (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n) = 0 := by
  by_contra h
  push_neg at h
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  have hn : 0 < n := by omega
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hweak := C.support_numerator_weak_re_nonneg
    hn hstableA hstableB
  have hPstable : paperPolynomialHurwitz
      (paperDescendingNumerator n x +
        Polynomial.C ε * Polynomial.X^n) := by
    apply paperRaisedNumerator_hurwitz_of_weak_re
      n a x ε ha0 hε hstableA
    · intro ω
      simpa [x, ε] using (hweak ω).1
    · intro ω
      simpa [x, ε] using h ω
  exact C.no_stable_support_positive_leading
    hn2 ha0 hb0 hsegment hε (by simpa [x, ε] using hPstable)



theorem PaperCriticalCertificate.maximal_positive_leading_support_zero_at_origin
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn2 : 2 ≤ n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (hε : 0 < C.support 0) :
    (paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ)) +
     Polynomial.C (C.support 0) * Polynomial.X^n).eval 0 = 0 := by
  let P := paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ)) +
    Polynomial.C (C.support 0) * Polynomial.X^n
  have hn : 0 < n := by omega
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  obtain ⟨ω, hroot⟩ :=
    C.positive_leading_support_has_imag_zero
      hn2 ha0 hb0 hsegment hε
  have hωzero : ω = 0 := by
    by_contra hω
    exact (C.support_numerator_imag_ne_zero_of_maximal_contacts
      hn ha0 hb0 hstableA hstableB hmax ω hω) hroot
  subst ω
  change Polynomial.aeval (jw 0) P = 0 at hroot
  have hcoeffC : ((P.coeff 0 : ℝ) : ℂ) = 0 := by
    simpa [jw, Polynomial.aeval_def] using hroot
  have hcoeff : P.coeff 0 = 0 := by
    exact_mod_cast hcoeffC
  simpa [P, Polynomial.coeff_zero_eq_eval_zero] using hcoeff


/-- A stable real polynomial with positive leading coefficient is positive
throughout the nonnegative real axis. -/
theorem paperHurwitz_eval_pos_of_leadingCoeff_pos
    (p : Polynomial ℝ)
    (hdegree : 0 < p.degree)
    (hlead : 0 < p.leadingCoeff)
    (hstable : paperPolynomialHurwitz p)
    (x : ℝ) (hx : 0 ≤ x) :
    0 < p.eval x := by
  have htend : Filter.Tendsto (fun t : ℝ => p.eval t)
      Filter.atTop Filter.atTop :=
    p.tendsto_atTop_of_leadingCoeff_nonneg hdegree hlead.le
  have htop : ∀ᶠ t : ℝ in Filter.atTop, 0 < p.eval t :=
    htend.eventually (Filter.eventually_gt_atTop 0)
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 htop
  let T : ℝ := max (x+1) R
  have hxT : x ≤ T := by
    dsimp [T]
    linarith [le_max_left (x+1) R]
  have hpT : 0 < p.eval T := hR T (le_max_right _ _)
  by_contra hnot
  have hpx : p.eval x ≤ 0 := le_of_not_gt hnot
  have hmem : (0 : ℝ) ∈ (fun t : ℝ => p.eval t) '' Set.Icc x T :=
    (intermediate_value_Icc hxT p.continuous.continuousOn)
      ⟨hpx, hpT.le⟩
  obtain ⟨t, ht, hroot⟩ := hmem
  have hno := hstable (t : ℂ) (by exact_mod_cast hx.trans ht.1)
  apply hno
  have hz : ((p.eval t : ℝ) : ℂ) = 0 := by exact_mod_cast hroot
  exact (Polynomial.ofReal_eval (K := ℂ) p t).symm.trans hz

theorem paperRaisedNumerator_add_denominator
    (n : ℕ) (a x : ℕ → ℝ) (ε δ : ℝ)
    (ha0 : a 0 = 1) :
    paperDescendingNumerator n (fun j => x j + δ * a (j+1)) +
        Polynomial.C (ε+δ) * Polynomial.X^n =
      (paperDescendingNumerator n x + Polynomial.C ε * Polynomial.X^n) +
        Polynomial.C δ * paperDescendingDenominator n a := by
  ext m
  rw [Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    paperDescendingNumerator_coeff,
    paperDescendingNumerator_coeff,
    paperDescendingDenominator_coeff]
  by_cases hm : m < n
  · rw [if_pos hm, if_pos hm,
      if_pos (by omega : m ≤ n)]
    have hmn : n-1-m+1 = n-m := by omega
    rw [hmn]
    simp [Polynomial.coeff_X_pow, show m ≠ n by omega]
  · by_cases hmeq : m = n
    · subst m
      simp [Polynomial.coeff_X_pow,
        show ¬n<n by omega, ha0]
    · rw [if_neg hm, if_neg hm,
        if_neg (by omega : ¬m ≤ n)]
      simp [Polynomial.coeff_X_pow, hmeq]

theorem paperWeakPositiveReal_eval_nonneg
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) (ε : ℝ)
    (ha0 : a 0 = 1) (hε : 0 < ε)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hweak : ∀ ω : ℝ,
      0 ≤ ((Polynomial.aeval (jw ω)
        (paperDescendingNumerator n x +
          Polynomial.C ε * Polynomial.X^n) : ℂ) /
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n a)).re)
    (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ (paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n).eval y := by
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let D := paperDescendingDenominator n a
  have hδpos (δ : ℝ) (hδ : 0 < δ) :
      0 < (P + Polynomial.C δ * D).eval y := by
    let xδ : ℕ → ℝ := fun j => x j + δ * a (j+1)
    let Pδ : Polynomial ℝ :=
      paperDescendingNumerator n xδ +
        Polynomial.C (ε+δ) * Polynomial.X^n
    have hId : Pδ = P + Polynomial.C δ * D := by
      exact paperRaisedNumerator_add_denominator
        n a x ε δ ha0
    have hεδ : 0 < ε+δ := add_pos hε hδ
    have hreal (ω : ℝ) :
        ((Polynomial.aeval (jw ω) Pδ : ℂ) /
          Polynomial.aeval (jw ω) D).re =
        ((Polynomial.aeval (jw ω) P : ℂ) /
          Polynomial.aeval (jw ω) D).re + δ := by
      have hDne : Polynomial.aeval (jw ω) D ≠ (0 : ℂ) :=
        paperPolynomialHurwitz_imag_ne_zero D hstable ω
      have hcomplex :
          (Polynomial.aeval (jw ω) Pδ : ℂ) /
            Polynomial.aeval (jw ω) D =
          (Polynomial.aeval (jw ω) P : ℂ) /
            Polynomial.aeval (jw ω) D + (δ : ℂ) := by
        rw [hId, Polynomial.aeval_add,
          Polynomial.aeval_mul, Polynomial.aeval_C]
        field_simp
      rw [hcomplex]
      simp
    have hstrict (ω : ℝ) :
        0 < ((Polynomial.aeval (jw ω) Pδ : ℂ) /
          Polynomial.aeval (jw ω) D).re := by
      rw [hreal]
      exact add_pos_of_nonneg_of_pos (hweak ω) hδ
    have himag (ω : ℝ) :
        Polynomial.aeval (jw ω) Pδ ≠ (0 : ℂ) := by
      intro hz
      have h := hstrict ω
      rw [hz] at h
      norm_num at h
    have hstableδ : paperPolynomialHurwitz Pδ := by
      exact paperRaisedNumerator_hurwitz_of_weak_re
        n a xδ (ε+δ) ha0 hεδ hstable
        (fun ω => (hstrict ω).le) himag
    have hnat : Pδ.natDegree = n :=
      paperDescendingNumerator_raise_natDegree_eq n xδ (ε+δ) hεδ
    have hdeg : 0 < Pδ.degree := by
      apply Polynomial.natDegree_pos_iff_degree_pos.mp
      rw [hnat]
      exact hn
    have hlead : 0 < Pδ.leadingCoeff := by
      rw [←Polynomial.coeff_natDegree, hnat]
      dsimp [Pδ]
      rw [Polynomial.coeff_add, paperDescendingNumerator_coeff,
        if_neg (by omega : ¬n<n), Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow_self]
      simpa using hεδ
    rw [←hId]
    exact paperHurwitz_eval_pos_of_leadingCoeff_pos
      Pδ hdeg hlead hstableδ y hy
  refine le_of_forall_pos_le_add (fun η hη => ?_)
  let δ := η / (|D.eval y| + 1)
  have hδ : 0 < δ := div_pos hη (by positivity)
  have hpδ := hδpos δ hδ
  have hle : D.eval y ≤ |D.eval y|+1 := by
    linarith [le_abs_self (D.eval y)]
  have hδbound : δ * D.eval y ≤ η := by
    calc
      δ * D.eval y ≤ δ * (|D.eval y|+1) :=
        mul_le_mul_of_nonneg_left hle hδ.le
      _ = η := by
        dsimp [δ]
        field_simp
  simp only [Polynomial.eval_add, Polynomial.eval_C_mul] at hpδ
  change 0 < P.eval y + δ * D.eval y at hpδ
  linarith

theorem paperNonnegativePolynomial_first_coeff_nonneg
    (p : Polynomial ℝ)
    (hnonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ p.eval y)
    (hzero : p.eval 0 = 0) :
    0 ≤ p.coeff 1 := by
  have hfactor : p = Polynomial.X * p.divX := by
    simpa [Polynomial.coeff_zero_eq_eval_zero, hzero] using
      (Polynomial.X_mul_divX_add p).symm
  have hdiv_nonneg : ∀ y : ℝ, 0 < y → 0 ≤ p.divX.eval y := by
    intro y hy
    have hp := hnonneg y hy.le
    rw [hfactor, Polynomial.eval_mul, Polynomial.eval_X] at hp
    exact (mul_nonneg_iff_of_pos_left hy).mp hp
  have hlim : Filter.Tendsto (fun y : ℝ => p.divX.eval y)
      (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 (p.divX.eval 0)) :=
    p.divX.continuous.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hev : ∀ᶠ y : ℝ in 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ),
      0 ≤ p.divX.eval y := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hdiv_nonneg y hy
  have hcoeff : 0 ≤ p.divX.eval 0 := ge_of_tendsto hlim hev
  simpa [←Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_divX] using hcoeff

theorem paperNonnegativePolynomial_second_coeff_nonneg
    (p : Polynomial ℝ)
    (hnonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ p.eval y)
    (hzero : p.eval 0 = 0)
    (hfirst : p.coeff 1 = 0) :
    0 ≤ p.coeff 2 := by
  have hfactor : p = Polynomial.X * p.divX := by
    simpa [Polynomial.coeff_zero_eq_eval_zero, hzero] using
      (Polynomial.X_mul_divX_add p).symm
  have hdiv_nonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ p.divX.eval y := by
    intro y hy
    rcases hy.eq_or_lt with h | h
    · subst y
      simp [←Polynomial.coeff_zero_eq_eval_zero,
        Polynomial.coeff_divX, hfirst]
    · have hp := hnonneg y h.le
      rw [hfactor, Polynomial.eval_mul, Polynomial.eval_X] at hp
      exact (mul_nonneg_iff_of_pos_left h).mp hp
  have hdivzero : p.divX.eval 0 = 0 := by
    simp [←Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_divX, hfirst]
  have h := paperNonnegativePolynomial_first_coeff_nonneg
    p.divX hdiv_nonneg hdivzero
  simpa [Polynomial.coeff_divX] using h

theorem paperOddSaturated_first_coeff_ne_zero
    (q : Polynomial ℝ) (k : ℕ)
    (hq : q ≠ 0)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ q.eval t)
    (hdeg : q.natDegree = 2*k+1)
    (hroots : (MonicQuinticCoeff.positiveRealRoots q).card = k)
    (hzero : q.eval 0 = 0) :
    q.coeff 1 ≠ 0 := by
  let S := MonicQuinticCoeff.positiveRealRoots q
  have hS : S.card = k := hroots
  have hnotzero : (0 : ℝ) ∉ S := by
    intro h
    exact (not_lt_of_ge (le_refl (0 : ℝ)))
      (Finset.mem_filter.mp h).2
  have hrootzero : (0 : ℝ) ∈ q.roots.toFinset := by
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hq).mpr
    simpa [Polynomial.IsRoot] using hzero
  have hsub : insert (0 : ℝ) S ⊆ q.roots.toFinset := by
    intro r hr
    rcases Finset.mem_insert.mp hr with hr | hr
    · simpa [hr] using hrootzero
    · exact (Finset.filter_subset _ _) hr
  have hrootcount : ∀ r ∈ S, 2 ≤ q.roots.count r := by
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    rw [Polynomial.count_roots]
    exact MonicQuinticCoeff.rootMultiplicity_two_le_of_nonneg_of_pos_root
      q hq hnonneg hr'.2
        ((Polynomial.mem_roots hq).mp
          (Multiset.mem_toFinset.mp hr'.1))
  by_contra hfirst
  have hX2 : Polynomial.X^2 ∣ q := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro d hd
    interval_cases d
    · simpa [Polynomial.coeff_zero_eq_eval_zero] using hzero
    · exact hfirst
  have hzeroCount : 2 ≤ q.roots.count 0 := by
    rw [Polynomial.count_roots]
    apply (Polynomial.le_rootMultiplicity_iff hq).mpr
    simpa using hX2
  have hsumLower : 2*(S.card+1) ≤
      ∑ r ∈ insert (0 : ℝ) S, q.roots.count r := by
    rw [Finset.sum_insert hnotzero]
    have hs : 2*S.card ≤ ∑ r ∈ S, q.roots.count r := by
      calc
        2*S.card = ∑ r ∈ S, (2 : ℕ) := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum hrootcount
    omega
  have hsumUpper :
      (∑ r ∈ insert (0 : ℝ) S, q.roots.count r) ≤
        q.roots.card := by
    calc
      _ ≤ ∑ r ∈ q.roots.toFinset, q.roots.count r :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => Nat.zero_le _)
      _ = q.roots.card := Multiset.toFinset_sum_count_eq q.roots
  have hcard := Polynomial.card_roots' q
  omega

theorem paperOddSaturated_first_coeff_pos
    (q : Polynomial ℝ) (k : ℕ)
    (hq : q ≠ 0)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ q.eval t)
    (hdeg : q.natDegree = 2*k+1)
    (hroots : (MonicQuinticCoeff.positiveRealRoots q).card = k)
    (hzero : q.eval 0 = 0) :
    0 < q.coeff 1 := by
  have hnonneg1 :=
    paperNonnegativePolynomial_first_coeff_nonneg
      q hnonneg hzero
  have hne := paperOddSaturated_first_coeff_ne_zero
    q k hq hnonneg hdeg hroots hzero
  exact lt_of_le_of_ne hnonneg1 (Ne.symm hne)

theorem paperPolynomial_coeff_one_mul
    (p q : Polynomial ℝ) :
    (p*q).coeff 1 = p.coeff 0 * q.coeff 1 +
      p.coeff 1 * q.coeff 0 := by
  have h : Finset.antidiagonal 1 = {(0,1),(1,0)} := rfl
  simp [Polynomial.coeff_mul, h, add_comm]

theorem paperRaisedCross_coeff_one_of_double_zero
    (n : ℕ) (hn2 : 2 ≤ n) (a x : ℕ → ℝ) (ε : ℝ)
    (ha0 : a 0 = 1)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hP0 : (paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n).coeff 0 = 0)
    (hP1 : (paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n).coeff 1 = 0) :
    (paperRaisedCrossPolynomial n a x ε).coeff 1 =
      -(paperDescendingNumerator n x +
        Polynomial.C ε * Polynomial.X^n).coeff 2 *
      (paperDescendingDenominator n a).coeff 0 := by
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let D := paperDescendingDenominator n a
  have hId := paperRaisedCross_axis_identity_any
    n (by omega) a x ε ha0 hstable
  change paperRaisedCrossPolynomial n a x ε =
    paperAxisEven n P * paperAxisEven n D +
      Polynomial.X * paperAxisOdd n P * paperAxisOdd n D at hId
  rw [hId, Polynomial.coeff_add,
    paperPolynomial_coeff_one_mul,
    mul_assoc, Polynomial.coeff_X_mul,
    Polynomial.mul_coeff_zero]
  simp [paperAxisEven_coeff, paperAxisOdd_coeff,
    show (1 : ℕ) ≤ n by omega,
    show P.coeff 0 = 0 from hP0,
    show P.coeff 1 = 0 from hP1]
  simp [P, D, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  ring

theorem paperOddSaturated_support_simple_zero
    (n k : ℕ) (hn2 : 2 ≤ n) (hodd : n = 2*k+1)
    (a x : ℕ → ℝ) (ε : ℝ)
    (ha0 : a 0 = 1) (hε : 0 < ε)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hweak : ∀ ω : ℝ,
      0 ≤ ((Polynomial.aeval (jw ω)
        (paperDescendingNumerator n x +
          Polynomial.C ε * Polynomial.X^n) : ℂ) /
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n a)).re)
    (hcross : ∀ t : ℝ, 0 ≤ t →
      0 ≤ (paperRaisedCrossPolynomial n a x ε).eval t)
    (hroots : (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a x ε)).card = k)
    (hPzero : (paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n).eval 0 = 0) :
    0 < (paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n).coeff 1 := by
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let D := paperDescendingDenominator n a
  let Q := paperRaisedCrossPolynomial n a x ε
  have hPnonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ P.eval y := by
    intro y hy
    exact paperWeakPositiveReal_eval_nonneg
      n (by omega) a x ε ha0 hε hstable hweak y hy
  have hP1nonneg : 0 ≤ P.coeff 1 :=
    paperNonnegativePolynomial_first_coeff_nonneg
      P hPnonneg hPzero
  have hQ0 : Q.eval 0 = 0 := by
    rw [paperRaisedCrossPolynomial_eval_zero n (by omega) a x ε]
    have hx : x (n-1) = 0 := by
      simpa [P, paperRaisedNumerator_eval_zero n (by omega) x ε]
        using hPzero
    simp [hx]
  have hQdeg : Q.natDegree = 2*k+1 := by
    rw [paperRaisedCrossPolynomial_natDegree_eq n a x ε ha0
      (ne_of_gt hε), hodd]
  have hQne : Q ≠ 0 := by
    intro he
    have htop := paperRaisedCrossPolynomial_top_coeff
      n a x ε ha0
    change Q.coeff n = ε at htop
    simp [he] at htop
    exact (ne_of_gt hε) htop.symm
  have hQ1pos : 0 < Q.coeff 1 :=
    paperOddSaturated_first_coeff_pos
      Q k hQne hcross hQdeg hroots hQ0
  by_contra hnot
  have hP1 : P.coeff 1 = 0 := by
    exact le_antisymm (le_of_not_gt hnot) hP1nonneg
  have hP2nonneg : 0 ≤ P.coeff 2 :=
    paperNonnegativePolynomial_second_coeff_nonneg
      P hPnonneg hPzero hP1
  have hD0pos : 0 < D.coeff 0 := by
    have h := paperDescendingDenominator_const_pos_of_hurwitz
      n (by omega) a ha0 hstable
    change 0 < (paperDescendingDenominator n a).coeff 0
    rw [paperDescendingDenominator_coeff,
      if_pos (by omega : 0 ≤ n)]
    simpa using h
  have hQ1 := paperRaisedCross_coeff_one_of_double_zero
    n hn2 a x ε ha0 hstable
    (by simpa [P, Polynomial.coeff_zero_eq_eval_zero] using hPzero)
    (by simpa [P] using hP1)
  change Q.coeff 1 = -(P.coeff 2)*D.coeff 0 at hQ1
  nlinarith [mul_nonneg hP2nonneg hD0pos.le]

theorem PaperCriticalCertificate.maximal_odd_positive_leading_support_simple_zero
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn2 : 2 ≤ n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hodd : n = 2*(n/2)+1)
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (hε : 0 < C.support 0) :
    0 < (paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ)) +
      Polynomial.C (C.support 0) * Polynomial.X^n).coeff 1 := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  have hn : 0 < n := by omega
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hweak := C.support_numerator_weak_re_nonneg
    hn hstableA hstableB
  have hstructure := C.maximal_positiveFiniteNodes_structure
    hn ha0 hb0 hstableA hstableB hmax
  have hroots : (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a x ε)).card = n/2 := by
    simpa [x, ε] using hstructure.1
  have hcross : ∀ t : ℝ, 0 ≤ t →
      0 ≤ (paperRaisedCrossPolynomial n a x ε).eval t := by
    intro t ht
    exact paperFeature_nonneg_cross_nonneg
      n a C.support C.support_nonneg_left t ht
  have hPzero := C.maximal_positive_leading_support_zero_at_origin
    hn2 ha0 hb0 hsegment hmax hε
  exact paperOddSaturated_support_simple_zero
    n (n/2) hn2 hodd a x ε ha0 hε hstableA
      (fun ω => by simpa [x, ε] using (hweak ω).1)
      hcross hroots (by simpa [x, ε] using hPzero)



theorem paperContactResidue_no_grouped_odd_shifted_balance
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z y : ι → ℝ)
    (E O : Polynomial ℝ) (k : ℕ)
    (htpos : ∀ i ∈ s, 0 < t i)
    (hcard : (s.image t).card ≤ 2*k)
    (hEdegree : E.degree ≤ k)
    (hOdegree : O.degree = (k : WithBot ℕ))
    (hcop : IsCoprime E O)
    (hz : ∀ j < k, (∑ i ∈ s, (t i)^(j+1) * z i) = 0)
    (hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0)
    (hc : ∀ i ∈ s, E.eval (t i) * (t i * z i) +
      O.eval (t i) * y i = 0)
    (hnode : ∃ r ∈ s.image t,
      paperGroupedResidue s t z r ≠ 0 ∨
        paperGroupedResidue s t y r ≠ 0) : False := by
  let z' : ι → ℝ := fun i => t i * z i
  have hz' : ∀ j < k,
      (∑ i ∈ s, (t i)^j * z' i) = 0 := by
    intro j hj
    convert hz j hj using 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [z']
    ring
  have hc' : ∀ i ∈ s,
      E.eval (t i) * z' i + O.eval (t i) * y i = 0 := by
    intro i hi
    exact hc i hi
  have hgroup (r : ℝ) :
      paperGroupedResidue s t z' r =
        r * paperGroupedResidue s t z r := by
    dsimp [paperGroupedResidue, z']
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  have hnode' : ∃ r ∈ s.image t,
      paperGroupedResidue s t z' r ≠ 0 ∨
        paperGroupedResidue s t y r ≠ 0 := by
    obtain ⟨r, hr, h⟩ := hnode
    refine ⟨r, hr, ?_⟩
    rcases h with hz0 | hy0
    · left
      rw [hgroup]
      have hrpos : 0 < r := by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
        exact htpos i hi
      exact mul_ne_zero (ne_of_gt hrpos) hz0
    · exact Or.inr hy0
  exact paperContactResidue_no_grouped_odd_balance
    s t z' y E O k hcard hEdegree hOdegree hcop
    hz' hy hc' hnode'


/-- A root-product lower bound for a stable polynomial with arbitrary
positive leading coefficient. -/
theorem paperHurwitz_eval_norm_lower_of_leadingCoeff_pos
    (p : Polynomial ℝ) (hlead : 0 < p.leadingCoeff)
    (hstable : paperPolynomialHurwitz p)
    (z : ℂ) (hz : 0 < z.re) :
    p.leadingCoeff * z.re ^ p.natDegree ≤
      ‖(Polynomial.aeval z p : ℂ)‖ := by
  let P := p.map (algebraMap ℝ ℂ)
  have hsplit : P.Splits (RingHom.id ℂ) := IsAlgClosed.splits P
  have hfactor (w : P.roots) : z.re ≤ ‖z - (w : ℂ)‖ := by
    have hwroot : Polynomial.aeval (w : ℂ) p = 0 := by
      have hPne : P ≠ 0 := by
        intro he
        have hcoeff : P.leadingCoeff = 0 := by simp [he]
        have : ((p.leadingCoeff : ℝ) : ℂ) = 0 := by
          simpa [P] using hcoeff
        exact (ne_of_gt hlead) (by exact_mod_cast this)
      have h := (Polynomial.mem_roots hPne).mp
        (Multiset.coe_mem (x := w))
      simpa [P] using h
    have hw : (w : ℂ).re < 0 :=
      lt_of_not_ge (fun hge => hstable w hge hwroot)
    have hre : z.re ≤ (z - (w : ℂ)).re := by
      simp only [Complex.sub_re]
      linarith
    exact hre.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hprod :
      (∏ w : P.roots, z.re) ≤
        ∏ w : P.roots, ‖z - (w : ℂ)‖ :=
    Finset.prod_le_prod (fun _ _ => hz.le) (fun w _ => hfactor w)
  have hcard : P.roots.card = p.natDegree := by
    simpa [P, Polynomial.natDegree_map] using
      (Polynomial.natDegree_eq_card_roots' hsplit).symm
  simp only [Finset.prod_const, Finset.card_univ, Multiset.card_coe,
    hcard] at hprod
  have hEval : P.eval z = Polynomial.aeval z p := by
    simp [P]
  rw [← hEval,
    Polynomial.eval_eq_prod_roots_sub_of_splits_id hsplit,
    general_prod_map_eq_prod_occurrences, norm_mul,
    norm_prod]
  have hleadnorm : ‖P.leadingCoeff‖ = p.leadingCoeff := by
    simp [P, Complex.norm_real, abs_of_pos hlead]
  rw [hleadnorm]
  exact mul_le_mul_of_nonneg_left hprod hlead.le

theorem paperPerturbedStable_no_open_right_root
    (P D : Polynomial ℝ) (n : ℕ) (ε : ℝ)
    (hε : 0 < ε)
    (hpert : ∀ δ : ℝ, 0 < δ →
      paperPolynomialHurwitz (P + Polynomial.C δ * D) ∧
      (P + Polynomial.C δ * D).natDegree = n ∧
      (P + Polynomial.C δ * D).leadingCoeff = ε+δ)
    (z : ℂ) (hz : 0 < z.re) :
    Polynomial.aeval z P ≠ (0 : ℂ) := by
  intro hzero
  have hpow : 0 < z.re^n := pow_pos hz n
  have hbound (δ : ℝ) (hδ : 0 < δ) :
      ε * z.re^n ≤ δ * ‖(Polynomial.aeval z D : ℂ)‖ := by
    obtain ⟨hstable, hdegree, hlead⟩ := hpert δ hδ
    have hnorm :=
      paperHurwitz_eval_norm_lower_of_leadingCoeff_pos
        (P + Polynomial.C δ * D)
        (by rw [hlead]; exact add_pos hε hδ)
        hstable z hz
    rw [hdegree, hlead,
      Polynomial.aeval_add, Polynomial.aeval_mul,
      Polynomial.aeval_C, hzero, zero_add] at hnorm
    have hnorm' :
        ‖(δ : ℂ) * Polynomial.aeval z D‖ =
        δ * ‖(Polynomial.aeval z D : ℂ)‖ := by
      simp [norm_mul, Complex.norm_real, abs_of_pos hδ]
    change (ε+δ) * z.re^n ≤
      ‖(δ : ℂ) * Polynomial.aeval z D‖ at hnorm
    rw [hnorm'] at hnorm
    nlinarith
  have hnonpos : ε * z.re^n ≤ 0 := by
    refine le_of_forall_pos_le_add (fun η hη => ?_)
    let δ := η / (‖(Polynomial.aeval z D : ℂ)‖ + 1)
    have hδ : 0 < δ := div_pos hη (by positivity)
    have h := hbound δ hδ
    have hδbound : δ * ‖(Polynomial.aeval z D : ℂ)‖ ≤ η := by
      calc
        _ ≤ δ * (‖(Polynomial.aeval z D : ℂ)‖ + 1) := by
          apply mul_le_mul_of_nonneg_left _ hδ.le
          linarith
        _ = η := by
          dsimp [δ]
          field_simp
    linarith
  exact (not_le_of_gt (mul_pos hε hpow)) hnonpos

theorem paperWeakPositiveReal_perturb_hurwitz
    (n : ℕ) (a x : ℕ → ℝ) (ε : ℝ)
    (ha0 : a 0 = 1) (hε : 0 ≤ ε)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hweak : ∀ ω : ℝ,
      0 ≤ ((Polynomial.aeval (jw ω)
        (paperDescendingNumerator n x +
          Polynomial.C ε * Polynomial.X^n) : ℂ) /
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n a)).re)
    (δ : ℝ) (hδ : 0 < δ) :
    paperPolynomialHurwitz
      ((paperDescendingNumerator n x +
        Polynomial.C ε * Polynomial.X^n) +
       Polynomial.C δ * paperDescendingDenominator n a) ∧
    ((paperDescendingNumerator n x +
        Polynomial.C ε * Polynomial.X^n) +
       Polynomial.C δ * paperDescendingDenominator n a).natDegree = n ∧
    ((paperDescendingNumerator n x +
        Polynomial.C ε * Polynomial.X^n) +
       Polynomial.C δ * paperDescendingDenominator n a).leadingCoeff = ε+δ := by
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let D := paperDescendingDenominator n a
  let xδ : ℕ → ℝ := fun j => x j + δ * a (j+1)
  let Pδ : Polynomial ℝ :=
    paperDescendingNumerator n xδ +
      Polynomial.C (ε+δ) * Polynomial.X^n
  have hId : Pδ = P + Polynomial.C δ * D :=
    paperRaisedNumerator_add_denominator n a x ε δ ha0
  have hεδ : 0 < ε+δ := add_pos_of_nonneg_of_pos hε hδ
  have hreal (ω : ℝ) :
      ((Polynomial.aeval (jw ω) Pδ : ℂ) /
        Polynomial.aeval (jw ω) D).re =
      ((Polynomial.aeval (jw ω) P : ℂ) /
        Polynomial.aeval (jw ω) D).re + δ := by
    have hDne : Polynomial.aeval (jw ω) D ≠ (0 : ℂ) :=
      paperPolynomialHurwitz_imag_ne_zero D hstable ω
    have hcomplex :
        (Polynomial.aeval (jw ω) Pδ : ℂ) /
          Polynomial.aeval (jw ω) D =
        (Polynomial.aeval (jw ω) P : ℂ) /
          Polynomial.aeval (jw ω) D + (δ : ℂ) := by
      rw [hId, Polynomial.aeval_add,
        Polynomial.aeval_mul, Polynomial.aeval_C]
      field_simp
    rw [hcomplex]
    simp
  have hstrict (ω : ℝ) :
      0 < ((Polynomial.aeval (jw ω) Pδ : ℂ) /
        Polynomial.aeval (jw ω) D).re := by
    rw [hreal]
    exact add_pos_of_nonneg_of_pos (hweak ω) hδ
  have himag (ω : ℝ) :
      Polynomial.aeval (jw ω) Pδ ≠ (0 : ℂ) := by
    intro hz
    have h := hstrict ω
    rw [hz] at h
    norm_num at h
  have hstableδ : paperPolynomialHurwitz Pδ :=
    paperRaisedNumerator_hurwitz_of_weak_re
      n a xδ (ε+δ) ha0 hεδ hstable
      (fun ω => (hstrict ω).le) himag
  have hnat : Pδ.natDegree = n :=
    paperDescendingNumerator_raise_natDegree_eq n xδ (ε+δ) hεδ
  have hlead : Pδ.leadingCoeff = ε+δ := by
    rw [←Polynomial.coeff_natDegree, hnat]
    dsimp [Pδ]
    rw [Polynomial.coeff_add, paperDescendingNumerator_coeff,
      if_neg (by omega : ¬n<n), Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow_self]
    ring
  rw [←hId]
  exact ⟨hstableδ, hnat, hlead⟩

theorem paperWeakPositiveReal_no_open_right_root
    (n : ℕ) (a x : ℕ → ℝ) (ε : ℝ)
    (ha0 : a 0 = 1) (hε : 0 < ε)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hweak : ∀ ω : ℝ,
      0 ≤ ((Polynomial.aeval (jw ω)
        (paperDescendingNumerator n x +
          Polynomial.C ε * Polynomial.X^n) : ℂ) /
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n a)).re)
    (z : ℂ) (hz : 0 < z.re) :
    Polynomial.aeval z
      (paperDescendingNumerator n x +
        Polynomial.C ε * Polynomial.X^n) ≠ (0 : ℂ) := by
  apply paperPerturbedStable_no_open_right_root
    (paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n)
    (paperDescendingDenominator n a) n ε hε
  · intro δ hδ
    exact paperWeakPositiveReal_perturb_hurwitz
      n a x ε ha0 hε.le hstable hweak δ hδ
  · exact hz

theorem paperPolynomialHurwitz_divX_of_simple_origin
    (p : Polynomial ℝ)
    (hzero : p.eval 0 = 0)
    (hfirst : p.coeff 1 ≠ 0)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z p ≠ (0 : ℂ))
    (himag : ∀ ω : ℝ, ω ≠ 0 →
      Polynomial.aeval (jw ω) p ≠ (0 : ℂ)) :
    paperPolynomialHurwitz p.divX := by
  have hfactor : p = Polynomial.X * p.divX := by
    simpa [Polynomial.coeff_zero_eq_eval_zero, hzero] using
      (Polynomial.X_mul_divX_add p).symm
  intro z hzre hdivzero
  have hpzero : Polynomial.aeval z p = 0 := by
    rw [hfactor, Polynomial.aeval_mul,
      Polynomial.aeval_X, hdivzero]
    simp
  rcases hzre.eq_or_lt with hzre0 | hzrePos
  · have hzjw : z = jw z.im := by
      apply Complex.ext
      · simp [jw, hzre0.symm]
      · simp [jw]
    by_cases hz0 : z = 0
    · subst z
      have hcoeff : ((p.divX.coeff 0 : ℝ) : ℂ) = 0 := by
        simpa [Polynomial.aeval_def] using hdivzero
      have hreal : p.coeff 1 = 0 := by
        exact_mod_cast hcoeff
      exact hfirst (by simpa [Polynomial.coeff_divX] using hreal)
    · have hωne : z.im ≠ 0 := by
        intro h
        apply hz0
        rw [hzjw, h]
        simp [jw]
      exact (himag z.im hωne) (hzjw ▸ hpzero)
  · exact (hopen z hzrePos) hpzero

theorem PaperCriticalCertificate.maximal_odd_positive_leading_support_divX_hurwitz
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn2 : 2 ≤ n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hodd : n = 2*(n/2)+1)
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (hε : 0 < C.support 0) :
    paperPolynomialHurwitz
      (paperDescendingNumerator n
        (paperFiniteNumeratorCoeffs n
          (fun j => C.support j.succ)) +
       Polynomial.C (C.support 0) * Polynomial.X^n).divX := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hweak := C.support_numerator_weak_re_nonneg
    (by omega : 0 < n) hstableA hstableB
  have hzero : P.eval 0 = 0 :=
    C.maximal_positive_leading_support_zero_at_origin
      hn2 ha0 hb0 hsegment hmax hε
  have hfirst : P.coeff 1 ≠ 0 := ne_of_gt
    (C.maximal_odd_positive_leading_support_simple_zero
      hn2 ha0 hb0 hsegment hodd hmax hε)
  have hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ) := by
    intro z hz
    exact paperWeakPositiveReal_no_open_right_root
      n a x ε ha0 hε hstableA
      (fun ω => by simpa [x, ε] using (hweak ω).1) z hz
  have himag : ∀ ω : ℝ, ω ≠ 0 →
      Polynomial.aeval (jw ω) P ≠ (0 : ℂ) := by
    intro ω hω
    exact C.support_numerator_imag_ne_zero_of_maximal_contacts
      (by omega : 0 < n) ha0 hb0 hstableA hstableB
      hmax ω hω
  exact paperPolynomialHurwitz_divX_of_simple_origin
    P hzero hfirst hopen himag

theorem paperAxisOdd_X_mul
    (n : ℕ) (R : Polynomial ℝ) :
    paperAxisOdd n (Polynomial.X * R) = paperAxisEven n R := by
  ext j
  rw [paperAxisOdd_coeff, paperAxisEven_coeff]
  by_cases hj : j ≤ n
  · rw [if_pos hj, if_pos hj]
    have hidx : 2*j+1 = (2*j)+1 := by omega
    rw [hidx, Polynomial.coeff_X_mul]
  · simp [hj]

theorem paperAxisEven_X_mul
    (n : ℕ) (R : Polynomial ℝ)
    (hRdeg : R.natDegree ≤ n) :
    paperAxisEven n (Polynomial.X * R) =
      -(Polynomial.X * paperAxisOdd n R) := by
  ext j
  rw [paperAxisEven_coeff, Polynomial.coeff_neg]
  cases j with
  | zero => simp
  | succ j =>
      by_cases hj : j+1 ≤ n
      · rw [if_pos hj, Polynomial.coeff_X_mul,
          paperAxisOdd_coeff, if_pos (by omega : j ≤ n)]
        have hidx : 2*(j+1) = (2*j+1)+1 := by omega
        rw [hidx, Polynomial.coeff_X_mul]
        simp only [pow_succ]
        ring
      · rw [if_neg hj, Polynomial.coeff_X_mul,
          paperAxisOdd_coeff]
        by_cases hj2 : j ≤ n
        · rw [if_pos hj2]
          have hvanish : R.coeff (2*j+1) = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt
              (by omega : R.natDegree < 2*j+1)
          simp [hvanish]
        · simp [hj2]

theorem paperAxisEven_divX_of_X_mul
    (n : ℕ) (R : Polynomial ℝ)
    (hRdeg : R.natDegree ≤ n) :
    (paperAxisEven n (Polynomial.X * R)).divX =
      -paperAxisOdd n R := by
  rw [paperAxisEven_X_mul n R hRdeg]
  ext j
  rw [Polynomial.coeff_divX, Polynomial.coeff_neg,
    Polynomial.coeff_neg, Polynomial.coeff_X_mul]

theorem paperAxis_divX_coprime_of_stable_divX
    (n : ℕ) (p : Polynomial ℝ)
    (hdegree : p.natDegree ≤ n)
    (hzero : p.eval 0 = 0)
    (hstable : paperPolynomialHurwitz p.divX) :
    IsCoprime (paperAxisEven n p).divX
      (paperAxisOdd n p) := by
  let R := p.divX
  have hRdeg : R.natDegree ≤ n :=
    (Polynomial.natDegree_divX_le).trans hdegree
  have hfactor : p = Polynomial.X * R := by
    simpa [R, Polynomial.coeff_zero_eq_eval_zero, hzero] using
      (Polynomial.X_mul_divX_add p).symm
  have hcop := paperAxisEvenOdd_coprime n R hRdeg hstable
  rw [hfactor,
    paperAxisEven_divX_of_X_mul n R hRdeg,
    paperAxisOdd_X_mul n R]
  exact (IsCoprime.neg_left_iff _ _).mpr hcop.symm

theorem PaperCriticalCertificate.maximal_odd_positive_leading_parity_coprime
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn2 : 2 ≤ n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hodd : n = 2*(n/2)+1)
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (hε : 0 < C.support 0) :
    let P := paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ)) +
       Polynomial.C (C.support 0) * Polynomial.X^n
    IsCoprime (paperAxisEven n P).divX
      (paperAxisOdd n P) := by
  dsimp
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  have hpdeg : P.natDegree ≤ n :=
    (paperDescendingNumerator_raise_natDegree_eq
      n x ε hε).le
  have hzero : P.eval 0 = 0 :=
    C.maximal_positive_leading_support_zero_at_origin
      hn2 ha0 hb0 hsegment hmax hε
  have hstable : paperPolynomialHurwitz P.divX :=
    C.maximal_odd_positive_leading_support_divX_hurwitz
      hn2 ha0 hb0 hsegment hodd hmax hε
  exact paperAxis_divX_coprime_of_stable_divX
    n P hpdeg hzero hstable

theorem PaperCriticalCertificate.positive_leading_atoms_finite
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hε : 0 < C.support 0) :
    ∀ i : Fin C.atomCount, C.compactFrequency i < 1 := by
  intro i
  have hle := (C.frequency_mem i).2
  rcases hle.eq_or_lt with h | h
  · let d : ℕ → ℝ := if C.rightEndpoint i then b else a
    have hd0 : d 0 = 1 := by
      cases hs : C.rightEndpoint i <;> simp [d, hs, ha0, hb0]
    have hfeature := C.support_zero_atom i
    rw [h, paperCompactFeature_one n d hd0] at hfeature
    have hεzero : C.support 0 = 0 := by
      simpa [paperFeatureDot, Fin.sum_univ_succ,
        Pi.single_apply] using hfeature
    exact False.elim ((ne_of_gt hε) hεzero)
  · exact h

theorem PaperCriticalCertificate.ordinary_coefficient_balance_of_atoms_finite
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b)
    (hfinite : ∀ i : Fin C.atomCount,
      C.compactFrequency i < 1) :
    (∑ i : Fin C.atomCount,
      C.weight i * (1-C.compactFrequency i)^n *
        (paperRaiseCorrection n
          (if C.rightEndpoint i then b else a)).eval
            (C.compactFrequency i /
              (1-C.compactFrequency i))) = 0 ∧
    (∀ j : Fin n,
      (∑ i : Fin C.atomCount,
        C.weight i * (1-C.compactFrequency i)^n *
          (paperGeneralCrossPolynomial n
            (if C.rightEndpoint i then b else a)
            (paperFiniteNumeratorCoeffs n
              (fun k => if j = k then 1 else 0))).eval
                (C.compactFrequency i /
                  (1-C.compactFrequency i))) = 0) := by
  have hbalance :
      (∑ i : Fin C.atomCount,
        (C.weight i * (1-C.compactFrequency i)^n) •
          paperOrdinaryFeature n
            (if C.rightEndpoint i then b else a)
            (C.compactFrequency i /
              (1-C.compactFrequency i))) = 0 := by
    calc
      _ = ∑ i : Fin C.atomCount,
          C.weight i •
            paperCompactFeature n
              (if C.rightEndpoint i then b else a)
              (C.compactFrequency i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [paperCompactFeature_eq_scaledOrdinary
          n _ _ (ne_of_lt (hfinite i))]
        simp only [smul_smul, smul_eq_mul]
      _ = 0 := C.balance
  have hcoord (j : Fin (n+1)) :
      (∑ i : Fin C.atomCount,
        C.weight i * (1-C.compactFrequency i)^n *
          paperOrdinaryFeature n
            (if C.rightEndpoint i then b else a)
            (C.compactFrequency i /
              (1-C.compactFrequency i)) j) = 0 := by
    have h := congrArg (fun v : Fin (n+1) → ℝ => v j) hbalance
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] using h
  constructor
  · simpa [paperOrdinaryFeature] using hcoord 0
  · intro j
    simpa [paperOrdinaryFeature] using hcoord j.succ

theorem paperSum_positive_filter_of_zero_at_zero
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t f : ι → ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i)
    (hzero : ∀ i ∈ s, t i = 0 → f i = 0) :
    (∑ i ∈ s.filter (fun i => 0 < t i), f i) =
      ∑ i ∈ s, f i := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : 0 < t i
  · simp [h]
  · have hz : t i = 0 := le_antisymm (le_of_not_gt h) (ht i hi)
    simp [h, hzero i hi hz]

theorem paperNoOddGroupedCertificate_with_zero
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) (hk : 0 < k)
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (side : ι → Bool) (w t : ι → ℝ)
    (x : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hcard : ((s.filter (fun i => 0 < t i)).image t).card ≤ 2*k)
    (hsne : (s.filter (fun i => 0 < t i)).Nonempty)
    (htnonneg : ∀ i ∈ s, 0 ≤ t i)
    (hwpos : ∀ i ∈ s, 0 < w i)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k+1) a b q))
    (hPzero : (paperDescendingNumerator (2*k+1) x +
      Polynomial.C ε * Polynomial.X^(2*k+1)).eval 0 = 0)
    (hPdivstable : paperPolynomialHurwitz
      (paperDescendingNumerator (2*k+1) x +
        Polynomial.C ε * Polynomial.X^(2*k+1)).divX)
    (hbalance : ∀ r : Fin (2*k+1),
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial (2*k+1)
          (if side i then b else a)
          (paperFiniteNumeratorCoeffs (2*k+1)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0)
    (hcontact : ∀ i ∈ s.filter (fun i => 0 < t i),
      (paperRaisedCrossPolynomial (2*k+1)
        (if side i then b else a) x ε).eval (t i) = 0) :
    False := by
  let n := 2*k+1
  let sPos := s.filter (fun i => 0 < t i)
  let d : ι → ℕ → ℝ := fun i => if side i then b else a
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let E := paperAxisEven n P
  let E' := E.divX
  let O := paperAxisOdd n P
  let z : ι → ℝ := fun i =>
    w i * (paperAxisEven n
      (paperDescendingDenominator n (d i))).eval (t i)
  let y : ι → ℝ := fun i =>
    w i * t i * (paperAxisOdd n
      (paperDescendingDenominator n (d i))).eval (t i)
  have hn : 0 < n := by dsimp [n]; omega
  have hmonic : ∀ i ∈ s, d i 0 = 1 := by
    intro i hi
    by_cases h : side i
    · simp [d, h, hb0]
    · simp [d, h, ha0]
  have hstable : ∀ i ∈ s,
      paperPolynomialHurwitz
        (paperDescendingDenominator n (d i)) := by
    intro i hi
    by_cases h : side i
    · simpa [d, h, paperSegmentDenominator] using
        (hsegment 1 (by norm_num) (by norm_num))
    · simpa [d, h, paperSegmentDenominator] using
        (hsegment 0 (by norm_num) (by norm_num))
  have hpdegree : P.natDegree = n :=
    paperDescendingNumerator_raise_natDegree_eq n x ε hε
  have hEbound : E.natDegree ≤ k := by
    have h := paperAxisEven_natDegree_le n P hpdegree.le
    change E.natDegree ≤ n/2 at h
    have hdiv : n/2 ≤ k := by dsimp [n]; omega
    exact h.trans hdiv
  have hE'bound : E'.natDegree ≤ k :=
    (Polynomial.natDegree_divX_le).trans hEbound
  have hE'degree : E'.degree ≤ (k : WithBot ℕ) := by
    by_cases hzero : E' = 0
    · simp [hzero]
    · rw [Polynomial.degree_eq_natDegree hzero]
      exact_mod_cast hE'bound
  have hObound : O.natDegree ≤ k := by
    have h := paperAxisOdd_natDegree_le n P hpdegree.le
    change O.natDegree ≤ (n-1)/2 at h
    have hdiv : (n-1)/2 ≤ k := by dsimp [n]; omega
    exact h.trans hdiv
  have hOcoeff : O.coeff k = ε * (-1 : ℝ)^k := by
    have hPtop : P.coeff n = ε := by
      dsimp [P]
      rw [Polynomial.coeff_add, paperDescendingNumerator_coeff,
        if_neg (by omega : ¬ n < n),
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_pos rfl]
      ring
    change (paperAxisOdd n P).coeff k = ε * (-1 : ℝ)^k
    rw [paperAxisOdd_coeff, if_pos (by dsimp [n]; omega),
      show 2*k+1 = n by rfl, hPtop]
  have hOcoe : O.coeff k ≠ 0 := by
    rw [hOcoeff]
    exact mul_ne_zero (ne_of_gt hε) (pow_ne_zero _ (by norm_num))
  have hOnat : O.natDegree = k :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      hObound hOcoe
  have hOdegree : O.degree = (k : WithBot ℕ) := by
    have hOne : O ≠ 0 := by
      intro he
      simp [he] at hOcoe
    rw [Polynomial.degree_eq_natDegree hOne, hOnat]
  have hcop : IsCoprime E' O :=
    paperAxis_divX_coprime_of_stable_divX
      n P hpdegree.le hPzero hPdivstable
  have hE0 : E.eval 0 = 0 := by
    have hPcoeff : P.coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact hPzero
    rw [←Polynomial.coeff_zero_eq_eval_zero,
      paperAxisEven_coeff, if_pos (by omega : 0 ≤ n)]
    simpa using hPcoeff
  have hEfactor : E = Polynomial.X * E' := by
    simpa [E', Polynomial.coeff_zero_eq_eval_zero,
      hE0] using (Polynomial.X_mul_divX_add E).symm
  have hz : ∀ j < k,
      (∑ i ∈ sPos, (t i)^(j+1) * z i) = 0 := by
    intro j hj
    have hsmall : 2*(j+1) < n := by dsimp [n]; omega
    have hfull := paperCoefficientBalance_even_moments
      s n hn d w t hmonic hstable hbalance (j+1) hsmall
    have hfilter := paperSum_positive_filter_of_zero_at_zero
      s t (fun i => (t i)^(j+1) * z i) htnonneg
      (by intro i hi hz; simp [hz])
    exact hfilter.trans hfull
  have hy : ∀ j < k,
      (∑ i ∈ sPos, (t i)^j * y i) = 0 := by
    intro j hj
    have hsmall : 2*j+1 < n := by dsimp [n]; omega
    have hfull := paperCoefficientBalance_odd_moments
      s n hn d w t hmonic hstable hbalance j hsmall
    have hfilter := paperSum_positive_filter_of_zero_at_zero
      s t (fun i => (t i)^j * y i) htnonneg
      (by intro i hi hz; simp [y, hz])
    exact hfilter.trans hfull
  have hc : ∀ i ∈ sPos,
      E'.eval (t i) * (t i * z i) + O.eval (t i) * y i = 0 := by
    intro i hi
    have hsi : i ∈ s := (Finset.mem_filter.mp hi).1
    have hid := paperRaisedCross_axis_identity_any
      n hn (d i) x ε (hmonic i hsi) (hstable i hsi)
    have hzero := hcontact i hi
    rw [hid] at hzero
    change (E * paperAxisEven n
      (paperDescendingDenominator n (d i)) +
      Polynomial.X * O * paperAxisOdd n
        (paperDescendingDenominator n (d i))).eval (t i) = 0 at hzero
    rw [hEfactor] at hzero
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] at hzero
    have hwzero := congrArg (fun v : ℝ => w i * v) hzero
    simp only [mul_zero] at hwzero
    dsimp [z, y]
    convert hwzero using 1
    ring
  have hnode : ∃ r ∈ sPos.image t,
      paperGroupedResidue sPos t z r ≠ 0 ∨
        paperGroupedResidue sPos t y r ≠ 0 := by
    obtain ⟨i, hi⟩ := hsne
    have hr : t i ∈ sPos.image t :=
      Finset.mem_image.mpr ⟨i, hi, rfl⟩
    refine ⟨t i, hr, ?_⟩
    simpa [z, y, d] using
      (paperGroupedAxisResidue_nontrivial
        n a b ha0 hb0 sPos t w side
        (fun i hi => (Finset.mem_filter.mp hi).2)
        (fun i hi => hwpos i (Finset.mem_filter.mp hi).1)
        hsegment (t i) hr)
  exact paperContactResidue_no_grouped_odd_shifted_balance
    sPos t z y E' O k
    (fun i hi => (Finset.mem_filter.mp hi).2)
    hcard hE'degree hOdegree hcop hz hy hc hnode

theorem PaperCriticalCertificate.no_maximal_odd_positive_leading
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn3 : 3 ≤ n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hodd : n = 2*(n/2)+1)
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (hε : 0 < C.support 0) : False := by
  let k := n/2
  let w : Fin C.atomCount → ℝ :=
    fun i => C.weight i * (1-C.compactFrequency i)^n
  let t : Fin C.atomCount → ℝ :=
    fun i => C.compactFrequency i /
      (1-C.compactFrequency i)
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  have hk : 0 < k := by dsimp [k]; omega
  have hfinite := C.positive_leading_atoms_finite
    ha0 hb0 hε
  have htiff (i : Fin C.atomCount) :
      0 < t i ↔ 0 < C.compactFrequency i := by
    dsimp [t]
    exact (div_pos_iff_of_pos_right
      (sub_pos.mpr (hfinite i)))
  have hindices :
      (Finset.univ.filter (fun i : Fin C.atomCount => 0 < t i)) =
        C.positiveFiniteIndices := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and, PaperCriticalCertificate.positiveFiniteIndices]
    exact ⟨fun h => ⟨(htiff i).mp h, hfinite i⟩,
      fun h => (htiff i).mpr h.1⟩
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hcard :
      ((Finset.univ.filter (fun i : Fin C.atomCount => 0 < t i)).image t).card
        ≤ 2*k := by
    simpa [hindices, PaperCriticalCertificate.positiveFiniteNodes,
      t, k] using hmax.le
  have hsne :
      (Finset.univ.filter (fun i : Fin C.atomCount => 0 < t i)).Nonempty := by
    obtain ⟨r, hr⟩ := C.positiveFiniteNodes_nonempty
      (by omega : 0 < n) ha0 hb0 hstableA hstableB
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hr
    exact ⟨i, by simpa [←hindices] using hi⟩
  have htnonneg : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      0 ≤ t i := by
    intro i _
    exact div_nonneg (C.frequency_mem i).1
      (sub_pos.mpr (hfinite i)).le
  have hwpos : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      0 < w i := by
    intro i _
    exact mul_pos (C.weight_pos i)
      (pow_pos (sub_pos.mpr (hfinite i)) n)
  have hsegment' : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k+1) a b q) := by
    rw [←hodd]
    exact hsegment
  have hPzero :
      (paperDescendingNumerator (2*k+1) x +
        Polynomial.C ε * Polynomial.X^(2*k+1)).eval 0 = 0 := by
    rw [←hodd]
    exact C.maximal_positive_leading_support_zero_at_origin
      (by omega : 2 ≤ n) ha0 hb0 hsegment hmax hε
  have hPdivstable : paperPolynomialHurwitz
      (paperDescendingNumerator (2*k+1) x +
        Polynomial.C ε * Polynomial.X^(2*k+1)).divX := by
    rw [←hodd]
    exact C.maximal_odd_positive_leading_support_divX_hurwitz
      (by omega : 2 ≤ n) ha0 hb0 hsegment hodd hmax hε
  have hbalance : ∀ r : Fin (2*k+1),
      (∑ i ∈ Finset.univ, w i *
        (paperGeneralCrossPolynomial (2*k+1)
          (if C.rightEndpoint i then b else a)
          (paperFiniteNumeratorCoeffs (2*k+1)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0 := by
    have hb := (C.ordinary_coefficient_balance_of_atoms_finite
      hfinite).2
    rw [←hodd]
    intro r
    simpa [w, t] using hb r
  have hcontact : ∀ i ∈
      (Finset.univ.filter (fun i : Fin C.atomCount => 0 < t i)),
      (paperRaisedCrossPolynomial (2*k+1)
        (if C.rightEndpoint i then b else a)
        x ε).eval (t i) = 0 := by
    intro i hi
    have hupos : 0 < C.compactFrequency i :=
      (htiff i).mp (Finset.mem_filter.mp hi).2
    rw [←hodd]
    simpa [x, ε, t] using
      (C.positive_contact_root_and_deriv
        i hupos (hfinite i)).1
  exact paperNoOddGroupedCertificate_with_zero
    Finset.univ k hk a b ha0 hb0 C.rightEndpoint
    w t x ε hε hcard hsne htnonneg hwpos
    hsegment' hPzero hPdivstable hbalance hcontact



theorem paperEvenSaturated_cross_eval_zero_pos
    (q : Polynomial ℝ) (k : ℕ)
    (hq : q ≠ 0)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ q.eval t)
    (hdegree : q.natDegree ≤ 2*k)
    (hroots : (MonicQuinticCoeff.positiveRealRoots q).card = k) :
    0 < q.eval 0 := by
  have hlow : 2*k ≤ q.natDegree := by
    have h := MonicQuinticCoeff.twice_card_positiveRealRoots_le_natDegree
      q hq hnonneg
    simpa [hroots] using h
  have hsat : 2 * (MonicQuinticCoeff.positiveRealRoots q).card =
      q.natDegree := by
    omega
  obtain ⟨_, _, hrootset⟩ :=
    MonicQuinticCoeff.saturated_positive_roots_structure
      q hq hnonneg hsat
  have hqzero : q.eval 0 ≠ 0 := by
    intro hz
    have hroot : (0 : ℝ) ∈ q.roots.toFinset := by
      apply Multiset.mem_toFinset.mpr
      exact (Polynomial.mem_roots hq).mpr
        (by simpa [Polynomial.IsRoot] using hz)
    rw [hrootset] at hroot
    exact (not_lt_of_ge (le_refl (0 : ℝ)))
      (Finset.mem_filter.mp hroot).2
  exact lt_of_le_of_ne (hnonneg 0 le_rfl) (Ne.symm hqzero)

theorem PaperCriticalCertificate.maximal_odd_zero_leading_support_eval_zero_pos
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn3 : 3 ≤ n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hodd : n = 2*(n/2)+1)
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (hεzero : C.support 0 = 0) :
    0 < (paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ)) +
      Polynomial.C (C.support 0) * Polynomial.X^n).eval 0 := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let qA := paperRaisedCrossPolynomial n a x ε
  have hn : 0 < n := by omega
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hstructure := C.maximal_positiveFiniteNodes_structure
    hn ha0 hb0 hstableA hstableB hmax
  have hroots : (MonicQuinticCoeff.positiveRealRoots qA).card = n/2 := by
    simpa [qA, x, ε] using hstructure.1
  have hqne : qA ≠ 0 :=
    paperRaisedCrossPolynomial_ne_zero_of_hurwitz
      n hn a ha0 hstableA C.support C.support_ne
  have hqnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ qA.eval t :=
    paperFeature_nonneg_cross_nonneg
      n a C.support C.support_nonneg_left
  have hqdeg : qA.natDegree ≤ 2*(n/2) := by
    have h := paperRaisedCrossPolynomial_natDegree_le_pred_of_top_zero
      n hn a x ε ha0 hεzero
    change qA.natDegree ≤ n-1 at h
    omega
  have hqpos : 0 < qA.eval 0 :=
    paperEvenSaturated_cross_eval_zero_pos
      qA (n/2) hqne hqnonneg hqdeg hroots
  have hdenpos : 0 < a n :=
    paperDescendingDenominator_const_pos_of_hurwitz
      n hn a ha0 hstableA
  have hxpos : 0 < x (n-1) := by
    have hq0 := paperRaisedCrossPolynomial_eval_zero n hn a x ε
    change qA.eval 0 = a n * x (n-1) at hq0
    rw [hq0] at hqpos
    exact (mul_pos_iff_of_pos_left hdenpos).mp hqpos
  simpa [x, ε, paperRaisedNumerator_eval_zero n hn] using hxpos

theorem PaperCriticalCertificate.maximal_odd_zero_leading_atoms_positive_frequency
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn3 : 3 ≤ n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hodd : n = 2*(n/2)+1)
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (hεzero : C.support 0 = 0) :
    ∀ i : Fin C.atomCount, 0 < C.compactFrequency i := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  have hP0 := C.maximal_odd_zero_leading_support_eval_zero_pos
    hn3 ha0 hb0 hsegment hodd hmax hεzero
  have hxpos : 0 < x (n-1) := by
    simpa [x, ε, paperRaisedNumerator_eval_zero n (by omega)]
      using hP0
  intro i
  let d : ℕ → ℝ := if C.rightEndpoint i then b else a
  have hd0 : d 0 = 1 := by
    cases h : C.rightEndpoint i <;> simp [d, h, ha0, hb0]
  have hstableD : paperPolynomialHurwitz
      (paperDescendingDenominator n d) := by
    cases h : C.rightEndpoint i
    · simpa [d, h, paperSegmentDenominator] using
        hsegment 0 (by norm_num) (by norm_num)
    · simpa [d, h, paperSegmentDenominator] using
        hsegment 1 (by norm_num) (by norm_num)
  have hdconst : 0 < d n :=
    paperDescendingDenominator_const_pos_of_hurwitz
      n (by omega) d hd0 hstableD
  have hpairzero : 0 < paperFeatureDot C.support
      (paperCompactFeature n d 0) := by
    rw [paperFeatureDot_compactFeature,
      paperHomogenizedPolynomial_zero,
      Polynomial.coeff_zero_eq_eval_zero]
    change 0 < (paperRaisedCrossPolynomial n d x ε).eval 0
    rw [paperRaisedCrossPolynomial_eval_zero n (by omega) d x ε]
    exact mul_pos hdconst hxpos
  have hzero : paperFeatureDot C.support
      (paperCompactFeature n d (C.compactFrequency i)) = 0 := by
    simpa [d] using C.support_zero_atom i
  have hu := (C.frequency_mem i).1
  rcases hu.eq_or_lt with hz | hp
  · rw [←hz] at hzero
    exact False.elim ((ne_of_gt hpairzero) hzero)
  · exact hp

theorem paperHurwitz_reflect_of_positive_top
    (p : Polynomial ℝ) (n : ℕ)
    (hdegree : p.natDegree = n)
    (htop : 0 < p.leadingCoeff)
    (hstable : paperPolynomialHurwitz p) :
    paperPolynomialHurwitz (Polynomial.reflect n p) := by
  intro z hzre hroot
  by_cases hz0 : z = 0
  · subst z
    have hcoeff : ((Polynomial.reflect n p).coeff 0 : ℂ) = 0 := by
      simpa [Polynomial.aeval_def] using hroot
    rw [Polynomial.coeff_reflect,
      Polynomial.revAt_le (by omega : 0 ≤ n),
      Nat.sub_zero, ←hdegree, Polynomial.coeff_natDegree] at hcoeff
    have hc : ((p.leadingCoeff : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt htop)
    exact hc hcoeff
  · have hinv : 0 ≤ (z⁻¹).re := by
      rw [Complex.inv_re]
      exact div_nonneg hzre (Complex.normSq_nonneg z)
    letI : Invertible (z⁻¹) := invertibleOfNonzero (inv_ne_zero hz0)
    have heq := Polynomial.eval₂_reflect_eq_zero_iff
      (algebraMap ℝ ℂ) (z⁻¹) n p hdegree.le
    have hroot' : Polynomial.aeval (z⁻¹) p = 0 := by
      apply heq.mp
      simpa [Polynomial.aeval_def, invOf_eq_inv] using hroot
    exact (hstable (z⁻¹) hinv) hroot'

theorem paperReflect_natDegree_leadingCoeff
    (p : Polynomial ℝ) (n : ℕ)
    (hdegree : p.natDegree ≤ n)
    (hconst : p.coeff 0 ≠ 0) :
    (Polynomial.reflect n p).natDegree = n ∧
      (Polynomial.reflect n p).leadingCoeff = p.coeff 0 := by
  have hbound : (Polynomial.reflect n p).natDegree ≤ n := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    rw [Polynomial.coeff_reflect,
      Polynomial.revAt_eq_self_of_lt hm]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt hdegree hm)
  have hcoeff : (Polynomial.reflect n p).coeff n = p.coeff 0 := by
    rw [Polynomial.coeff_reflect,
      Polynomial.revAt_le le_rfl, Nat.sub_self]
  have hnat : (Polynomial.reflect n p).natDegree = n :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      hbound (by rw [hcoeff]; exact hconst)
  exact ⟨hnat, by rw [←Polynomial.coeff_natDegree, hnat, hcoeff]⟩

theorem paperPerturbedStable_no_open_right_root_of_leading_lower
    (P D : Polynomial ℝ) (n : ℕ) (ε : ℝ)
    (hε : 0 < ε)
    (hpert : ∀ δ : ℝ, 0 < δ →
      paperPolynomialHurwitz (P + Polynomial.C δ * D) ∧
      (P + Polynomial.C δ * D).natDegree = n ∧
      ε ≤ (P + Polynomial.C δ * D).leadingCoeff)
    (z : ℂ) (hz : 0 < z.re) :
    Polynomial.aeval z P ≠ (0 : ℂ) := by
  intro hzero
  have hpow : 0 < z.re^n := pow_pos hz n
  have hbound (δ : ℝ) (hδ : 0 < δ) :
      ε * z.re^n ≤ δ * ‖(Polynomial.aeval z D : ℂ)‖ := by
    obtain ⟨hstable, hdegree, hlead⟩ := hpert δ hδ
    have hnorm :=
      paperHurwitz_eval_norm_lower_of_leadingCoeff_pos
        (P + Polynomial.C δ * D)
        (lt_of_lt_of_le hε hlead) hstable z hz
    rw [hdegree,
      Polynomial.aeval_add, Polynomial.aeval_mul,
      Polynomial.aeval_C, hzero, zero_add] at hnorm
    change (P + Polynomial.C δ * D).leadingCoeff *
      z.re^n ≤ ‖(δ : ℂ) * Polynomial.aeval z D‖ at hnorm
    have hnorm' : (P + Polynomial.C δ * D).leadingCoeff *
        z.re^n ≤ δ * ‖(Polynomial.aeval z D : ℂ)‖ := by
      simpa [norm_mul, Complex.norm_real, abs_of_pos hδ] using hnorm
    nlinarith [mul_le_mul_of_nonneg_right hlead hpow.le]
  have hnonpos : ε * z.re^n ≤ 0 := by
    refine le_of_forall_pos_le_add (fun η hη => ?_)
    let δ := η / (‖(Polynomial.aeval z D : ℂ)‖ + 1)
    have hδ : 0 < δ := div_pos hη (by positivity)
    have h := hbound δ hδ
    have hδbound : δ * ‖(Polynomial.aeval z D : ℂ)‖ ≤ η := by
      calc
        _ ≤ δ * (‖(Polynomial.aeval z D : ℂ)‖ + 1) := by
          apply mul_le_mul_of_nonneg_left _ hδ.le
          linarith
        _ = η := by
          dsimp [δ]
          field_simp
    linarith
  exact (not_le_of_gt (mul_pos hε hpow)) hnonpos

theorem paperWeakPositiveReal_zero_leading_no_open_right_root
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ)
    (ha0 : a 0 = 1)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hweak : ∀ ω : ℝ,
      0 ≤ ((Polynomial.aeval (jw ω)
        (paperDescendingNumerator n x : Polynomial ℝ) : ℂ) /
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n a)).re)
    (hP0 : 0 < (paperDescendingNumerator n x).eval 0)
    (z : ℂ) (hz : 0 < z.re) :
    Polynomial.aeval z (paperDescendingNumerator n x) ≠ (0 : ℂ) := by
  let P := paperDescendingNumerator n x
  let D := paperDescendingDenominator n a
  let R := Polynomial.reflect n P
  let S := Polynomial.reflect n D
  have hPdeg : P.natDegree ≤ n := by
    have h' := paperDescendingNumerator_natDegree_le n hn x
    exact h'.trans (Nat.pred_le n)
  have hD0 : 0 < D.coeff 0 := by
    have h := paperDescendingDenominator_const_pos_of_hurwitz
      n hn a ha0 hstable
    change 0 < (paperDescendingDenominator n a).coeff 0
    rw [paperDescendingDenominator_coeff,
      if_pos (by omega : 0 ≤ n)]
    simpa using h
  have hPcoeff : 0 < P.coeff 0 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hP0
  have hpert (δ : ℝ) (hδ : 0 < δ) :
      paperPolynomialHurwitz (R + Polynomial.C δ * S) ∧
      (R + Polynomial.C δ * S).natDegree = n ∧
      P.coeff 0 ≤ (R + Polynomial.C δ * S).leadingCoeff := by
    let Pδ := P + Polynomial.C δ * D
    have hδfacts := paperWeakPositiveReal_perturb_hurwitz
      n a x 0 ha0 le_rfl hstable
      (by intro ω; simpa [P] using hweak ω) δ hδ
    have hδstable : paperPolynomialHurwitz Pδ := by
      simpa [Pδ, P, D] using hδfacts.1
    have hδdegree : Pδ.natDegree = n := by
      simpa [Pδ, P, D] using hδfacts.2.1
    have hδlead : Pδ.leadingCoeff = δ := by
      simpa [Pδ, P, D] using hδfacts.2.2
    have hδ0 : 0 < Pδ.coeff 0 := by
      dsimp [Pδ]
      rw [Polynomial.coeff_add, Polynomial.coeff_C_mul]
      exact add_pos hPcoeff (mul_pos hδ hD0)
    have hreflect := paperReflect_natDegree_leadingCoeff
      Pδ n hδdegree.le (ne_of_gt hδ0)
    have hreflectStable : paperPolynomialHurwitz
        (Polynomial.reflect n Pδ) :=
      paperHurwitz_reflect_of_positive_top
        Pδ n hδdegree (by rw [hδlead]; exact hδ) hδstable
    have hId : Polynomial.reflect n Pδ =
        R + Polynomial.C δ * S := by
      simp [Pδ, R, S, Polynomial.reflect_add,
        Polynomial.reflect_C_mul]
    rw [←hId]
    exact ⟨hreflectStable, hreflect.1,
      by rw [hreflect.2];
         dsimp [Pδ];
         rw [Polynomial.coeff_add, Polynomial.coeff_C_mul];
         nlinarith [mul_pos hδ hD0]⟩
  have hRopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z R ≠ (0 : ℂ) := by
    intro w hw
    exact paperPerturbedStable_no_open_right_root_of_leading_lower
      R S n (P.coeff 0) hPcoeff hpert w hw
  have hz0 : z ≠ 0 := by
    intro he
    simp [he] at hz
  have hzinvr : 0 < (z⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hz (Complex.normSq_pos.mpr hz0)
  letI : Invertible z := invertibleOfNonzero hz0
  have heq := Polynomial.eval₂_reflect_eq_zero_iff
    (algebraMap ℝ ℂ) z n P hPdeg
  intro hroot
  have hRroot : Polynomial.aeval (z⁻¹) R = 0 := by
    apply heq.mpr
    simpa [Polynomial.aeval_def] using hroot
  exact (hRopen (z⁻¹) hzinvr) (by
    simpa [R, Polynomial.aeval_def, invOf_eq_inv] using hRroot)

theorem paperPolynomialHurwitz_of_open_and_imag
    (p : Polynomial ℝ)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z p ≠ (0 : ℂ))
    (himag : ∀ ω : ℝ,
      Polynomial.aeval (jw ω) p ≠ (0 : ℂ)) :
    paperPolynomialHurwitz p := by
  intro z hzre
  by_cases hpos : 0 < z.re
  · exact hopen z hpos
  · have hre0 : z.re = 0 := le_antisymm (le_of_not_gt hpos) hzre
    have hzjw : z = jw z.im := by
      apply Complex.ext
      · simp [jw, hre0]
      · simp [jw]
    rw [hzjw]
    exact himag z.im

theorem PaperCriticalCertificate.maximal_odd_zero_leading_support_hurwitz
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn3 : 3 ≤ n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hodd : n = 2*(n/2)+1)
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (hεzero : C.support 0 = 0) :
    paperPolynomialHurwitz
      (paperDescendingNumerator n
        (paperFiniteNumeratorCoeffs n
          (fun j => C.support j.succ))) := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let P := paperDescendingNumerator n x
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hweak := C.support_numerator_weak_re_nonneg
    (by omega : 0 < n) hstableA hstableB
  have hP0 : 0 < P.eval 0 := by
    have h := C.maximal_odd_zero_leading_support_eval_zero_pos
      hn3 ha0 hb0 hsegment hodd hmax hεzero
    simpa [P, x, hεzero] using h
  have hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ) := by
    intro z hz
    exact paperWeakPositiveReal_zero_leading_no_open_right_root
      n (by omega) a x ha0 hstableA
      (fun ω => by simpa [x, hεzero] using (hweak ω).1)
      hP0 z hz
  have himag : ∀ ω : ℝ,
      Polynomial.aeval (jw ω) P ≠ (0 : ℂ) := by
    intro ω
    by_cases hω : ω = 0
    · subst ω
      have hc : ((P.coeff 0 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (by simpa [Polynomial.coeff_zero_eq_eval_zero]
          using (ne_of_gt hP0) : P.coeff 0 ≠ 0)
      simpa [jw, Polynomial.aeval_def] using hc
    · have h := C.support_numerator_imag_ne_zero_of_maximal_contacts
        (by omega : 0 < n) ha0 hb0 hstableA hstableB
        hmax ω hω
      simpa [P, x, hεzero] using h
  exact paperPolynomialHurwitz_of_open_and_imag
    P hopen himag



theorem paperHurwitz_eval_pos_of_eval_zero_pos
    (p : Polynomial ℝ)
    (hstable : paperPolynomialHurwitz p)
    (hzero : 0 < p.eval 0)
    (x : ℝ) (hx : 0 ≤ x) :
    0 < p.eval x := by
  by_contra hnot
  have hpx : p.eval x ≤ 0 := le_of_not_gt hnot
  have hmem : (0 : ℝ) ∈ (fun t : ℝ => p.eval t) '' Set.Icc 0 x :=
    (intermediate_value_Icc' hx p.continuous.continuousOn)
      ⟨hpx, hzero.le⟩
  obtain ⟨t, ht, hroot⟩ := hmem
  have hno := hstable (t : ℂ) (by exact_mod_cast ht.1)
  apply hno
  have hz : ((p.eval t : ℝ) : ℂ) = 0 := by exact_mod_cast hroot
  exact (Polynomial.ofReal_eval (K := ℂ) p t).symm.trans hz

theorem paperPolynomial_leadingCoeff_pos_of_nonneg_on_nonneg
    (p : Polynomial ℝ)
    (hdeg : 0 < p.degree)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ p.eval t) :
    0 < p.leadingCoeff := by
  by_contra hnot
  have hlead : p.leadingCoeff ≤ 0 := le_of_not_gt hnot
  have htend : Filter.Tendsto (fun t : ℝ => p.eval t)
      Filter.atTop Filter.atBot :=
    p.tendsto_atBot_of_leadingCoeff_nonpos hdeg hlead
  have hev : ∀ᶠ t : ℝ in Filter.atTop, p.eval t ≤ -1 :=
    (Filter.tendsto_atBot.1 htend) (-1)
  obtain ⟨t, hneg, ht⟩ :=
    (hev.and (Filter.eventually_ge_atTop (0 : ℝ))).exists
  linarith only [hneg, hnonneg t ht]

theorem paperOddZeroLeading_cross_top_coeff
    (k : ℕ) (hk : 0 < k) (a x : ℕ → ℝ)
    (ha0 : a 0 = 1)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator (2*k+1) a)) :
    (paperRaisedCrossPolynomial (2*k+1) a x 0).coeff (2*k) =
      (paperDescendingNumerator (2*k+1) x).coeff (2*k) * a 1 -
      (paperDescendingNumerator (2*k+1) x).coeff (2*k-1) := by
  let n := 2*k+1
  let P := paperDescendingNumerator n x
  let D := paperDescendingDenominator n a
  let E := paperAxisEven n P
  let O := paperAxisOdd n P
  let F := paperAxisEven n D
  let G := paperAxisOdd n D
  have hpdegree : P.natDegree ≤ 2*k := by
    have h := paperDescendingNumerator_natDegree_le n (by dsimp [n]; omega) x
    simpa [n] using h
  have hddegree : D.natDegree = n :=
    paperDescendingDenominator_natDegree_eq n a ha0
  have hEbound : E.natDegree ≤ k := by
    have h := paperAxisEven_natDegree_le n P
      (hpdegree.trans (by dsimp [n]; omega))
    change E.natDegree ≤ n/2 at h
    dsimp [n] at h
    omega
  have hObound : O.natDegree ≤ k-1 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [paperAxisOdd_coeff]
    by_cases hjn : j ≤ n
    · rw [if_pos hjn]
      have hvanish : P.coeff (2*j+1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (by omega : P.natDegree < 2*j+1)
      simp [hvanish]
    · simp [hjn]
  have hFbound : F.natDegree ≤ k := by
    have h := paperAxisEven_natDegree_le n D hddegree.le
    change F.natDegree ≤ n/2 at h
    dsimp [n] at h
    omega
  have hGbound : G.natDegree ≤ k := by
    have h := paperAxisOdd_natDegree_le n D hddegree.le
    simpa [G, n] using h
  have hId : paperRaisedCrossPolynomial n a x 0 =
      E*F + Polynomial.X*O*G := by
    simpa [P, D, E, O, F, G] using
      (paperRaisedCross_axis_identity_any
        n (by dsimp [n]; omega) a x 0 ha0 hstable)
  have heven : (E*F).coeff (2*k) = E.coeff k * F.coeff k := by
    rw [show 2*k=k+k by omega]
    exact Polynomial.coeff_mul_of_natDegree_le hEbound hFbound
  have hodd : (Polynomial.X*O*G).coeff (2*k) =
      O.coeff (k-1) * G.coeff k := by
    rw [mul_assoc, show 2*k=(2*k-1)+1 by omega,
      Polynomial.coeff_X_mul]
    rw [show 2*k-1=(k-1)+k by omega]
    exact Polynomial.coeff_mul_of_natDegree_le hObound hGbound
  rw [hId, Polynomial.coeff_add, heven, hodd]
  have hE : E.coeff k = P.coeff (2*k) * (-1 : ℝ)^k := by
    rw [paperAxisEven_coeff, if_pos (by dsimp [n]; omega)]
  have hF : F.coeff k = D.coeff (2*k) * (-1 : ℝ)^k := by
    rw [paperAxisEven_coeff, if_pos (by dsimp [n]; omega)]
  have hO : O.coeff (k-1) =
      P.coeff (2*k-1) * (-1 : ℝ)^(k-1) := by
    rw [paperAxisOdd_coeff, if_pos (by dsimp [n]; omega),
      show 2*(k-1)+1 = 2*k-1 by omega]
  have hG : G.coeff k = D.coeff (2*k+1) * (-1 : ℝ)^k := by
    rw [paperAxisOdd_coeff, if_pos (by dsimp [n]; omega)]
  rw [hE, hF, hO, hG]
  have hdnext : D.coeff (2*k) = a 1 := by
    rw [paperDescendingDenominator_coeff,
      if_pos (by dsimp [n]; omega)]
    simp [n]
  have hdtop : D.coeff (2*k+1) = 1 := by
    rw [paperDescendingDenominator_coeff,
      if_pos (by dsimp [n]; omega)]
    simpa [n] using ha0
  rw [hdnext, hdtop]
  have hs1 : (-1 : ℝ)^k * (-1 : ℝ)^k = 1 := by
    rw [←pow_add, show k+k = 2*k by omega, pow_mul]
    norm_num
  have hs2 : (-1 : ℝ)^(k-1) * (-1 : ℝ)^k = -1 := by
    rw [←pow_add, show (k-1)+k=2*(k-1)+1 by omega,
      pow_add, pow_mul]
    norm_num
  change P.coeff (2*k) * (-1 : ℝ)^k *
      (a 1 * (-1 : ℝ)^k) +
      (P.coeff (2*k-1) * (-1 : ℝ)^(k-1)) *
      (1 * (-1 : ℝ)^k) =
      P.coeff (2*k) * a 1 - P.coeff (2*k-1)
  calc
    _ = P.coeff (2*k) * a 1 *
          ((-1 : ℝ)^k * (-1 : ℝ)^k) +
        P.coeff (2*k-1) *
          ((-1 : ℝ)^(k-1) * (-1 : ℝ)^k) := by ring
    _ = _ := by rw [hs1, hs2]; ring

theorem PaperCriticalCertificate.maximal_odd_zero_leading_support_degree
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn3 : 3 ≤ n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hodd : n = 2*(n/2)+1)
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (hεzero : C.support 0 = 0) :
    let P := paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ))
    P.natDegree = n-1 ∧ 0 < P.leadingCoeff := by
  dsimp
  let k := n/2
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let P := paperDescendingNumerator n x
  let qA := paperRaisedCrossPolynomial n a x 0
  have hk : 0 < k := by dsimp [k]; omega
  have hn : 0 < n := by omega
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hstructure := C.maximal_positiveFiniteNodes_structure
    hn ha0 hb0 hstableA hstableB hmax
  have hqroots : (MonicQuinticCoeff.positiveRealRoots qA).card = k := by
    simpa [qA, x, k, hεzero] using hstructure.1
  have hqne : qA ≠ 0 := by
    simpa [qA, hεzero] using
      (paperRaisedCrossPolynomial_ne_zero_of_hurwitz
        n hn a ha0 hstableA C.support C.support_ne)
  have hqnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ qA.eval t := by
    intro t ht
    simpa [qA, hεzero] using
      (paperFeature_nonneg_cross_nonneg
        n a C.support C.support_nonneg_left t ht)
  have hqdegupper : qA.natDegree ≤ 2*k := by
    have h := paperRaisedCrossPolynomial_natDegree_le_pred_of_top_zero
      n hn a x 0 ha0 (by simp)
    change qA.natDegree ≤ n-1 at h
    omega
  have hqdeglower : 2*k ≤ qA.natDegree := by
    have h := MonicQuinticCoeff.twice_card_positiveRealRoots_le_natDegree
      qA hqne hqnonneg
    simpa [hqroots] using h
  have hqdegree : qA.natDegree = 2*k := by omega
  have hqdegpos : 0 < qA.degree := by
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    rw [hqdegree]
    omega
  have hqleadpos : 0 < qA.leadingCoeff :=
    paperPolynomial_leadingCoeff_pos_of_nonneg_on_nonneg
      qA hqdegpos hqnonneg
  have hqtoppos : 0 < qA.coeff (2*k) := by
    rw [←hqdegree, Polynomial.coeff_natDegree]
    exact hqleadpos
  have hPdegreeupper : P.natDegree ≤ 2*k := by
    have h := paperDescendingNumerator_natDegree_le n hn x
    change P.natDegree ≤ n-1 at h
    omega
  have hP0 : 0 < P.eval 0 := by
    have h := C.maximal_odd_zero_leading_support_eval_zero_pos
      hn3 ha0 hb0 hsegment hodd hmax hεzero
    simpa [P, x, hεzero] using h
  have hPstable : paperPolynomialHurwitz P := by
    exact C.maximal_odd_zero_leading_support_hurwitz
      hn3 ha0 hb0 hsegment hodd hmax hεzero
  have hPpos : ∀ t : ℝ, 0 ≤ t → 0 < P.eval t :=
    paperHurwitz_eval_pos_of_eval_zero_pos P hPstable hP0
  have htopformula : qA.coeff (2*k) =
      P.coeff (2*k) * a 1 - P.coeff (2*k-1) := by
    have hkn : n = 2*k+1 := by simpa only [k] using hodd
    have hstableA' : paperPolynomialHurwitz
        (paperDescendingDenominator (2*k+1) a) := by
      simpa only [← hkn] using hstableA
    simpa only [← hkn, qA, P] using
      (paperOddZeroLeading_cross_top_coeff
        k hk a x ha0 hstableA')
  have hPtopne : P.coeff (2*k) ≠ 0 := by
    intro htopzero
    have hPdegreePred : P.natDegree ≤ 2*k-1 := by
      apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro m hm
      by_cases heq : m = 2*k
      · simpa [heq] using htopzero
      · have hgt : 2*k < m := by omega
        exact Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt hPdegreeupper hgt)
    have hPnextneg : P.coeff (2*k-1) < 0 := by
      rw [htopzero, zero_mul, zero_sub] at htopformula
      linarith
    have hPnextne : P.coeff (2*k-1) ≠ 0 := ne_of_lt hPnextneg
    have hPdegreePredEq : P.natDegree = 2*k-1 :=
      Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
        hPdegreePred hPnextne
    have hPdegreepos : 0 < P.degree := by
      apply Polynomial.natDegree_pos_iff_degree_pos.mp
      rw [hPdegreePredEq]
      omega
    have hPleadpos : 0 < P.leadingCoeff :=
      polynomial_leadingCoeff_pos_of_pos_on_nonneg
        P hPdegreepos hPpos
    rw [←Polynomial.coeff_natDegree, hPdegreePredEq] at hPleadpos
    linarith
  have hPdegree : P.natDegree = 2*k :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      hPdegreeupper hPtopne
  have hPdegreepos : 0 < P.degree := by
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    rw [hPdegree]
    omega
  have hPleadpos : 0 < P.leadingCoeff :=
    polynomial_leadingCoeff_pos_of_pos_on_nonneg
      P hPdegreepos hPpos
  have hnk : n-1 = 2*k := by dsimp [k]; omega
  exact ⟨by rw [hnk]; exact hPdegree, hPleadpos⟩



theorem PaperCriticalCertificate.finite_coefficient_balance_with_infinity
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    ∀ j : Fin n,
      (∑ i : Fin C.atomCount,
        C.weight i * (1-C.compactFrequency i)^n *
          (paperGeneralCrossPolynomial n
            (if C.rightEndpoint i then b else a)
            (paperFiniteNumeratorCoeffs n
              (fun k => if j = k then 1 else 0))).eval
                (C.compactFrequency i /
                  (1-C.compactFrequency i))) = 0 := by
  intro j
  have hcoord :
      (∑ i : Fin C.atomCount, C.weight i *
        (paperCompactFeature n
          (if C.rightEndpoint i then b else a)
          (C.compactFrequency i)) j.succ) = 0 := by
    have h := congrArg (fun v : Fin (n+1) → ℝ => v j.succ) C.balance
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] using h
  calc
    _ = ∑ i : Fin C.atomCount, C.weight i *
        (paperCompactFeature n
          (if C.rightEndpoint i then b else a)
          (C.compactFrequency i)) j.succ := by
      apply Finset.sum_congr rfl
      intro i _
      let d : ℕ → ℝ := if C.rightEndpoint i then b else a
      have hd0 : d 0 = 1 := by
        cases h : C.rightEndpoint i <;> simp [d, h, ha0, hb0]
      by_cases hi : C.compactFrequency i = 1
      · rw [hi]
        have hj : j.succ ≠ (0 : Fin (n+1)) := Fin.succ_ne_zero j
        simp [paperCompactFeature_one n d hd0, d, hn.ne',
          Pi.single_apply, hj]
      · rw [paperCompactFeature_eq_scaledOrdinary n d _ hi]
        simp only [paperOrdinaryFeature, Fin.cons_succ, Pi.smul_apply,
          smul_eq_mul]
        ring
    _ = 0 := hcoord

theorem paperNoOddZeroLeadingGroupedCertificate_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) (hk : 0 < k)
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (side : ι → Bool) (w t : ι → ℝ)
    (x : ℕ → ℝ)
    (hcard : (s.image t).card ≤ 2*k)
    (hsne : s.Nonempty)
    (htpos : ∀ i ∈ s, 0 < t i)
    (hwpos : ∀ i ∈ s, 0 < w i)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k+1) a b q))
    (hPdegree : (paperDescendingNumerator (2*k+1) x).natDegree = 2*k)
    (hPstable : paperPolynomialHurwitz
      (paperDescendingNumerator (2*k+1) x))
    (hbalance : ∀ r : Fin (2*k+1),
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial (2*k+1)
          (if side i then b else a)
          (paperFiniteNumeratorCoeffs (2*k+1)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0)
    (hcontact : ∀ i ∈ s,
      (paperRaisedCrossPolynomial (2*k+1)
        (if side i then b else a) x 0).eval (t i) = 0) :
    False := by
  let n := 2*k+1
  let d : ι → ℕ → ℝ := fun i =>
    if side i then b else a
  let P := paperDescendingNumerator n x
  let E := paperAxisEven n P
  let O := paperAxisOdd n P
  let z : ι → ℝ := fun i =>
    w i * (paperAxisEven n
      (paperDescendingDenominator n (d i))).eval (t i)
  let y : ι → ℝ := fun i =>
    w i * t i * (paperAxisOdd n
      (paperDescendingDenominator n (d i))).eval (t i)
  have hn : 0 < n := by dsimp [n]; omega
  have hmonic : ∀ i ∈ s, d i 0 = 1 := by
    intro i hi
    by_cases h : side i
    · simp [d, h, hb0]
    · simp [d, h, ha0]
  have hstable : ∀ i ∈ s,
      paperPolynomialHurwitz
        (paperDescendingDenominator n (d i)) := by
    intro i hi
    by_cases h : side i
    · simpa [d, h, paperSegmentDenominator] using
        (hsegment 1 (by norm_num) (by norm_num))
    · simpa [d, h, paperSegmentDenominator] using
        (hsegment 0 (by norm_num) (by norm_num))
  have hpdegree : P.natDegree = 2*k := hPdegree
  have hPdegreele : P.natDegree ≤ n := by dsimp [n] at *; omega
  have hEbound : E.natDegree ≤ k := by
    have h := paperAxisEven_natDegree_le n P hPdegreele
    change E.natDegree ≤ n/2 at h
    dsimp [n] at h
    omega
  have hEcoeff : E.coeff k = P.leadingCoeff * (-1 : ℝ)^k := by
    change (paperAxisEven n P).coeff k = P.leadingCoeff * (-1 : ℝ)^k
    rw [paperAxisEven_coeff, if_pos (by dsimp [n]; omega),
      show 2*k = P.natDegree by rw [hpdegree]]
    rw [Polynomial.coeff_natDegree]
  have hPne : P ≠ 0 := by
    intro h
    simp [h] at hpdegree
    omega
  have hEcoe : E.coeff k ≠ 0 := by
    rw [hEcoeff]
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hPne)
      (pow_ne_zero _ (by norm_num))
  have hEnat : E.natDegree = k :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      hEbound hEcoe
  have hEdegree : E.degree = (k : WithBot ℕ) := by
    have hEne : E ≠ 0 := by
      intro he
      simp [he] at hEcoe
    rw [Polynomial.degree_eq_natDegree hEne, hEnat]
  have hObound : O.natDegree ≤ k := by
    have h := paperAxisOdd_natDegree_le n P hPdegreele
    change O.natDegree ≤ (n-1)/2 at h
    have hdiv : (n-1)/2 ≤ k := by dsimp [n]; omega
    exact h.trans hdiv
  have hOdegree : O.degree ≤ (k : WithBot ℕ) := by
    by_cases hOzero : O = 0
    · simp [hOzero]
    · rw [Polynomial.degree_eq_natDegree hOzero]
      exact_mod_cast hObound
  have hcop : IsCoprime E O := by
    exact paperAxisEvenOdd_coprime n P hPdegreele hPstable
  have hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0 := by
    intro j hj
    have hsmall : 2*j < n := by dsimp [n]; omega
    exact paperCoefficientBalance_even_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0 := by
    intro j hj
    have hsmall : 2*j+1 < n := by dsimp [n]; omega
    exact paperCoefficientBalance_odd_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hc : ∀ i ∈ s,
      E.eval (t i) * z i + O.eval (t i) * y i = 0 := by
    intro i hi
    have hid := paperRaisedCross_axis_identity_any
      n hn (d i) x 0 (hmonic i hi) (hstable i hi)
    have hzero := hcontact i hi
    rw [hid] at hzero
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] at hzero
    simp only [Polynomial.C_0, zero_mul, add_zero] at hzero
    calc
      E.eval (t i) * z i + O.eval (t i) * y i =
          w i * ((paperAxisEven n P).eval (t i) *
            (paperAxisEven n
              (paperDescendingDenominator n (d i))).eval (t i) +
            t i * (paperAxisOdd n P).eval (t i) *
              (paperAxisOdd n
                (paperDescendingDenominator n (d i))).eval (t i)) := by
          dsimp [E, O, z, y]
          ring
      _ = 0 := by
          rw [show P = paperDescendingNumerator n x from rfl, hzero]
          ring
  have hnode : ∃ r ∈ s.image t,
      paperGroupedResidue s t z r ≠ 0 ∨
        paperGroupedResidue s t y r ≠ 0 := by
    obtain ⟨i, hi⟩ := hsne
    have hr : t i ∈ s.image t :=
      Finset.mem_image.mpr ⟨i, hi, rfl⟩
    refine ⟨t i, hr, ?_⟩
    simpa [z, y, d] using
      (paperGroupedAxisResidue_nontrivial
        n a b ha0 hb0 s t w side htpos hwpos
        hsegment (t i) hr)
  exact paperContactResidue_no_grouped_even_balance
    s t z y E O k hcard hEdegree hOdegree hcop
    hz hy hc hnode

theorem PaperCriticalCertificate.no_maximal_odd_zero_leading_certificate
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn3 : 3 ≤ n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hodd : n = 2*(n/2)+1)
    (hmax : C.positiveFiniteNodes.card = 2*(n/2))
    (hεzero : C.support 0 = 0) : False := by
  let k := n/2
  let s := C.positiveFiniteIndices
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let t : Fin C.atomCount → ℝ := fun i =>
    C.compactFrequency i / (1-C.compactFrequency i)
  let w : Fin C.atomCount → ℝ := fun i =>
    C.weight i * (1-C.compactFrequency i)^n
  have hk : 0 < k := by dsimp [k]; omega
  have hupos : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i :=
    C.maximal_odd_zero_leading_atoms_positive_frequency
      hn3 ha0 hb0 hsegment hodd hmax hεzero
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hcard : (s.image t).card ≤ 2*k := by
    simpa [s, PaperCriticalCertificate.positiveFiniteNodes, t, k]
      using hmax.le
  have hsne : s.Nonempty := by
    obtain ⟨r, hr⟩ := C.positiveFiniteNodes_nonempty
      (by omega : 0 < n) ha0 hb0 hstableA hstableB
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hr
    exact ⟨i, hi⟩
  have htpos : ∀ i ∈ s, 0 < t i := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2.2
    exact div_pos (hupos i) (sub_pos.mpr hi')
  have hwpos : ∀ i ∈ s, 0 < w i := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2.2
    exact mul_pos (C.weight_pos i)
      (pow_pos (sub_pos.mpr hi') n)
  have hsegment' : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k+1) a b q) := by
    rw [←hodd]
    exact hsegment
  have hPdegree :
      (paperDescendingNumerator (2*k+1) x).natDegree = 2*k := by
    have h := (C.maximal_odd_zero_leading_support_degree
      hn3 ha0 hb0 hsegment hodd hmax hεzero).1
    rw [←hodd]
    have hnk : n-1 = 2*k := by dsimp [k]; omega
    simpa only [x, hnk] using h
  have hPstable : paperPolynomialHurwitz
      (paperDescendingNumerator (2*k+1) x) := by
    rw [←hodd]
    exact C.maximal_odd_zero_leading_support_hurwitz
      hn3 ha0 hb0 hsegment hodd hmax hεzero
  have hbalance : ∀ r : Fin (2*k+1),
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial (2*k+1)
          (if C.rightEndpoint i then b else a)
          (paperFiniteNumeratorCoeffs (2*k+1)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0 := by
    rw [←hodd]
    intro r
    have hb := C.finite_coefficient_balance_with_infinity
      (by omega : 0 < n) ha0 hb0 r
    calc
      _ = ∑ i : Fin C.atomCount, w i *
          (paperGeneralCrossPolynomial n
            (if C.rightEndpoint i then b else a)
            (paperFiniteNumeratorCoeffs n
              (fun j => if r = j then 1 else 0))).eval (t i) := by
        change (∑ i ∈ Finset.univ.filter
          (fun i : Fin C.atomCount =>
            0 < C.compactFrequency i ∧ C.compactFrequency i < 1),
          w i *
            (paperGeneralCrossPolynomial n
              (if C.rightEndpoint i then b else a)
              (paperFiniteNumeratorCoeffs n
                (fun j => if r = j then 1 else 0))).eval (t i)) = _
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : 0 < C.compactFrequency i ∧
            C.compactFrequency i < 1
        · simp [hi]
        · have hu1 : C.compactFrequency i = 1 := by
            have hle := (C.frequency_mem i).2
            have hnot : ¬ C.compactFrequency i < 1 := by
              intro hlt
              exact hi ⟨hupos i, hlt⟩
            exact le_antisymm hle (le_of_not_gt hnot)
          have hn0 : n ≠ 0 := by omega
          have hwzero : w i = 0 := by simp [w, hu1, hn0]
          simp [hi, hwzero]
      _ = 0 := by simpa [w, t] using hb
  have hcontact : ∀ i ∈ s,
      (paperRaisedCrossPolynomial (2*k+1)
        (if C.rightEndpoint i then b else a)
        x 0).eval (t i) = 0 := by
    intro i hi
    have hfinite := (Finset.mem_filter.mp hi).2.2
    rw [←hodd]
    simpa [x, t, hεzero] using
      (C.positive_contact_root_and_deriv
        i (hupos i) hfinite).1
  exact paperNoOddZeroLeadingGroupedCertificate_le
    s k hk a b ha0 hb0 C.rightEndpoint w t x
    hcard hsne htpos hwpos hsegment' hPdegree
    hPstable hbalance hcontact



/-- Maximal positive contact count is impossible for a stable segment. -/
theorem PaperCriticalCertificate.no_maximal_contacts
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn3 : 3 ≤ n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hmax : C.positiveFiniteNodes.card = 2*(n/2)) : False := by
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hparity : n = 2*(n/2) ∨ n = 2*(n/2)+1 := by omega
  rcases hparity with heven | hodd
  · exact C.no_maximal_even_contacts
      (by omega) ha0 hb0 hstableA hstableB hmax heven
  · have hε := C.support_leading_nonneg ha0
    rcases hε.eq_or_lt with hzero | hpos
    · exact C.no_maximal_odd_zero_leading_certificate
        hn3 ha0 hb0 hsegment hodd hmax hzero.symm
    · exact C.no_maximal_odd_positive_leading
        hn3 ha0 hb0 hsegment hodd hmax hpos

theorem PaperCriticalCertificate.positiveFiniteNodes_card_lt_even_part
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn3 : 3 ≤ n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q)) :
    C.positiveFiniteNodes.card < 2*(n/2) := by
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hle := C.positiveFiniteNodes_card_le_even_part
    (by omega : 0 < n) ha0 hb0 hstableA hstableB
  have hne : C.positiveFiniteNodes.card ≠ 2*(n/2) := by
    intro h
    exact C.no_maximal_contacts hn3 ha0 hb0 hsegment h
  omega

/-- Any still possible critical certificate has an intermediate number of
distinct positive finite contacts. -/
theorem PaperCriticalCertificate.remaining_contact_range
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn3 : 3 ≤ n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q)) :
    n/2 < C.positiveFiniteNodes.card ∧
      C.positiveFiniteNodes.card < 2*(n/2) := by
  have hmany : n < 2*C.positiveFiniteNodes.card := by
    apply C.low_contact_excluded (by omega) ha0 hb0
    simpa [paperSegmentDenominator] using hsegment
  have hfew := C.positiveFiniteNodes_card_lt_even_part
    hn3 ha0 hb0 hsegment
  omega



/-- A zero leading support coefficient lowers each endpoint root budget. -/
theorem PaperCriticalCertificate.positiveFiniteNodes_card_le_twice_half_pred_of_leading_zero
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hzero : C.support 0 = 0) :
    C.positiveFiniteNodes.card ≤ 2*((n-1)/2) := by
  let rootsA := MonicQuinticCoeff.positiveRealRoots
    (paperRaisedCrossPolynomial n a
      (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
      (C.support 0))
  let rootsB := MonicQuinticCoeff.positiveRealRoots
    (paperRaisedCrossPolynomial n b
      (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
      (C.support 0))
  have hsub : C.positiveFiniteNodes ⊆ rootsA ∪ rootsB :=
    C.positiveFiniteNodes_subset_endpoint_roots
      hn ha0 hb0 hstableA hstableB
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le rootsA rootsB
  have hbound := C.endpoint_positiveRoots_bounds_of_leading_zero
    hn ha0 hb0 hstableA hstableB hzero
  change 2*rootsA.card ≤ n-1 ∧ 2*rootsB.card ≤ n-1 at hbound
  omega

theorem PaperCriticalCertificate.even_zero_leading_card_le_two_below
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (heven : n = 2*(n/2))
    (hzero : C.support 0 = 0) :
    C.positiveFiniteNodes.card ≤ n-2 := by
  have h := C.positiveFiniteNodes_card_le_twice_half_pred_of_leading_zero
    hn ha0 hb0 hstableA hstableB hzero
  omega



/-- A nontrivial moment/contact residue forces a sufficiently large common
factor of the real and imaginary numerator components. -/
theorem paperContactResidue_gcd_degree_gap
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z y : ι → ℝ)
    (ht : Set.InjOn t s) (E O : Polynomial ℝ) (k : ℕ)
    (hEdegree : E.degree = (k : WithBot ℕ))
    (hOdegree : O.degree ≤ k)
    (hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0)
    (hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0)
    (hc : ∀ i ∈ s, E.eval (t i) * z i +
      O.eval (t i) * y i = 0)
    (hnode : ∃ i ∈ s, z i ≠ 0 ∨ y i ≠ 0) :
    2*k < s.card + (GCDMonoid.gcd O E).natDegree := by
  classical
  let U := MonicQuinticCoeff.quinticResiduePolynomial s t z
  let V := MonicQuinticCoeff.quinticResiduePolynomial s t y
  let G := GCDMonoid.gcd O E
  let E' := E / G
  let O' := O / G
  have hEne : E ≠ 0 := by
    intro he
    simp [he] at hEdegree
  have hGne : G ≠ 0 := gcd_ne_zero_of_right hEne
  have hE'ne : E' ≠ 0 := right_div_gcd_ne_zero hEne
  have hEfactor : G * E' = E := by
    simpa [G, E'] using
      (EuclideanDomain.mul_div_cancel' hGne
        (GCDMonoid.gcd_dvd_right O E))
  have hOfactor : G * O' = O := by
    simpa [G, O'] using
      (EuclideanDomain.mul_div_cancel' hGne
        (GCDMonoid.gcd_dvd_left O E))
  have hcop : IsCoprime E' O' := by
    simpa [E', O', G] using
      (isCoprime_div_gcd_div_gcd (p := O) (q := E) hEne).symm
  have hid : E*U+O*V=0 :=
    paperContactResiduePolynomial_identity s t z y ht E O k
      hEdegree.le hOdegree hz hy hc
  have hid' : E'*U+O'*V=0 := by
    have h : G * (E'*U+O'*V) = 0 := by
      calc
        _ = E*U+O*V := by rw [←hEfactor, ←hOfactor]; ring
        _ = 0 := hid
    exact (mul_eq_zero.mp h).resolve_left hGne
  have hdiv : E' ∣ V := by
    have h : E' ∣ O'*V := by
      refine ⟨-U, ?_⟩
      calc
        O'*V = -(E'*U) := by linear_combination hid'
        _ = E'*(-U) := by ring
    exact hcop.dvd_of_dvd_mul_left h
  have hVne : V ≠ 0 := by
    intro hVzero
    rw [hVzero, mul_zero, add_zero] at hid
    have hUzero : U = 0 :=
      (mul_eq_zero.mp hid).resolve_left hEne
    exact (paperContactResidue_nontrivial s t z y ht hnode).elim
      (fun h => h hUzero) (fun h => h hVzero)
  have hVbound := MonicQuinticCoeff.degree_quinticResiduePolynomial_of_moments
    s t y k hy
  change V.degree + k < (s.card : WithBot ℕ) at hVbound
  have hVnat : V.natDegree + k < s.card := by
    rw [Polynomial.degree_eq_natDegree hVne] at hVbound
    exact_mod_cast hVbound
  have hEnat : E.natDegree = k := by
    rw [Polynomial.degree_eq_natDegree hEne] at hEdegree
    exact_mod_cast hEdegree
  have hfactorDegree : G.natDegree + E'.natDegree = k := by
    rw [← Polynomial.natDegree_mul hGne hE'ne, hEfactor]
    exact hEnat
  have hE'leV : E'.natDegree ≤ V.natDegree :=
    Polynomial.natDegree_le_of_dvd hdiv hVne
  change 2*k < s.card + G.natDegree
  omega

theorem paperContactResidue_grouped_gcd_degree_gap
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z y : ι → ℝ)
    (E O : Polynomial ℝ) (k : ℕ)
    (hEdegree : E.degree = (k : WithBot ℕ))
    (hOdegree : O.degree ≤ k)
    (hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0)
    (hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0)
    (hc : ∀ i ∈ s, E.eval (t i) * z i +
      O.eval (t i) * y i = 0)
    (hnode : ∃ r ∈ s.image t,
      paperGroupedResidue s t z r ≠ 0 ∨
        paperGroupedResidue s t y r ≠ 0) :
    2*k < (s.image t).card + (GCDMonoid.gcd O E).natDegree := by
  classical
  let u : ℝ → ℝ := paperGroupedResidue s t z
  let v : ℝ → ℝ := paperGroupedResidue s t y
  apply paperContactResidue_gcd_degree_gap
    (s.image t) id u v
    (by intro r _ q _ h; exact h)
    E O k hEdegree hOdegree
  · intro j hj
    simpa [u] using
      (paperGroupedResidue_moment s t z j).trans (hz j hj)
  · intro j hj
    simpa [v] using
      (paperGroupedResidue_moment s t y j).trans (hy j hj)
  · intro r hr
    exact paperGroupedResidue_contact s t z y E O hc r
  · exact hnode

/-- A root-count bound on the common factor closes the grouped residue
obstruction, even when the parity polynomials are not coprime. -/
theorem paperContactResidue_no_grouped_balance_of_gcd_budget
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z y : ι → ℝ)
    (E O : Polynomial ℝ) (k : ℕ)
    (hbudget : (s.image t).card +
      (GCDMonoid.gcd O E).natDegree ≤ 2*k)
    (hEdegree : E.degree = (k : WithBot ℕ))
    (hOdegree : O.degree ≤ k)
    (hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0)
    (hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0)
    (hc : ∀ i ∈ s, E.eval (t i) * z i +
      O.eval (t i) * y i = 0)
    (hnode : ∃ r ∈ s.image t,
      paperGroupedResidue s t z r ≠ 0 ∨
        paperGroupedResidue s t y r ≠ 0) : False := by
  have hgap := paperContactResidue_grouped_gcd_degree_gap
    s t z y E O k hEdegree hOdegree hz hy hc hnode
  omega

theorem paperEvenGroupedCertificate_gcd_degree_gap
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) (hk : 0 < k)
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (side : ι → Bool) (w t : ι → ℝ)
    (x : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hsne : s.Nonempty)
    (htpos : ∀ i ∈ s, 0 < t i)
    (hwpos : ∀ i ∈ s, 0 < w i)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k) a b q))
    (hbalance : ∀ r : Fin (2*k),
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial (2*k)
          (if side i then b else a)
          (paperFiniteNumeratorCoeffs (2*k)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0)
    (hcontact : ∀ i ∈ s,
      (paperRaisedCrossPolynomial (2*k)
        (if side i then b else a) x ε).eval (t i) = 0) :
    2*k < (s.image t).card +
      (GCDMonoid.gcd
        (paperAxisOdd (2*k)
          (paperDescendingNumerator (2*k) x +
            Polynomial.C ε * Polynomial.X^(2*k)))
        (paperAxisEven (2*k)
          (paperDescendingNumerator (2*k) x +
            Polynomial.C ε * Polynomial.X^(2*k)))).natDegree := by
  let n := 2*k
  let d : ι → ℕ → ℝ := fun i =>
    if side i then b else a
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let E := paperAxisEven n P
  let O := paperAxisOdd n P
  let z : ι → ℝ := fun i =>
    w i * (paperAxisEven n
      (paperDescendingDenominator n (d i))).eval (t i)
  let y : ι → ℝ := fun i =>
    w i * t i * (paperAxisOdd n
      (paperDescendingDenominator n (d i))).eval (t i)
  have hn : 0 < n := by dsimp [n]; omega
  have hmonic : ∀ i ∈ s, d i 0 = 1 := by
    intro i hi
    by_cases h : side i
    · simp [d, h, hb0]
    · simp [d, h, ha0]
  have hstable : ∀ i ∈ s,
      paperPolynomialHurwitz
        (paperDescendingDenominator n (d i)) := by
    intro i hi
    by_cases h : side i
    · simpa [d, h, paperSegmentDenominator] using
        (hsegment 1 (by norm_num) (by norm_num))
    · simpa [d, h, paperSegmentDenominator] using
        (hsegment 0 (by norm_num) (by norm_num))
  have hpdegree : P.natDegree = n := by
    exact paperDescendingNumerator_raise_natDegree_eq n x ε hε
  have hEbound : E.natDegree ≤ k := by
    simpa [E, n] using
      paperAxisEven_natDegree_le n P hpdegree.le
  have hEcoeff : E.coeff k = ε * (-1 : ℝ)^k := by
    have hPtop : P.coeff n = ε := by
      dsimp [P]
      rw [Polynomial.coeff_add, paperDescendingNumerator_coeff,
        if_neg (by omega : ¬ n < n),
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_pos rfl]
      ring
    change (paperAxisEven n P).coeff k = ε * (-1 : ℝ)^k
    rw [paperAxisEven_coeff, if_pos (by dsimp [n]; omega),
      show 2*k = n by rfl, hPtop]
  have hEcoe : E.coeff k ≠ 0 :=
    hEcoeff.symm ▸
      mul_ne_zero (ne_of_gt hε) (pow_ne_zero _ (by norm_num))
  have hEnat : E.natDegree = k :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      hEbound hEcoe
  have hEdegree : E.degree = (k : WithBot ℕ) := by
    have hEne : E ≠ 0 := by
      intro he
      simp [he] at hEcoe
    rw [Polynomial.degree_eq_natDegree hEne, hEnat]
  have hObound : O.natDegree ≤ k := by
    have h := paperAxisOdd_natDegree_le n P hpdegree.le
    change O.natDegree ≤ (n-1)/2 at h
    have hdiv : (n-1)/2 ≤ k := by dsimp [n]; omega
    exact h.trans hdiv
  have hOdegree : O.degree ≤ (k : WithBot ℕ) := by
    by_cases hOzero : O = 0
    · simp [hOzero]
    · rw [Polynomial.degree_eq_natDegree hOzero]
      exact_mod_cast hObound
  have hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0 := by
    intro j hj
    have hsmall : 2*j < n := by dsimp [n]; omega
    exact paperCoefficientBalance_even_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0 := by
    intro j hj
    have hsmall : 2*j+1 < n := by dsimp [n]; omega
    exact paperCoefficientBalance_odd_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hc : ∀ i ∈ s,
      E.eval (t i) * z i + O.eval (t i) * y i = 0 := by
    intro i hi
    have hid := paperRaisedCross_axis_identity_any
      n hn (d i) x ε (hmonic i hi) (hstable i hi)
    have hzero := hcontact i hi
    rw [hid] at hzero
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] at hzero
    calc
      E.eval (t i) * z i + O.eval (t i) * y i =
          w i * ((paperAxisEven n P).eval (t i) *
            (paperAxisEven n
              (paperDescendingDenominator n (d i))).eval (t i) +
            t i * (paperAxisOdd n P).eval (t i) *
              (paperAxisOdd n
                (paperDescendingDenominator n (d i))).eval (t i)) := by
          dsimp [E, O, z, y]
          ring
      _ = 0 := by
          rw [hzero]
          ring
  have hnode : ∃ r ∈ s.image t,
      paperGroupedResidue s t z r ≠ 0 ∨
        paperGroupedResidue s t y r ≠ 0 := by
    obtain ⟨i, hi⟩ := hsne
    have hr : t i ∈ s.image t :=
      Finset.mem_image.mpr ⟨i, hi, rfl⟩
    refine ⟨t i, hr, ?_⟩
    simpa [z, y, d] using
      (paperGroupedAxisResidue_nontrivial
        n a b ha0 hb0 s t w side htpos hwpos
        hsegment (t i) hr)
  change 2*k < (s.image t).card +
    (GCDMonoid.gcd O E).natDegree
  exact paperContactResidue_grouped_gcd_degree_gap
    s t z y E O k hEdegree hOdegree hz hy hc hnode

theorem PaperCriticalCertificate.interior_even_gcd_degree_gap
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hinter : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1)
    (hε : 0 < C.support 0) :
    2*(n/2) < C.positiveFiniteNodes.card +
      (GCDMonoid.gcd
        (paperAxisOdd n
          (paperDescendingNumerator n
            (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
           Polynomial.C (C.support 0) * Polynomial.X^n))
        (paperAxisEven n
          (paperDescendingNumerator n
            (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
           Polynomial.C (C.support 0) * Polynomial.X^n))).natDegree := by
  let k := n/2
  let w : Fin C.atomCount → ℝ :=
    fun i => C.weight i * (1-C.compactFrequency i)^n
  let t : Fin C.atomCount → ℝ :=
    fun i => C.compactFrequency i /
      (1-C.compactFrequency i)
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  have hk : 0 < k := by dsimp [k]; omega
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hindices : C.positiveFiniteIndices = Finset.univ := by
    ext i
    simp [PaperCriticalCertificate.positiveFiniteIndices,
      (hinter i).1, (hinter i).2]
  have hsne : (Finset.univ : Finset (Fin C.atomCount)).Nonempty := by
    obtain ⟨r, hr⟩ :=
      C.positiveFiniteNodes_nonempty
        hn ha0 hb0 hstableA hstableB
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hr
    exact ⟨i, Finset.mem_univ i⟩
  have htpos : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      0 < t i := by
    intro i _
    exact div_pos (hinter i).1 (sub_pos.mpr (hinter i).2)
  have hwpos : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      0 < w i := by
    intro i _
    exact mul_pos (C.weight_pos i)
      (pow_pos (sub_pos.mpr (hinter i).2) n)
  have hsegment' : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k) a b q) := by
    rw [←heven]
    exact hsegment
  have hbalance : ∀ r : Fin (2*k),
      (∑ i ∈ Finset.univ, w i *
        (paperGeneralCrossPolynomial (2*k)
          (if C.rightEndpoint i then b else a)
          (paperFiniteNumeratorCoeffs (2*k)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0 := by
    have hb := (C.ordinary_coefficient_balance_of_atoms_interior
      hinter).2
    rw [←heven]
    intro r
    simpa [w, t] using hb r
  have hcontact : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      (paperRaisedCrossPolynomial (2*k)
        (if C.rightEndpoint i then b else a)
        x ε).eval (t i) = 0 := by
    intro i _
    rw [←heven]
    simpa [x, ε, t] using
      (C.positive_contact_root_and_deriv
        i (hinter i).1 (hinter i).2).1
  have hgap := paperEvenGroupedCertificate_gcd_degree_gap
    Finset.univ k hk a b ha0 hb0 C.rightEndpoint
    w t x ε hε hsne htpos hwpos
    hsegment' hbalance hcontact
  have hcardEq : C.positiveFiniteNodes.card =
      (Finset.univ.image t).card := by
    simp only [PaperCriticalCertificate.positiveFiniteNodes, hindices]
    rfl
  rw [← heven] at hgap
  rw [← heven, hcardEq]
  simpa only [x, ε] using hgap

/-- A remaining even-order interior certificate must have a common parity
factor whose degree exceeds the number of shared positive endpoint roots. -/
theorem PaperCriticalCertificate.interior_even_gcd_exceeds_overlap
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hinter : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1)
    (hε : 0 < C.support 0) :
    let x := paperFiniteNumeratorCoeffs n
      (fun j => C.support j.succ)
    let P := paperDescendingNumerator n x +
      Polynomial.C (C.support 0) * Polynomial.X^n
    let qA := paperRaisedCrossPolynomial n a x (C.support 0)
    let qB := paperRaisedCrossPolynomial n b x (C.support 0)
    ((MonicQuinticCoeff.positiveRealRoots qA ∩
      MonicQuinticCoeff.positiveRealRoots qB).card) <
        (GCDMonoid.gcd (paperAxisOdd n P)
          (paperAxisEven n P)).natDegree := by
  dsimp
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hbound := C.positiveFiniteNodes_card_add_overlap_le
    hn ha0 hb0 hstableA hstableB
  have hgap := C.interior_even_gcd_degree_gap
    hn ha0 hb0 hsegment heven hinter hε
  omega

/-- If a real polynomial has no open right-half-plane root, every common
complex root of its even and odd axis components is a nonnegative real
squared frequency. -/
theorem paperAxisEvenOdd_common_root_nonnegative_real
    (n : ℕ) (p : Polynomial ℝ) (hpdegree : p.natDegree ≤ n)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z p ≠ (0 : ℂ))
    (t : ℂ)
    (hE : Polynomial.aeval t (paperAxisEven n p) = 0)
    (hO : Polynomial.aeval t (paperAxisOdd n p) = 0) :
    0 ≤ t.re ∧ t.im = 0 := by
  obtain ⟨s, hs⟩ :=
    IsAlgClosed.exists_pow_nat_eq (-t) (show 0 < 2 by decide)
  have ht : -s^2 = t := by rw [hs]; ring
  have hzero (u : ℂ) (hu : -u^2 = t) :
      Polynomial.aeval u p = 0 := by
    rw [paperAxisEvenOdd_polynomial_identity n p hpdegree]
    simp only [Polynomial.aeval_add, Polynomial.aeval_mul,
      Polynomial.aeval_comp, map_neg, map_pow,
      Polynomial.aeval_X]
    rw [hu, hE, hO]
    ring
  have hsnonpos : s.re ≤ 0 := by
    by_contra h
    push_neg at h
    exact (hopen s h) (hzero s ht)
  have hsnonneg : 0 ≤ s.re := by
    by_contra h
    push_neg at h
    have hnegpos : 0 < (-s).re := by
      simp only [Complex.neg_re]
      linarith
    have htneg : -(-s)^2 = t := by
      calc
        -(-s)^2 = -s^2 := by ring
        _ = t := ht
    exact (hopen (-s) hnegpos) (hzero (-s) htneg)
  have hsre : s.re = 0 := le_antisymm hsnonpos hsnonneg
  have htre : t.re = s.im^2 := by
    rw [← ht]
    simp only [Complex.neg_re, pow_two, Complex.mul_re]
    rw [hsre]
    ring
  have htim : t.im = 0 := by
    rw [← ht]
    simp only [Complex.neg_im, pow_two, Complex.mul_im]
    rw [hsre]
    ring
  exact ⟨by rw [htre]; positivity, htim⟩

theorem paperAxisEvenOdd_common_root_positive_real
    (n : ℕ) (p : Polynomial ℝ) (hpdegree : p.natDegree ≤ n)
    (hp0 : 0 < p.eval 0)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z p ≠ (0 : ℂ))
    (t : ℂ)
    (hE : Polynomial.aeval t (paperAxisEven n p) = 0)
    (hO : Polynomial.aeval t (paperAxisOdd n p) = 0) :
    0 < t.re ∧ t.im = 0 := by
  obtain ⟨htnonneg, htim⟩ :=
    paperAxisEvenOdd_common_root_nonnegative_real
      n p hpdegree hopen t hE hO
  have htne : t ≠ 0 := by
    intro hz
    subst t
    have hE0 : (paperAxisEven n p).eval 0 = 0 := by
      have hcoeff : (paperAxisEven n p).coeff 0 = 0 := by
        simpa [Polynomial.aeval_def] using hE
      simpa [Polynomial.coeff_zero_eq_eval_zero] using hcoeff
    have hpE := paperAxisEvenOdd_real_eval n p hpdegree 0
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_zero,
      zero_mul, add_zero] at hpE
    rw [hE0] at hpE
    linarith
  have htre : t.re ≠ 0 := by
    intro hzero
    apply htne
    apply Complex.ext
    · simpa using hzero
    · simpa using htim
  exact ⟨lt_of_le_of_ne htnonneg htre.symm, htim⟩

theorem paperAxisEvenOdd_common_root_imaginary_zero
    (n : ℕ) (p : Polynomial ℝ) (hpdegree : p.natDegree ≤ n)
    (hp0 : 0 < p.eval 0)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z p ≠ (0 : ℂ))
    (t : ℂ)
    (hE : Polynomial.aeval t (paperAxisEven n p) = 0)
    (hO : Polynomial.aeval t (paperAxisOdd n p) = 0) :
    ∃ ω : ℝ, 0 < ω ∧ t = ((ω^2 : ℝ) : ℂ) ∧
      Polynomial.aeval (jw ω) p = 0 := by
  obtain ⟨hrpos, htim⟩ :=
    paperAxisEvenOdd_common_root_positive_real
      n p hpdegree hp0 hopen t hE hO
  let ω := Real.sqrt t.re
  have hωpos : 0 < ω := Real.sqrt_pos.2 hrpos
  have hωsq : ω^2 = t.re := Real.sq_sqrt hrpos.le
  have htcast : t = ((t.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using htim
  have hEreal : (paperAxisEven n p).eval t.re = 0 := by
    rw [htcast, Polynomial.aeval_def] at hE
    change Polynomial.eval₂ (algebraMap ℝ ℂ)
      ((algebraMap ℝ ℂ) t.re) (paperAxisEven n p) = 0 at hE
    rw [Polynomial.eval₂_at_apply] at hE
    change (((paperAxisEven n p).eval t.re : ℝ) : ℂ) = 0 at hE
    exact_mod_cast hE
  have hOreal : (paperAxisOdd n p).eval t.re = 0 := by
    rw [htcast, Polynomial.aeval_def] at hO
    change Polynomial.eval₂ (algebraMap ℝ ℂ)
      ((algebraMap ℝ ℂ) t.re) (paperAxisOdd n p) = 0 at hO
    rw [Polynomial.eval₂_at_apply] at hO
    change (((paperAxisOdd n p).eval t.re : ℝ) : ℂ) = 0 at hO
    exact_mod_cast hO
  refine ⟨ω, hωpos, ?_, ?_⟩
  · rw [hωsq]
    exact htcast
  · rw [paperAxisComplex_eval n p hpdegree ω, hωsq,
      hEreal, hOreal]
    simp

/-- Every common parity root of a weakly positive-real numerator with a
positive constant term appears as a shared positive root of the two endpoint
cross polynomials. -/
theorem paperAxisCommonRoot_in_endpoint_overlap
    (n : ℕ) (hn : 0 < n) (a b x : ℕ → ℝ) (ε : ℝ)
    (P : Polynomial ℝ)
    (hPform : P = paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n)
    (hPdegree : P.natDegree ≤ n)
    (hP0 : 0 < P.eval 0)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ))
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hqAne : paperRaisedCrossPolynomial n a x ε ≠ 0)
    (hqBne : paperRaisedCrossPolynomial n b x ε ≠ 0)
    (t : ℂ)
    (hE : Polynomial.aeval t (paperAxisEven n P) = 0)
    (hO : Polynomial.aeval t (paperAxisOdd n P) = 0) :
    t.re ∈
      (MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n a x ε)) ∩
      (MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n b x ε)) := by
  obtain ⟨ω, hωpos, ht, hPzero⟩ :=
    paperAxisEvenOdd_common_root_imaginary_zero
      n P hPdegree hP0 hopen t hE hO
  have hPzero' : Polynomial.aeval (jw ω)
      (paperDescendingNumerator n x +
        Polynomial.C ε * Polynomial.X^n) = 0 := by
    simpa only [hPform] using hPzero
  have hqAzero := paperRaisedCross_eval_zero_of_numerator_imag_zero
    n hn a x ε ω hstableA hPzero'
  have hqBzero := paperRaisedCross_eval_zero_of_numerator_imag_zero
    n hn b x ε ω hstableB hPzero'
  have htre : t.re = ω^2 := by
    rw [ht]
    exact Complex.ofReal_re _
  have hωsqpos : 0 < ω^2 := sq_pos_of_pos hωpos
  apply Finset.mem_inter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨?_, by rw [htre]; exact hωsqpos⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hqAne, htre]
    exact hqAzero
  · apply Finset.mem_filter.mpr
    refine ⟨?_, by rw [htre]; exact hωsqpos⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hqBne, htre]
    exact hqBzero

theorem paperAxisGcd_root_in_endpoint_overlap
    (n : ℕ) (hn : 0 < n) (a b x : ℕ → ℝ) (ε : ℝ)
    (P : Polynomial ℝ)
    (hPform : P = paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n)
    (hPdegree : P.natDegree ≤ n)
    (hP0 : 0 < P.eval 0)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ))
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hqAne : paperRaisedCrossPolynomial n a x ε ≠ 0)
    (hqBne : paperRaisedCrossPolynomial n b x ε ≠ 0)
    (t : ℂ)
    (hroot : Polynomial.aeval t
      (GCDMonoid.gcd (paperAxisOdd n P)
        (paperAxisEven n P)) = 0) :
    t.re ∈
      (MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n a x ε)) ∩
      (MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n b x ε)) := by
  let E := paperAxisEven n P
  let O := paperAxisOdd n P
  let G := GCDMonoid.gcd O E
  have hE : Polynomial.aeval t E = 0 := by
    obtain ⟨M, hM⟩ := GCDMonoid.gcd_dvd_right O E
    rw [hM, Polynomial.aeval_mul]
    rw [show Polynomial.aeval t G = 0 from hroot]
    simp
  have hO : Polynomial.aeval t O = 0 := by
    obtain ⟨M, hM⟩ := GCDMonoid.gcd_dvd_left O E
    rw [hM, Polynomial.aeval_mul]
    rw [show Polynomial.aeval t G = 0 from hroot]
    simp
  exact paperAxisCommonRoot_in_endpoint_overlap
    n hn a b x ε P hPform hPdegree hP0 hopen
      hstableA hstableB hqAne hqBne t hE hO

theorem paperAxisGcd_root_positive_real
    (n : ℕ) (P : Polynomial ℝ)
    (hPdegree : P.natDegree ≤ n) (hP0 : 0 < P.eval 0)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ))
    (t : ℂ)
    (hroot : Polynomial.aeval t
      (GCDMonoid.gcd (paperAxisOdd n P)
        (paperAxisEven n P)) = 0) :
    0 < t.re ∧ t.im = 0 := by
  let E := paperAxisEven n P
  let O := paperAxisOdd n P
  let G := GCDMonoid.gcd O E
  have hE : Polynomial.aeval t E = 0 := by
    obtain ⟨M, hM⟩ := GCDMonoid.gcd_dvd_right O E
    rw [hM, Polynomial.aeval_mul]
    rw [show Polynomial.aeval t G = 0 from hroot]
    simp
  have hO : Polynomial.aeval t O = 0 := by
    obtain ⟨M, hM⟩ := GCDMonoid.gcd_dvd_left O E
    rw [hM, Polynomial.aeval_mul]
    rw [show Polynomial.aeval t G = 0 from hroot]
    simp
  exact paperAxisEvenOdd_common_root_positive_real
    n P hPdegree hP0 hopen t hE hO

theorem paperAxisGcd_distinct_roots_le_overlap
    (n : ℕ) (hn : 0 < n) (a b x : ℕ → ℝ) (ε : ℝ)
    (P : Polynomial ℝ)
    (hPform : P = paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n)
    (hPdegree : P.natDegree ≤ n)
    (hP0 : 0 < P.eval 0)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ))
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hqAne : paperRaisedCrossPolynomial n a x ε ≠ 0)
    (hqBne : paperRaisedCrossPolynomial n b x ε ≠ 0)
    (hGne : GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P) ≠ 0) :
    let G := GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P)
    let q := G.map (algebraMap ℝ ℂ)
    q.roots.toFinset.card ≤
      ((MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n a x ε)) ∩
        (MonicQuinticCoeff.positiveRealRoots
          (paperRaisedCrossPolynomial n b x ε))).card := by
  classical
  dsimp
  let G := GCDMonoid.gcd (paperAxisOdd n P)
    (paperAxisEven n P)
  let q := G.map (algebraMap ℝ ℂ)
  let R := q.roots.toFinset
  let S := (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a x ε)) ∩
    (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n b x ε))
  have hqne : q ≠ 0 := Polynomial.map_ne_zero hGne
  have hroot (z : ℂ) (hz : z ∈ R) :
      Polynomial.aeval z G = 0 := by
    have hz' : z ∈ q.roots := Multiset.mem_toFinset.mp hz
    have hqzero := (Polynomial.mem_roots hqne).mp hz'
    simpa [q, G] using hqzero
  have hsubset : R.image Complex.re ⊆ S := by
    intro r hr
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
    exact paperAxisGcd_root_in_endpoint_overlap
      n hn a b x ε P hPform hPdegree hP0 hopen
        hstableA hstableB hqAne hqBne z (hroot z hz)
  have hinj : Set.InjOn Complex.re R := by
    intro z hz v hv hreal
    have hzi := (paperAxisGcd_root_positive_real
      n P hPdegree hP0 hopen z (hroot z hz)).2
    have hvi := (paperAxisGcd_root_positive_real
      n P hPdegree hP0 hopen v (hroot v hv)).2
    apply Complex.ext
    · exact hreal
    · rw [hzi, hvi]
  have hcardImage : (R.image Complex.re).card = R.card :=
    Finset.card_image_of_injOn hinj
  have hcardSubset := Finset.card_le_card hsubset
  change R.card ≤ S.card
  omega

theorem paperAxisGcd_degree_le_overlap_of_nodup
    (n : ℕ) (hn : 0 < n) (a b x : ℕ → ℝ) (ε : ℝ)
    (P : Polynomial ℝ)
    (hPform : P = paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n)
    (hPdegree : P.natDegree ≤ n)
    (hP0 : 0 < P.eval 0)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ))
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hqAne : paperRaisedCrossPolynomial n a x ε ≠ 0)
    (hqBne : paperRaisedCrossPolynomial n b x ε ≠ 0)
    (hGne : GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P) ≠ 0)
    (hnodup : ((GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P)).map (algebraMap ℝ ℂ)).roots.Nodup) :
    (GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P)).natDegree ≤
      ((MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n a x ε)) ∩
        (MonicQuinticCoeff.positiveRealRoots
          (paperRaisedCrossPolynomial n b x ε))).card := by
  let G := GCDMonoid.gcd (paperAxisOdd n P)
    (paperAxisEven n P)
  let q := G.map (algebraMap ℝ ℂ)
  have hdistinct := paperAxisGcd_distinct_roots_le_overlap
    n hn a b x ε P hPform hPdegree hP0 hopen
      hstableA hstableB hqAne hqBne hGne
  have hsplit : q.Splits (RingHom.id ℂ) := IsAlgClosed.splits q
  have hdegree : G.natDegree = q.roots.card := by
    have h := Polynomial.natDegree_eq_card_roots' hsplit
    simpa [q, Polynomial.natDegree_map] using h
  have hcard : q.roots.toFinset.card = q.roots.card :=
    Multiset.toFinset_card_of_nodup hnodup
  change G.natDegree ≤ _
  rw [hdegree, ←hcard]
  exact hdistinct

theorem PaperCriticalCertificate.no_interior_even_certificate_of_nodup_gcd
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hinter : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1)
    (hε : 0 < C.support 0)
    (hP0 : 0 < (paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
       Polynomial.C (C.support 0) * Polynomial.X^n).eval 0)
    (hGne : GCDMonoid.gcd
      (paperAxisOdd n
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n))
      (paperAxisEven n
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n)) ≠ 0)
    (hnodup : ((GCDMonoid.gcd
      (paperAxisOdd n
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n))
      (paperAxisEven n
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n))).map
           (algebraMap ℝ ℂ)).roots.Nodup) : False := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hweak := C.support_numerator_weak_re_nonneg
    hn hstableA hstableB
  have hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ 0 := by
    intro z hz
    exact paperWeakPositiveReal_no_open_right_root
      n a x ε ha0 hε hstableA
      (fun ω => by simpa [x, ε] using (hweak ω).1) z hz
  have hPdegree : P.natDegree ≤ n :=
    (paperDescendingNumerator_raise_natDegree_eq n x ε hε).le
  have hqAne := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn a ha0 hstableA C.support C.support_ne
  have hqBne := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn b hb0 hstableB C.support C.support_ne
  have hbound := paperAxisGcd_degree_le_overlap_of_nodup
    n hn a b x ε P rfl hPdegree
    (by simpa [P, x, ε] using hP0) hopen
    hstableA hstableB
    (by simpa [x, ε] using hqAne)
    (by simpa [x, ε] using hqBne)
    (by simpa [P, x, ε] using hGne)
    (by simpa [P, x, ε] using hnodup)
  have hgap := C.interior_even_gcd_exceeds_overlap
    hn ha0 hb0 hsegment heven hinter hε
  exact (not_lt_of_ge hbound) hgap



theorem paperAxisEven_ne_zero_of_eval_zero_pos
    (n : ℕ) (P : Polynomial ℝ) (hP0 : 0 < P.eval 0) :
    paperAxisEven n P ≠ 0 := by
  intro hzero
  have hcoeff := paperAxisEven_coeff n P 0
  rw [hzero] at hcoeff
  have hc : P.coeff 0 = 0 := by simpa using hcoeff.symm
  rw [Polynomial.coeff_zero_eq_eval_zero] at hc
  exact (ne_of_gt hP0) hc


theorem PaperCriticalCertificate.interior_even_gcd_repeated_root
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hinter : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1)
    (hε : 0 < C.support 0)
    (hP0 : 0 < (paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
       Polynomial.C (C.support 0) * Polynomial.X^n).eval 0) :
    ¬ ((GCDMonoid.gcd
      (paperAxisOdd n
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n))
      (paperAxisEven n
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n))).map
           (algebraMap ℝ ℂ)).roots.Nodup := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  have hEne : paperAxisEven n P ≠ 0 :=
    paperAxisEven_ne_zero_of_eval_zero_pos n P
      (by simpa [P, x, ε] using hP0)
  have hGne : GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P) ≠ 0 :=
    gcd_ne_zero_of_right hEne
  intro hnodup
  exact C.no_interior_even_certificate_of_nodup_gcd
    hn ha0 hb0 hsegment heven hinter hε hP0
    (by simpa [P, x, ε] using hGne) hnodup



/-- An even-order interior critical certificate has an origin zero or a
repeated positive imaginary-axis zero in its supporting numerator. -/
theorem PaperCriticalCertificate.interior_even_origin_or_repeated_gcd
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hinter : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1)
    (hε : 0 < C.support 0) :
    let P := paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
       Polynomial.C (C.support 0) * Polynomial.X^n
    P.eval 0 = 0 ∨
      ¬ ((GCDMonoid.gcd (paperAxisOdd n P)
          (paperAxisEven n P)).map (algebraMap ℝ ℂ)).roots.Nodup := by
  dsimp
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hweak := C.support_numerator_weak_re_nonneg
    hn hstableA hstableB
  have hP0nonneg : 0 ≤ P.eval 0 := by
    exact paperWeakPositiveReal_eval_nonneg n hn a x ε ha0 hε
      hstableA
      (fun ω => by simpa [x, ε] using (hweak ω).1)
      0 (le_refl 0)
  by_cases hP0 : 0 < P.eval 0
  · right
    exact C.interior_even_gcd_repeated_root hn ha0 hb0
      hsegment heven hinter hε
      (by simpa [P, x, ε] using hP0)
  · left
    linarith



/-- An origin zero uses one unit of degree at each endpoint. In even order,
the total distinct-contact plus shared-root budget drops by two. -/
theorem PaperCriticalCertificate.positiveFiniteNodes_card_add_overlap_le_of_origin_zero
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (heven : n = 2*(n/2))
    (hP0 : (paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
       Polynomial.C (C.support 0) * Polynomial.X^n).eval 0 = 0) :
    C.positiveFiniteNodes.card +
      ((MonicQuinticCoeff.positiveRealRoots
          (paperRaisedCrossPolynomial n a
            (paperFiniteNumeratorCoeffs n
              (fun j => C.support j.succ)) (C.support 0))) ∩
        (MonicQuinticCoeff.positiveRealRoots
          (paperRaisedCrossPolynomial n b
            (paperFiniteNumeratorCoeffs n
              (fun j => C.support j.succ)) (C.support 0)))).card
        ≤ n-2 := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let qA := paperRaisedCrossPolynomial n a x ε
  let qB := paperRaisedCrossPolynomial n b x ε
  let rootsA := MonicQuinticCoeff.positiveRealRoots qA
  let rootsB := MonicQuinticCoeff.positiveRealRoots qB
  have hx0 : x (n-1) = 0 := by
    change (paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n).eval 0 = 0 at hP0
    rw [paperRaisedNumerator_eval_zero n hn x ε] at hP0
    exact hP0
  have hqA0 : qA.eval 0 = 0 := by
    rw [paperRaisedCrossPolynomial_eval_zero n hn a x ε, hx0, mul_zero]
  have hqB0 : qB.eval 0 = 0 := by
    rw [paperRaisedCrossPolynomial_eval_zero n hn b x ε, hx0, mul_zero]
  have hneA : qA ≠ 0 :=
    paperRaisedCrossPolynomial_ne_zero_of_hurwitz
      n hn a ha0 hstableA C.support C.support_ne
  have hneB : qB ≠ 0 :=
    paperRaisedCrossPolynomial_ne_zero_of_hurwitz
      n hn b hb0 hstableB C.support C.support_ne
  have hnonnegA : ∀ t : ℝ, 0 ≤ t → 0 ≤ qA.eval t :=
    paperFeature_nonneg_cross_nonneg n a C.support C.support_nonneg_left
  have hnonnegB : ∀ t : ℝ, 0 ≤ t → 0 ≤ qB.eval t :=
    paperFeature_nonneg_cross_nonneg n b C.support C.support_nonneg_right
  have hboundA : 2*rootsA.card+1 ≤ n :=
    (MonicQuinticCoeff.twice_card_positiveRealRoots_add_one_le_natDegree_of_zero_root
      qA hneA hnonnegA hqA0).trans
      (paperRaisedCrossPolynomial_natDegree_le n a x ε)
  have hboundB : 2*rootsB.card+1 ≤ n :=
    (MonicQuinticCoeff.twice_card_positiveRealRoots_add_one_le_natDegree_of_zero_root
      qB hneB hnonnegB hqB0).trans
      (paperRaisedCrossPolynomial_natDegree_le n b x ε)
  have hsub : C.positiveFiniteNodes ⊆ rootsA ∪ rootsB :=
    C.positiveFiniteNodes_subset_endpoint_roots
      hn ha0 hb0 hstableA hstableB
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_add_card_inter rootsA rootsB
  change C.positiveFiniteNodes.card + (rootsA ∩ rootsB).card ≤ n-2
  omega

/-- A common parity root with positive real part is a positive squared
frequency, even when the supporting numerator vanishes at the origin. -/
theorem paperAxisEvenOdd_common_root_imaginary_zero_of_positive_re
    (n : ℕ) (p : Polynomial ℝ) (hpdegree : p.natDegree ≤ n)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z p ≠ (0 : ℂ))
    (t : ℂ) (htpos : 0 < t.re)
    (hE : Polynomial.aeval t (paperAxisEven n p) = 0)
    (hO : Polynomial.aeval t (paperAxisOdd n p) = 0) :
    ∃ ω : ℝ, 0 < ω ∧ t = ((ω^2 : ℝ) : ℂ) ∧
      Polynomial.aeval (jw ω) p = 0 := by
  have htim := (paperAxisEvenOdd_common_root_nonnegative_real
    n p hpdegree hopen t hE hO).2
  let ω := Real.sqrt t.re
  have hωpos : 0 < ω := Real.sqrt_pos.2 htpos
  have hωsq : ω^2 = t.re := Real.sq_sqrt htpos.le
  have htcast : t = ((t.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using htim
  have hEreal : (paperAxisEven n p).eval t.re = 0 := by
    rw [htcast, Polynomial.aeval_def] at hE
    change Polynomial.eval₂ (algebraMap ℝ ℂ)
      ((algebraMap ℝ ℂ) t.re) (paperAxisEven n p) = 0 at hE
    rw [Polynomial.eval₂_at_apply] at hE
    change (((paperAxisEven n p).eval t.re : ℝ) : ℂ) = 0 at hE
    exact_mod_cast hE
  have hOreal : (paperAxisOdd n p).eval t.re = 0 := by
    rw [htcast, Polynomial.aeval_def] at hO
    change Polynomial.eval₂ (algebraMap ℝ ℂ)
      ((algebraMap ℝ ℂ) t.re) (paperAxisOdd n p) = 0 at hO
    rw [Polynomial.eval₂_at_apply] at hO
    change (((paperAxisOdd n p).eval t.re : ℝ) : ℂ) = 0 at hO
    exact_mod_cast hO
  refine ⟨ω, hωpos, ?_, ?_⟩
  · rw [hωsq]
    exact htcast
  · rw [paperAxisComplex_eval n p hpdegree ω, hωsq,
      hEreal, hOreal]
    simp

theorem paperAxisCommonRoot_in_endpoint_overlap_of_positive_re
    (n : ℕ) (hn : 0 < n) (a b x : ℕ → ℝ) (ε : ℝ)
    (P : Polynomial ℝ)
    (hPform : P = paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n)
    (hPdegree : P.natDegree ≤ n)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ))
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hqAne : paperRaisedCrossPolynomial n a x ε ≠ 0)
    (hqBne : paperRaisedCrossPolynomial n b x ε ≠ 0)
    (t : ℂ) (htpos : 0 < t.re)
    (hE : Polynomial.aeval t (paperAxisEven n P) = 0)
    (hO : Polynomial.aeval t (paperAxisOdd n P) = 0) :
    t.re ∈
      (MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n a x ε)) ∩
      (MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n b x ε)) := by
  obtain ⟨ω, hωpos, ht, hPzero⟩ :=
    paperAxisEvenOdd_common_root_imaginary_zero_of_positive_re
      n P hPdegree hopen t htpos hE hO
  have hPzero' : Polynomial.aeval (jw ω)
      (paperDescendingNumerator n x +
        Polynomial.C ε * Polynomial.X^n) = 0 := by
    simpa only [hPform] using hPzero
  have hqAzero := paperRaisedCross_eval_zero_of_numerator_imag_zero
    n hn a x ε ω hstableA hPzero'
  have hqBzero := paperRaisedCross_eval_zero_of_numerator_imag_zero
    n hn b x ε ω hstableB hPzero'
  have htre : t.re = ω^2 := by
    rw [ht]
    exact Complex.ofReal_re _
  have hωsqpos : 0 < ω^2 := sq_pos_of_pos hωpos
  apply Finset.mem_inter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨?_, by rw [htre]; exact hωsqpos⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hqAne, htre]
    exact hqAzero
  · apply Finset.mem_filter.mpr
    refine ⟨?_, by rw [htre]; exact hωsqpos⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hqBne, htre]
    exact hqBzero

theorem paperAxisGcd_root_nonnegative_real
    (n : ℕ) (P : Polynomial ℝ)
    (hPdegree : P.natDegree ≤ n)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ))
    (t : ℂ)
    (hroot : Polynomial.aeval t
      (GCDMonoid.gcd (paperAxisOdd n P)
        (paperAxisEven n P)) = 0) :
    0 ≤ t.re ∧ t.im = 0 := by
  let E := paperAxisEven n P
  let O := paperAxisOdd n P
  let G := GCDMonoid.gcd O E
  have hE : Polynomial.aeval t E = 0 := by
    obtain ⟨M, hM⟩ := GCDMonoid.gcd_dvd_right O E
    rw [hM, Polynomial.aeval_mul]
    rw [show Polynomial.aeval t G = 0 from hroot]
    simp
  have hO : Polynomial.aeval t O = 0 := by
    obtain ⟨M, hM⟩ := GCDMonoid.gcd_dvd_left O E
    rw [hM, Polynomial.aeval_mul]
    rw [show Polynomial.aeval t G = 0 from hroot]
    simp
  exact paperAxisEvenOdd_common_root_nonnegative_real
    n P hPdegree hopen t hE hO

theorem paperAxisGcd_root_in_endpoint_overlap_of_positive_re
    (n : ℕ) (hn : 0 < n) (a b x : ℕ → ℝ) (ε : ℝ)
    (P : Polynomial ℝ)
    (hPform : P = paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n)
    (hPdegree : P.natDegree ≤ n)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ))
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hqAne : paperRaisedCrossPolynomial n a x ε ≠ 0)
    (hqBne : paperRaisedCrossPolynomial n b x ε ≠ 0)
    (t : ℂ) (htpos : 0 < t.re)
    (hroot : Polynomial.aeval t
      (GCDMonoid.gcd (paperAxisOdd n P)
        (paperAxisEven n P)) = 0) :
    t.re ∈
      (MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n a x ε)) ∩
      (MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n b x ε)) := by
  let E := paperAxisEven n P
  let O := paperAxisOdd n P
  let G := GCDMonoid.gcd O E
  have hE : Polynomial.aeval t E = 0 := by
    obtain ⟨M, hM⟩ := GCDMonoid.gcd_dvd_right O E
    rw [hM, Polynomial.aeval_mul]
    rw [show Polynomial.aeval t G = 0 from hroot]
    simp
  have hO : Polynomial.aeval t O = 0 := by
    obtain ⟨M, hM⟩ := GCDMonoid.gcd_dvd_left O E
    rw [hM, Polynomial.aeval_mul]
    rw [show Polynomial.aeval t G = 0 from hroot]
    simp
  exact paperAxisCommonRoot_in_endpoint_overlap_of_positive_re
    n hn a b x ε P hPform hPdegree hopen hstableA hstableB
      hqAne hqBne t htpos hE hO

/-- Distinct gcd roots lie over the shared positive endpoint roots, with
at most one extra root at the origin. -/
theorem paperAxisGcd_distinct_roots_le_overlap_add_one
    (n : ℕ) (hn : 0 < n) (a b x : ℕ → ℝ) (ε : ℝ)
    (P : Polynomial ℝ)
    (hPform : P = paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n)
    (hPdegree : P.natDegree ≤ n)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ))
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hqAne : paperRaisedCrossPolynomial n a x ε ≠ 0)
    (hqBne : paperRaisedCrossPolynomial n b x ε ≠ 0)
    (hGne : GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P) ≠ 0) :
    let G := GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P)
    let q := G.map (algebraMap ℝ ℂ)
    q.roots.toFinset.card ≤
      ((MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n a x ε)) ∩
        (MonicQuinticCoeff.positiveRealRoots
          (paperRaisedCrossPolynomial n b x ε))).card + 1 := by
  classical
  dsimp
  let G := GCDMonoid.gcd (paperAxisOdd n P)
    (paperAxisEven n P)
  let q := G.map (algebraMap ℝ ℂ)
  let R := q.roots.toFinset
  let S := (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a x ε)) ∩
    (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n b x ε))
  have hqne : q ≠ 0 := Polynomial.map_ne_zero hGne
  have hroot (z : ℂ) (hz : z ∈ R) :
      Polynomial.aeval z G = 0 := by
    have hz' : z ∈ q.roots := Multiset.mem_toFinset.mp hz
    have hqzero := (Polynomial.mem_roots hqne).mp hz'
    simpa [q, G] using hqzero
  have hsubset : R.image Complex.re ⊆ insert 0 S := by
    intro r hr
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
    have hnonneg := (paperAxisGcd_root_nonnegative_real
      n P hPdegree hopen z (hroot z hz)).1
    by_cases hzero : z.re = 0
    · simp [hzero]
    · have hpos : 0 < z.re := lt_of_le_of_ne hnonneg (Ne.symm hzero)
      exact Finset.mem_insert_of_mem
        (paperAxisGcd_root_in_endpoint_overlap_of_positive_re
          n hn a b x ε P hPform hPdegree hopen
            hstableA hstableB hqAne hqBne z hpos (hroot z hz))
  have hinj : Set.InjOn Complex.re R := by
    intro z hz v hv hreal
    have hzi := (paperAxisGcd_root_nonnegative_real
      n P hPdegree hopen z (hroot z hz)).2
    have hvi := (paperAxisGcd_root_nonnegative_real
      n P hPdegree hopen v (hroot v hv)).2
    apply Complex.ext
    · exact hreal
    · rw [hzi, hvi]
  have hcardImage : (R.image Complex.re).card = R.card :=
    Finset.card_image_of_injOn hinj
  have hcardSubset := Finset.card_le_card hsubset
  have hcardInsert := Finset.card_insert_le 0 S
  change R.card ≤ S.card + 1
  omega

theorem paperAxisGcd_degree_le_overlap_add_one_of_nodup
    (n : ℕ) (hn : 0 < n) (a b x : ℕ → ℝ) (ε : ℝ)
    (P : Polynomial ℝ)
    (hPform : P = paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n)
    (hPdegree : P.natDegree ≤ n)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ))
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hqAne : paperRaisedCrossPolynomial n a x ε ≠ 0)
    (hqBne : paperRaisedCrossPolynomial n b x ε ≠ 0)
    (hGne : GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P) ≠ 0)
    (hnodup : ((GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P)).map (algebraMap ℝ ℂ)).roots.Nodup) :
    (GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P)).natDegree ≤
      ((MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n a x ε)) ∩
        (MonicQuinticCoeff.positiveRealRoots
          (paperRaisedCrossPolynomial n b x ε))).card + 1 := by
  let G := GCDMonoid.gcd (paperAxisOdd n P)
    (paperAxisEven n P)
  let q := G.map (algebraMap ℝ ℂ)
  have hdistinct := paperAxisGcd_distinct_roots_le_overlap_add_one
    n hn a b x ε P hPform hPdegree hopen
      hstableA hstableB hqAne hqBne hGne
  have hsplit : q.Splits (RingHom.id ℂ) := IsAlgClosed.splits q
  have hdegree : G.natDegree = q.roots.card := by
    have h := Polynomial.natDegree_eq_card_roots' hsplit
    simpa [q, Polynomial.natDegree_map] using h
  have hcard : q.roots.toFinset.card = q.roots.card :=
    Multiset.toFinset_card_of_nodup hnodup
  change G.natDegree ≤ _
  rw [hdegree, ←hcard]
  exact hdistinct

theorem paperAxisEven_ne_zero_of_even_raised_positive_leading
    (n : ℕ) (x : ℕ → ℝ) (ε : ℝ)
    (heven : n = 2*(n/2)) (hε : 0 < ε) :
    paperAxisEven n
      (paperDescendingNumerator n x +
        Polynomial.C ε * Polynomial.X^n) ≠ 0 := by
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  have hPtop : P.coeff n = ε := by
    dsimp [P]
    rw [Polynomial.coeff_add, paperDescendingNumerator_coeff,
      if_neg (by omega : ¬ n < n),
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_pos rfl]
    ring
  have hEcoeff : (paperAxisEven n P).coeff (n/2) =
      ε * (-1 : ℝ)^(n/2) := by
    rw [paperAxisEven_coeff, if_pos (by omega : n/2 ≤ n),
      show 2*(n/2)=n from heven.symm, hPtop]
  have hEcoe : (paperAxisEven n P).coeff (n/2) ≠ 0 :=
    hEcoeff.symm ▸
      mul_ne_zero (ne_of_gt hε) (pow_ne_zero _ (by norm_num))
  intro hz
  change paperAxisEven n P = 0 at hz
  simp [hz] at hEcoe

/-- The origin-zero branch of an even-order interior certificate also
forces a repeated parity-gcd root. -/
theorem PaperCriticalCertificate.no_interior_even_origin_certificate_of_nodup_gcd
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hinter : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1)
    (hε : 0 < C.support 0)
    (hP0 : (paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
       Polynomial.C (C.support 0) * Polynomial.X^n).eval 0 = 0)
    (hnodup : ((GCDMonoid.gcd
      (paperAxisOdd n
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n))
      (paperAxisEven n
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n))).map
           (algebraMap ℝ ℂ)).roots.Nodup) : False := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hweak := C.support_numerator_weak_re_nonneg
    hn hstableA hstableB
  have hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ 0 := by
    intro z hz
    exact paperWeakPositiveReal_no_open_right_root
      n a x ε ha0 hε hstableA
      (fun ω => by simpa [x, ε] using (hweak ω).1) z hz
  have hPdegree : P.natDegree ≤ n :=
    (paperDescendingNumerator_raise_natDegree_eq n x ε hε).le
  have hqAne := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn a ha0 hstableA C.support C.support_ne
  have hqBne := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn b hb0 hstableB C.support C.support_ne
  have hEne : paperAxisEven n P ≠ 0 :=
    paperAxisEven_ne_zero_of_even_raised_positive_leading
      n x ε heven hε
  have hGne : GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P) ≠ 0 := gcd_ne_zero_of_right hEne
  have hbound := paperAxisGcd_degree_le_overlap_add_one_of_nodup
    n hn a b x ε P rfl hPdegree hopen
    hstableA hstableB
    (by simpa [x, ε] using hqAne)
    (by simpa [x, ε] using hqBne)
    hGne (by simpa [P, x, ε] using hnodup)
  have hcontact := C.positiveFiniteNodes_card_add_overlap_le_of_origin_zero
    hn ha0 hb0 hstableA hstableB heven hP0
  have hgap := C.interior_even_gcd_degree_gap
    hn ha0 hb0 hsegment heven hinter hε
  let S := (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a x ε)) ∩
    (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n b x ε))
  let G := GCDMonoid.gcd (paperAxisOdd n P)
    (paperAxisEven n P)
  change C.positiveFiniteNodes.card + S.card ≤ n-2 at hcontact
  change G.natDegree ≤ S.card + 1 at hbound
  change 2*(n/2) < C.positiveFiniteNodes.card + G.natDegree at hgap
  rw [←heven] at hgap
  omega

/-- A positive-leading even-order interior critical certificate forces a
multiple complex root in the parity gcd, without an assumption at zero. -/
theorem PaperCriticalCertificate.interior_even_gcd_repeated_root_unconditional
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hinter : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1)
    (hε : 0 < C.support 0) :
    let P := paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
       Polynomial.C (C.support 0) * Polynomial.X^n
    ¬ ((GCDMonoid.gcd (paperAxisOdd n P)
          (paperAxisEven n P)).map (algebraMap ℝ ℂ)).roots.Nodup := by
  dsimp
  rcases C.interior_even_origin_or_repeated_gcd
    hn ha0 hb0 hsegment heven hinter hε with hzero | hrepeat
  · intro hnodup
    exact C.no_interior_even_origin_certificate_of_nodup_gcd
      hn ha0 hb0 hsegment heven hinter hε hzero hnodup
  · exact hrepeat



/-- The even/odd reconstruction identity also controls the derivative at
any common repeated parity root. -/
theorem paperAxisEvenOdd_derivative_zero_of_repeated_common_root
    (n : ℕ) (P : Polynomial ℝ) (hPdegree : P.natDegree ≤ n)
    (t s : ℂ) (hs : -s^2 = t)
    (hO : Polynomial.aeval t (paperAxisOdd n P) = 0)
    (hEderiv : Polynomial.aeval t
      (paperAxisEven n P).derivative = 0)
    (hOderiv : Polynomial.aeval t
      (paperAxisOdd n P).derivative = 0) :
    Polynomial.aeval s P.derivative = 0 := by
  rw [paperAxisEvenOdd_polynomial_identity n P hPdegree]
  simp only [Polynomial.derivative_add, Polynomial.derivative_comp,
    Polynomial.derivative_mul, Polynomial.derivative_X, one_mul,
    Polynomial.aeval_add, Polynomial.aeval_mul,
    Polynomial.aeval_comp, Polynomial.aeval_X]
  rw [show Polynomial.aeval s (-Polynomial.X^2 : Polynomial ℝ) = t by
    simpa using hs, hO, hEderiv, hOderiv]
  ring

/-- A multiple complex root of the parity gcd gives a multiple imaginary-axis
zero of the supporting polynomial. -/
theorem paperAxisGcd_multiple_root_gives_imaginary_multiple_zero
    (n : ℕ) (P : Polynomial ℝ) (hPdegree : P.natDegree ≤ n)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ))
    (t : ℂ)
    (hGroot : Polynomial.aeval t
      (GCDMonoid.gcd (paperAxisOdd n P)
        (paperAxisEven n P)) = 0)
    (hGderiv : Polynomial.aeval t
      (GCDMonoid.gcd (paperAxisOdd n P)
        (paperAxisEven n P)).derivative = 0) :
    ∃ ω : ℝ, 0 ≤ ω ∧
      Polynomial.aeval (jw ω) P = 0 ∧
      Polynomial.aeval (jw ω) P.derivative = 0 := by
  let E := paperAxisEven n P
  let O := paperAxisOdd n P
  let G := GCDMonoid.gcd O E
  have hfactor_zero (F : Polynomial ℝ) (hdiv : G ∣ F) :
      Polynomial.aeval t F = 0 ∧
      Polynomial.aeval t F.derivative = 0 := by
    obtain ⟨M, hM⟩ := hdiv
    rw [hM]
    constructor
    · rw [Polynomial.aeval_mul,
        show Polynomial.aeval t G = 0 from hGroot]
      simp
    · rw [Polynomial.derivative_mul, Polynomial.aeval_add,
        Polynomial.aeval_mul, Polynomial.aeval_mul,
        show Polynomial.aeval t G = 0 from hGroot,
        show Polynomial.aeval t G.derivative = 0 from hGderiv]
      ring
  obtain ⟨hE, hEderiv⟩ :=
    hfactor_zero E (GCDMonoid.gcd_dvd_right O E)
  obtain ⟨hO, hOderiv⟩ :=
    hfactor_zero O (GCDMonoid.gcd_dvd_left O E)
  obtain ⟨htnonneg, htim⟩ :=
    paperAxisGcd_root_nonnegative_real
      n P hPdegree hopen t hGroot
  let ω := Real.sqrt t.re
  have hωnonneg : 0 ≤ ω := Real.sqrt_nonneg _
  have hωsq : ω^2 = t.re := Real.sq_sqrt htnonneg
  have htcast : t = ((t.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using htim
  have hs : -(jw ω)^2 = t := by
    rw [htcast, ←hωsq, jw, mul_pow, Complex.I_sq]
    norm_num
  have hPzero : Polynomial.aeval (jw ω) P = 0 := by
    rw [paperAxisEvenOdd_polynomial_identity n P hPdegree]
    simp only [Polynomial.aeval_add, Polynomial.aeval_mul,
      Polynomial.aeval_comp, Polynomial.aeval_X]
    rw [show Polynomial.aeval (jw ω)
      (-Polynomial.X^2 : Polynomial ℝ) = t by simpa using hs,
      hE, hO]
    ring
  refine ⟨ω, hωnonneg, hPzero, ?_⟩
  exact paperAxisEvenOdd_derivative_zero_of_repeated_common_root
    n P hPdegree t (jw ω) hs hO hEderiv hOderiv

/-- Simplicity of all imaginary-axis zeros of the support numerator makes
the complexified parity gcd squarefree. -/
theorem paperAxisGcd_roots_nodup_of_imaginary_simple
    (n : ℕ) (P : Polynomial ℝ) (hPdegree : P.natDegree ≤ n)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ))
    (hGne : GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P) ≠ 0)
    (hsimple : ∀ ω : ℝ,
      Polynomial.aeval (jw ω) P = 0 →
        Polynomial.aeval (jw ω) P.derivative ≠ 0) :
    ((GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P)).map (algebraMap ℝ ℂ)).roots.Nodup := by
  classical
  let G := GCDMonoid.gcd (paperAxisOdd n P)
    (paperAxisEven n P)
  let q := G.map (algebraMap ℝ ℂ)
  have hqne : q ≠ 0 := Polynomial.map_ne_zero hGne
  by_contra hdup
  rw [Multiset.nodup_iff_count_le_one] at hdup
  push_neg at hdup
  obtain ⟨t, ht⟩ := hdup
  have hmult : 1 < q.rootMultiplicity t := by
    rwa [Polynomial.count_roots] at ht
  obtain ⟨hroot, hderiv⟩ :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hqne).mp hmult
  have hGroot : Polynomial.aeval t G = 0 := by
    simpa [q, G] using hroot
  have hGderiv : Polynomial.aeval t G.derivative = 0 := by
    simpa [q, G, Polynomial.derivative_map] using hderiv
  obtain ⟨ω, _, hPzero, hPderiv⟩ :=
    paperAxisGcd_multiple_root_gives_imaginary_multiple_zero
      n P hPdegree hopen t hGroot hGderiv
  exact (hsimple ω hPzero) hPderiv

/-- The even-order interior branch of the arbitrary-order theorem follows
from simplicity of the imaginary-axis zeros of its weakly positive-real
supporting numerator. -/
theorem PaperCriticalCertificate.no_interior_even_certificate_of_imaginary_simple
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hinter : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1)
    (hε : 0 < C.support 0)
    (hsimple : ∀ ω : ℝ,
      Polynomial.aeval (jw ω)
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n) = 0 →
      Polynomial.aeval (jw ω)
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n).derivative ≠ 0) :
    False := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hweak := C.support_numerator_weak_re_nonneg
    hn hstableA hstableB
  have hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ 0 := by
    intro z hz
    exact paperWeakPositiveReal_no_open_right_root
      n a x ε ha0 hε hstableA
      (fun ω => by simpa [x, ε] using (hweak ω).1) z hz
  have hPdegree : P.natDegree ≤ n :=
    (paperDescendingNumerator_raise_natDegree_eq n x ε hε).le
  have hEne : paperAxisEven n P ≠ 0 :=
    paperAxisEven_ne_zero_of_even_raised_positive_leading
      n x ε heven hε
  have hGne : GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P) ≠ 0 := gcd_ne_zero_of_right hEne
  have hnodup := paperAxisGcd_roots_nodup_of_imaginary_simple
    n P hPdegree hopen hGne
    (by simpa [P, x, ε] using hsimple)
  exact (C.interior_even_gcd_repeated_root_unconditional
    hn ha0 hb0 hsegment heven hinter hε)
    (by simpa [P, x, ε] using hnodup)


open Polynomial Set Filter Asymptotics Bornology
open scoped ComplexConjugate Topology Filter Real

/-- The Cayley transform converts a nonnegative real part into a unit-disk
bound at any point where both quotients are defined. -/
theorem paperCayley_norm_le_one_of_re_div_nonneg
    (p d : ℂ) (hd : d ≠ 0)
    (hweak : 0 ≤ (p/d).re) :
    ‖(p-d)/(p+d)‖ ≤ 1 := by
  have hsum : p+d ≠ 0 := by
    intro hz
    have hp : p = -d := add_eq_zero_iff_eq_neg.mp hz
    rw [hp] at hweak
    simp [hd] at hweak
    norm_num at hweak
  have hdenpos : 0 < Complex.normSq d := Complex.normSq_pos.mpr hd
  have hquot : 0 ≤
      (p.re*d.re+p.im*d.im)/Complex.normSq d := by
    simpa [Complex.div_re, add_div] using hweak
  have hnum : 0 ≤ p.re*d.re+p.im*d.im := by
    have h := mul_nonneg hquot hdenpos.le
    rw [div_mul_cancel₀ _ (ne_of_gt hdenpos)] at h
    exact h
  have hpair : 0 ≤ (p*conj d).re := by
    simpa [Complex.mul_re, Complex.conj_re, Complex.conj_im,
      mul_neg, sub_neg_eq_add] using hnum
  have hsq : Complex.normSq (p-d) ≤ Complex.normSq (p+d) := by
    rw [Complex.normSq_sub, Complex.normSq_add]
    nlinarith
  have hnorm : ‖p-d‖ ≤ ‖p+d‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    exact Real.sqrt_le_sqrt hsq
  have hsumpos : 0 < ‖p+d‖ := norm_pos_iff.mpr hsum
  rw [norm_div]
  exact (div_le_iff₀ hsumpos).mpr (by simpa using hnorm)

/-- Weak positive-realness on the imaginary axis yields a closed-unit-disk
bound for the Cayley transform of the numerator and stable denominator. -/
theorem paperWeakRe_cayley_boundary_norm_le_one
    (P D : Polynomial ℝ)
    (hstable : paperPolynomialHurwitz D)
    (hweak : ∀ ω : ℝ,
      0 ≤ ((Polynomial.aeval (jw ω) P : ℂ) /
        Polynomial.aeval (jw ω) D).re)
    (ω : ℝ) :
    ‖((Polynomial.aeval (jw ω) P : ℂ) -
        Polynomial.aeval (jw ω) D) /
      ((Polynomial.aeval (jw ω) P : ℂ) +
        Polynomial.aeval (jw ω) D)‖ ≤ 1 := by
  have hDne : Polynomial.aeval (jw ω) D ≠ (0 : ℂ) :=
    paperPolynomialHurwitz_imag_ne_zero D hstable ω
  exact paperCayley_norm_le_one_of_re_div_nonneg
    _ _ hDne (hweak ω)

/-- The Cayley denominator is Hurwitz and the Cayley transform is bounded
by one on the imaginary-axis boundary. -/
theorem paperWeakPositiveReal_cayley_data
    (n : ℕ) (a x : ℕ → ℝ) (ε : ℝ)
    (ha0 : a 0 = 1) (hε : 0 ≤ ε)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hweak : ∀ ω : ℝ,
      0 ≤ ((Polynomial.aeval (jw ω)
        (paperDescendingNumerator n x +
          Polynomial.C ε * Polynomial.X^n) : ℂ) /
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n a)).re) :
    let P := paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n
    let D := paperDescendingDenominator n a
    paperPolynomialHurwitz (P+D) ∧
      ∀ ω : ℝ,
        ‖((Polynomial.aeval (jw ω) P : ℂ) -
            Polynomial.aeval (jw ω) D) /
          ((Polynomial.aeval (jw ω) P : ℂ) +
            Polynomial.aeval (jw ω) D)‖ ≤ 1 := by
  dsimp
  constructor
  · simpa using (paperWeakPositiveReal_perturb_hurwitz
      n a x ε ha0 hε hstable hweak 1 (by norm_num)).1
  · exact paperWeakRe_cayley_boundary_norm_le_one
      _ _ hstable hweak

/-- If the Cayley denominator is Hurwitz, its rational Cayley transform is
complex differentiable in the right half-plane and continuous to the axis. -/
theorem paperCayley_diffContOnCl_of_sum_hurwitz
    (P D : Polynomial ℝ)
    (hsum : paperPolynomialHurwitz (P+D)) :
    DiffContOnCl ℂ
      (fun z : ℂ =>
        ((Polynomial.aeval z P : ℂ) - Polynomial.aeval z D) /
          ((Polynomial.aeval z P : ℂ) + Polynomial.aeval z D))
      {z : ℂ | 0 < z.re} := by
  let U : Set ℂ := {z | 0 < z.re}
  let V : Set ℂ := {z | 0 ≤ z.re}
  have hVclosed : IsClosed V :=
    isClosed_Ici.preimage Complex.continuous_re
  have hclosure : closure U ⊆ V :=
    closure_minimal (by
      intro z hz
      change 0 < z.re at hz
      change 0 ≤ z.re
      exact le_of_lt hz) hVclosed
  have hdenom : ∀ z ∈ closure U,
      (Polynomial.aeval z P : ℂ) + Polynomial.aeval z D ≠ 0 := by
    intro z hz
    have hzn : 0 ≤ z.re := hclosure hz
    simpa only [Polynomial.aeval_add] using hsum z hzn
  have hP : DiffContOnCl ℂ
      (fun z : ℂ => Polynomial.aeval z P) U :=
    P.differentiable_aeval.diffContOnCl
  have hD : DiffContOnCl ℂ
      (fun z : ℂ => Polynomial.aeval z D) U :=
    D.differentiable_aeval.diffContOnCl
  have hquot := ((hP.add hD).inv hdenom).smul (hP.sub hD)
  convert hquot using 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply,
    Pi.sub_apply, Pi.inv_apply, div_eq_mul_inv]
  ring

/-- A global right-half-plane bound plus the weak-positive-real boundary
inequality lets Phragmen-Lindelof put the Cayley transform in the unit disk
throughout the closed right half-plane. -/
theorem paperCayley_halfplane_norm_le_one_of_bounded
    (P D : Polynomial ℝ)
    (hsum : paperPolynomialHurwitz (P+D))
    (hboundary : ∀ ω : ℝ,
      ‖((Polynomial.aeval (jw ω) P : ℂ) -
          Polynomial.aeval (jw ω) D) /
        ((Polynomial.aeval (jw ω) P : ℂ) +
          Polynomial.aeval (jw ω) D)‖ ≤ 1)
    (hbounded : ∃ M : ℝ, ∀ z : ℂ, 0 ≤ z.re →
      ‖((Polynomial.aeval z P : ℂ) -
          Polynomial.aeval z D) /
        ((Polynomial.aeval z P : ℂ) +
          Polynomial.aeval z D)‖ ≤ M)
    (z : ℂ) (hz : 0 ≤ z.re) :
    ‖((Polynomial.aeval z P : ℂ) -
        Polynomial.aeval z D) /
      ((Polynomial.aeval z P : ℂ) +
        Polynomial.aeval z D)‖ ≤ 1 := by
  let f : ℂ → ℂ := fun z =>
    ((Polynomial.aeval z P : ℂ) - Polynomial.aeval z D) /
      ((Polynomial.aeval z P : ℂ) + Polynomial.aeval z D)
  obtain ⟨M, hM⟩ := hbounded
  have hd : DiffContOnCl ℂ f {z : ℂ | 0 < z.re} :=
    paperCayley_diffContOnCl_of_sum_hurwitz P D hsum
  have hexp : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 < z.re}]
        fun z => Real.exp (B * ‖z‖ ^ c) := by
    refine ⟨0, by norm_num, 0, ?_⟩
    apply Asymptotics.IsBigO.of_bound M
    exact eventually_inf_principal.2 <|
      Filter.Eventually.of_forall fun z hz => by
        have h := hM z (le_of_lt hz)
        simpa [f] using h
  have hre : IsBoundedUnder (· ≤ ·) atTop
      (fun x : ℝ => ‖f x‖) := by
    refine ⟨M, ?_⟩
    exact (Filter.eventually_ge_atTop (0 : ℝ)).mono
      (fun x hx => by
        simpa [f] using hM (x : ℂ) (by simpa using hx))
  have him : ∀ x : ℝ, ‖f (x * Complex.I)‖ ≤ 1 := by
    intro x
    simpa [f, jw, mul_comm] using hboundary x
  change ‖f z‖ ≤ 1
  exact PhragmenLindelof.right_half_plane_of_bounded_on_real
    (f := f) hd hexp hre him hz




theorem paperReflect_ratio_identity
    (n : ℕ) (P Q : Polynomial ℝ)
    (hPdegree : P.natDegree ≤ n) (hQdegree : Q.natDegree ≤ n)
    (z : ℂ) (hz : z ≠ 0) :
    (Polynomial.aeval z P : ℂ) / Polynomial.aeval z Q =
      (Polynomial.aeval z⁻¹ (Polynomial.reflect n P) : ℂ) /
        Polynomial.aeval z⁻¹ (Polynomial.reflect n Q) := by
  letI : Invertible z := invertibleOfNonzero hz
  have hP : (Polynomial.aeval z⁻¹ (Polynomial.reflect n P) : ℂ) * z^n =
      Polynomial.aeval z P := by
    simpa [Polynomial.aeval_def, invOf_eq_inv] using
      (Polynomial.eval₂_reflect_mul_pow
        (algebraMap ℝ ℂ) z n P hPdegree)
  have hQ : (Polynomial.aeval z⁻¹ (Polynomial.reflect n Q) : ℂ) * z^n =
      Polynomial.aeval z Q := by
    simpa [Polynomial.aeval_def, invOf_eq_inv] using
      (Polynomial.eval₂_reflect_mul_pow
        (algebraMap ℝ ℂ) z n Q hQdegree)
  rw [←hP, ←hQ]
  exact mul_div_mul_right _ _ (pow_ne_zero n hz)

theorem paperReflect_eval_zero_eq_top_coeff
    (n : ℕ) (Q : Polynomial ℝ) :
    (Polynomial.reflect n Q).eval 0 = Q.coeff n := by
  rw [←Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_reflect, Polynomial.revAt_zero]


theorem paperReflect_ratio_tendsto_cocompact
    (n : ℕ) (P Q : Polynomial ℝ)
    (hPdegree : P.natDegree ≤ n) (hQdegree : Q.natDegree ≤ n)
    (hQtop : Q.coeff n ≠ 0) :
    Tendsto (fun z : ℂ =>
      (Polynomial.aeval z P : ℂ) / Polynomial.aeval z Q)
      (cocompact ℂ)
      (𝓝 ((Polynomial.aeval (0 : ℂ) (Polynomial.reflect n P) : ℂ) /
        Polynomial.aeval (0 : ℂ) (Polynomial.reflect n Q))) := by
  let R := Polynomial.reflect n P
  let S := Polynomial.reflect n Q
  let g : ℂ → ℂ := fun w =>
    (Polynomial.aeval w R : ℂ) / Polynomial.aeval w S
  have hS0 : (Polynomial.aeval (0 : ℂ) S : ℂ) ≠ 0 := by
    have hreal : S.eval 0 ≠ 0 := by
      rw [paperReflect_eval_zero_eq_top_coeff]
      exact hQtop
    have hcoeff : S.coeff 0 ≠ 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact hreal
    simpa [Polynomial.aeval_def] using hcoeff
  have hcont : ContinuousAt g 0 := by
    exact (R.differentiable_aeval.continuous.continuousAt).div
      (S.differentiable_aeval.continuous.continuousAt) hS0
  have hinv : Tendsto (fun z : ℂ => z⁻¹)
      (cocompact ℂ) (𝓝 (0 : ℂ)) := by
    rw [←Metric.cobounded_eq_cocompact]
    exact Filter.tendsto_inv₀_cobounded
  have hlim : Tendsto (fun z : ℂ => g z⁻¹)
      (cocompact ℂ) (𝓝 (g 0)) := hcont.tendsto.comp hinv
  have hnonzero : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 := by
    have hc : IsCompact ({0} : Set ℂ) := isCompact_singleton
    simpa using hc.compl_mem_cocompact
  have hevent : (fun z : ℂ => g z⁻¹) =ᶠ[cocompact ℂ]
      (fun z => (Polynomial.aeval z P : ℂ) /
        Polynomial.aeval z Q) := by
    filter_upwards [hnonzero] with z hz
    exact (paperReflect_ratio_identity
      n P Q hPdegree hQdegree z hz).symm
  exact hlim.congr' hevent

/-- A function continuous on the closed right half-plane and convergent at
complex infinity is uniformly bounded on that half-plane. -/
theorem paperClosedRightHalfPlane_bounded_of_tendsto_cocompact
    (f : ℂ → ℂ)
    (hcont : ContinuousOn f {z : ℂ | 0 ≤ z.re})
    (L : ℂ) (hlim : Tendsto f (cocompact ℂ) (𝓝 L)) :
    ∃ M : ℝ, ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ M := by
  let U : Set ℂ := {z | 0 ≤ z.re}
  have hUclosed : IsClosed U :=
    isClosed_Ici.preimage Complex.continuous_re
  have hneighborhood : Metric.ball L 1 ∈ 𝓝 L :=
    Metric.ball_mem_nhds L (by norm_num)
  have hev : {z : ℂ | f z ∈ Metric.ball L 1} ∈ cocompact ℂ :=
    hlim hneighborhood
  obtain ⟨K, hK, hKcomp⟩ := Filter.mem_cocompact.mp hev
  have hKU : IsCompact (K ∩ U) := hK.inter_right hUclosed
  have hKcont : ContinuousOn f (K ∩ U) :=
    hcont.mono Set.inter_subset_right
  obtain ⟨M, hM⟩ :=
    (hKU.image_of_continuousOn hKcont).isBounded.exists_norm_le
  refine ⟨max M (‖L‖+1), ?_⟩
  intro z hz
  have hzU : z ∈ U := hz
  by_cases hzK : z ∈ K
  · have hzKU : z ∈ K ∩ U := ⟨hzK, hzU⟩
    have hbound : ‖f z‖ ≤ M :=
      hM (f z) (Set.mem_image_of_mem f hzKU)
    exact hbound.trans (le_max_left _ _)
  · have hzcomp : z ∈ Kᶜ := hzK
    have hzball : f z ∈ Metric.ball L 1 := hKcomp hzcomp
    have hdist : ‖f z-L‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hzball
    have hnorm : ‖f z‖ ≤ ‖f z-L‖+‖L‖ := by
      calc
        ‖f z‖ = ‖(f z-L)+L‖ := by congr 1; ring
        _ ≤ ‖f z-L‖+‖L‖ := norm_add_le _ _
    exact (hnorm.trans (by linarith)).trans (le_max_right _ _)

/-- A proper polynomial ratio with a Hurwitz denominator has a uniform
bound on the closed right half-plane. -/
theorem paperPolynomialRatio_bounded_closedRightHalfPlane
    (n : ℕ) (P Q : Polynomial ℝ)
    (hPdegree : P.natDegree ≤ n) (hQdegree : Q.natDegree ≤ n)
    (hQtop : Q.coeff n ≠ 0)
    (hQstable : paperPolynomialHurwitz Q) :
    ∃ M : ℝ, ∀ z : ℂ, 0 ≤ z.re →
      ‖(Polynomial.aeval z P : ℂ) / Polynomial.aeval z Q‖ ≤ M := by
  let U : Set ℂ := {z | 0 ≤ z.re}
  let f : ℂ → ℂ := fun z =>
    (Polynomial.aeval z P : ℂ) / Polynomial.aeval z Q
  let L : ℂ :=
    (Polynomial.aeval (0 : ℂ) (Polynomial.reflect n P) : ℂ) /
      Polynomial.aeval (0 : ℂ) (Polynomial.reflect n Q)
  have hQne : ∀ z ∈ U, (Polynomial.aeval z Q : ℂ) ≠ 0 := by
    intro z hz
    exact hQstable z hz
  have hPcont : ContinuousOn (fun z : ℂ => Polynomial.aeval z P) U :=
    P.differentiable_aeval.continuous.continuousOn
  have hQcont : ContinuousOn (fun z : ℂ => Polynomial.aeval z Q) U :=
    Q.differentiable_aeval.continuous.continuousOn
  have hcont : ContinuousOn f U :=
    hPcont.div₀ hQcont hQne
  have hlim : Tendsto f (cocompact ℂ) (𝓝 L) :=
    paperReflect_ratio_tendsto_cocompact
      n P Q hPdegree hQdegree hQtop
  exact paperClosedRightHalfPlane_bounded_of_tendsto_cocompact
    f hcont L hlim

/-- The Cayley boundary estimate propagates to the closed right half-plane
for degree-bounded polynomial quotients with a Hurwitz Cayley denominator. -/
theorem paperCayley_halfplane_norm_le_one
    (n : ℕ) (P D : Polynomial ℝ)
    (hPdegree : P.natDegree ≤ n)
    (hDdegree : D.natDegree ≤ n)
    (hQtop : (P+D).coeff n ≠ 0)
    (hsum : paperPolynomialHurwitz (P+D))
    (hboundary : ∀ ω : ℝ,
      ‖((Polynomial.aeval (jw ω) P : ℂ) -
          Polynomial.aeval (jw ω) D) /
        ((Polynomial.aeval (jw ω) P : ℂ) +
          Polynomial.aeval (jw ω) D)‖ ≤ 1)
    (z : ℂ) (hz : 0 ≤ z.re) :
    ‖((Polynomial.aeval z P : ℂ) -
        Polynomial.aeval z D) /
      ((Polynomial.aeval z P : ℂ) +
        Polynomial.aeval z D)‖ ≤ 1 := by
  have hNdeg : (P-D).natDegree ≤ n := by
    exact (Polynomial.natDegree_sub_le P D).trans
      (max_le hPdegree hDdegree)
  have hQdeg : (P+D).natDegree ≤ n := by
    exact (Polynomial.natDegree_add_le P D).trans
      (max_le hPdegree hDdegree)
  have hbounded := paperPolynomialRatio_bounded_closedRightHalfPlane
    n (P-D) (P+D) hNdeg hQdeg hQtop hsum
  have hbounded' : ∃ M : ℝ, ∀ z : ℂ, 0 ≤ z.re →
      ‖((Polynomial.aeval z P : ℂ) -
          Polynomial.aeval z D) /
        ((Polynomial.aeval z P : ℂ) +
          Polynomial.aeval z D)‖ ≤ M := by
    simpa only [map_sub, Polynomial.aeval_add] using hbounded
  exact paperCayley_halfplane_norm_le_one_of_bounded
    P D hsum hboundary hbounded' z hz

/-- A unit-disk Cayley bound recovers nonnegativity of the real part. -/
theorem paperCayley_re_div_nonneg_of_norm_le_one
    (p d : ℂ) (hd : d ≠ 0) (hsum : p+d ≠ 0)
    (hbound : ‖(p-d)/(p+d)‖ ≤ 1) :
    0 ≤ (p/d).re := by
  have hsumpos : 0 < ‖p+d‖ := norm_pos_iff.mpr hsum
  have hnorm : ‖p-d‖ ≤ ‖p+d‖ := by
    rw [norm_div] at hbound
    simpa using (div_le_iff₀ hsumpos).mp hbound
  have hsq : Complex.normSq (p-d) ≤ Complex.normSq (p+d) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
  have hpair : 0 ≤ (p*conj d).re := by
    rw [Complex.normSq_sub, Complex.normSq_add] at hsq
    linarith
  have hnum : 0 ≤ p.re*d.re+p.im*d.im := by
    simpa [Complex.mul_re, Complex.conj_re, Complex.conj_im,
      mul_neg, sub_neg_eq_add] using hpair
  have hdenpos : 0 < Complex.normSq d := Complex.normSq_pos.mpr hd
  have hquot : 0 ≤
      (p.re*d.re+p.im*d.im)/Complex.normSq d :=
    div_nonneg hnum hdenpos.le
  simpa [Complex.div_re, add_div] using hquot

/-- Boundary weak positive-realness of the paper's raised numerator extends
to every point of the closed right half-plane. -/
theorem paperWeakPositiveReal_closedRightHalfPlane
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) (ε : ℝ)
    (ha0 : a 0 = 1) (hε : 0 ≤ ε)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hweak : ∀ ω : ℝ,
      0 ≤ ((Polynomial.aeval (jw ω)
        (paperDescendingNumerator n x +
          Polynomial.C ε * Polynomial.X^n) : ℂ) /
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n a)).re)
    (z : ℂ) (hz : 0 ≤ z.re) :
    0 ≤ ((Polynomial.aeval z
      (paperDescendingNumerator n x +
        Polynomial.C ε * Polynomial.X^n) : ℂ) /
      Polynomial.aeval z
        (paperDescendingDenominator n a)).re := by
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let D := paperDescendingDenominator n a
  have hPdegree : P.natDegree ≤ n := by
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le
        ((paperDescendingNumerator_natDegree_le n hn x).trans
          (Nat.sub_le n 1))
        (Polynomial.natDegree_C_mul_X_pow_le ε n))
  have hDdegree : D.natDegree ≤ n :=
    (paperDescendingDenominator_natDegree_eq n a ha0).le
  have hdata := paperWeakPositiveReal_cayley_data
    n a x ε ha0 hε hstable hweak
  have hsum : paperPolynomialHurwitz (P+D) := by
    simpa [P, D] using hdata.1
  have hboundary : ∀ ω : ℝ,
      ‖((Polynomial.aeval (jw ω) P : ℂ) -
          Polynomial.aeval (jw ω) D) /
        ((Polynomial.aeval (jw ω) P : ℂ) +
          Polynomial.aeval (jw ω) D)‖ ≤ 1 := by
    simpa [P, D] using hdata.2
  have hδfacts := paperWeakPositiveReal_perturb_hurwitz
    n a x ε ha0 hε hstable hweak 1 (by norm_num)
  have hnat : (P+D).natDegree = n := by
    simpa [P, D] using hδfacts.2.1
  have hlead : (P+D).leadingCoeff = ε+1 := by
    simpa [P, D] using hδfacts.2.2
  have hQtop : (P+D).coeff n ≠ 0 := by
    have hcoeff : (P+D).coeff n = ε+1 := by
      rw [← hnat, Polynomial.coeff_natDegree]
      exact hlead
    rw [hcoeff]
    exact ne_of_gt (by linarith)
  have hbound := paperCayley_halfplane_norm_le_one
    n P D hPdegree hDdegree hQtop hsum hboundary z hz
  have hDne : (Polynomial.aeval z D : ℂ) ≠ 0 := hstable z hz
  have hsumne : (Polynomial.aeval z P : ℂ) +
      Polynomial.aeval z D ≠ 0 := by
    simpa only [Polynomial.aeval_add] using hsum z hz
  exact paperCayley_re_div_nonneg_of_norm_le_one
    _ _ hDne hsumne hbound

/-- A polynomial quotient with a Hurwitz denominator is analytic at every
point of the closed right half-plane, including boundary contacts. -/
theorem paperPolynomialQuotient_analyticAt_of_hurwitz
    (P D : Polynomial ℝ) (hD : paperPolynomialHurwitz D)
    (z : ℂ) (hz : 0 ≤ z.re) :
    AnalyticAt ℂ
      (fun w : ℂ => (Polynomial.aeval w P : ℂ) /
        Polynomial.aeval w D) z := by
  have hP : AnalyticAt ℂ
      (fun w : ℂ => (Polynomial.aeval w P : ℂ)) z :=
    P.differentiable_aeval.analyticAt z
  have hQ : AnalyticAt ℂ
      (fun w : ℂ => (Polynomial.aeval w D : ℂ)) z :=
    D.differentiable_aeval.analyticAt z
  exact hP.div hQ (hD z hz)

/-- A multiple numerator zero on the closed right half-plane gives a
critical point of the analytic quotient. -/
theorem paperPolynomialQuotient_deriv_zero_of_double_root
    (P D : Polynomial ℝ) (hD : paperPolynomialHurwitz D)
    (z : ℂ) (hz : 0 ≤ z.re)
    (hP : (Polynomial.aeval z P : ℂ) = 0)
    (hP' : (Polynomial.aeval z P.derivative : ℂ) = 0) :
    deriv (fun w : ℂ => (Polynomial.aeval w P : ℂ) /
      Polynomial.aeval w D) z = 0 := by
  have h := (P.hasDerivAt_aeval z).div
    (D.hasDerivAt_aeval z) (hD z hz)
  simpa [hP, hP'] using h.deriv

/-- Every critical support numerator has nonnegative quotient real part
throughout the closed right half-plane at both endpoint denominators. -/
theorem PaperCriticalCertificate.support_numerator_closedRightHalfPlane
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b)) :
    ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ ((Polynomial.aeval z
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n) : ℂ) /
          Polynomial.aeval z (paperDescendingDenominator n a)).re ∧
      0 ≤ ((Polynomial.aeval z
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n) : ℂ) /
          Polynomial.aeval z (paperDescendingDenominator n b)).re := by
  let x := paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)
  let ε := C.support 0
  have hε : 0 ≤ ε := C.support_leading_nonneg ha0
  have hweak := C.support_numerator_weak_re_nonneg hn hstableA hstableB
  intro z hz
  constructor
  · exact paperWeakPositiveReal_closedRightHalfPlane
      n hn a x ε ha0 hε hstableA
      (fun ω => by simpa [x, ε] using (hweak ω).1) z hz
  · exact paperWeakPositiveReal_closedRightHalfPlane
      n hn b x ε hb0 hε hstableB
      (fun ω => by simpa [x, ε] using (hweak ω).2) z hz

/-- A nonzero complex homogeneous term of degree at least two is negative
in some direction inside the right half-plane. -/
theorem paperComplexPower_negative_right_direction
    (m : ℕ) (hm : 2 ≤ m) (c : ℂ) (hc : c ≠ 0) :
    ∃ v : ℂ, 0 < v.re ∧ (c * v^m).re < 0 := by
  by_cases hcre : c.re < 0
  · refine ⟨1, by norm_num, ?_⟩
    simpa using hcre
  by_cases hcre0 : c.re = 0
  · have hcim : c.im ≠ 0 := by
      intro hci
      exact hc (Complex.ext hcre0 hci)
    let θ : ℝ := Real.pi / (2 * m)
    let v : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hθpos : 0 < θ := by dsimp [θ]; positivity
    have hθlt : θ < Real.pi / 2 := by
      dsimp [θ]
      apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2*(m:ℝ))
        (by norm_num : (0 : ℝ) < 2)).2
      have hmore : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
      nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hmore)]
    have hvre : 0 < v.re := by
      have hcos : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith, hθlt⟩
      simpa [v, Complex.exp_mul_I] using hcos
    have hvpow : v^m = Complex.I := by
      dsimp [v]
      rw [← Complex.exp_nat_mul]
      have harg : (m : ℂ) * ((θ : ℂ) * Complex.I) =
          ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
        dsimp [θ]
        have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
        field_simp <;> ring
      rw [harg]
      simpa [Complex.ofReal_div] using Complex.exp_pi_div_two_mul_I
    by_cases hcimpos : 0 < c.im
    · refine ⟨v, hvre, ?_⟩
      rw [hvpow]
      simp [Complex.mul_I_re]
      linarith
    · refine ⟨star v, ?_, ?_⟩
      · simpa using hvre
      · rw [← star_pow, hvpow]
        simp [Complex.mul_re, Complex.I_re, Complex.I_im]
        have hcimneg : c.im < 0 := lt_of_le_of_ne (le_of_not_gt hcimpos) hcim
        linarith
  have hcrepos : 0 < c.re := lt_of_le_of_ne (le_of_not_gt hcre) (Ne.symm hcre0)
  by_cases hm2 : m = 2
  · subst m
    let v₁ : ℂ := 1 + 2 * Complex.I
    let v₂ : ℂ := 1 - 2 * Complex.I
    have hv1 : 0 < v₁.re := by norm_num [v₁]
    have hv2 : 0 < v₂.re := by norm_num [v₂]
    have hsum : (c*v₁^2).re + (c*v₂^2).re = -6*c.re := by
      simp [v₁, v₂, pow_two, Complex.mul_re, Complex.add_re,
        Complex.sub_re, Complex.I_re, Complex.I_im]
      ring
    by_cases hneg : (c*v₁^2).re < 0
    · exact ⟨v₁, hv1, hneg⟩
    · refine ⟨v₂, hv2, ?_⟩
      linarith
  have hm3 : 3 ≤ m := by omega
  let θ : ℝ := Real.pi / m
  let v : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hθpos : 0 < θ := by dsimp [θ]; positivity
  have hθlt : θ < Real.pi / 2 := by
    dsimp [θ]
    apply (div_lt_div_iff₀ hmpos (by norm_num : (0 : ℝ) < 2)).2
    have hmore : (2 : ℝ) < m := by exact_mod_cast (by omega : 2 < m)
    nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hmore)]
  have hvre : 0 < v.re := by
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, hθlt⟩
    simpa [v, Complex.exp_mul_I] using hcos
  have hvpow : v^m = -1 := by
    dsimp [v]
    rw [← Complex.exp_nat_mul]
    have harg : (m : ℂ) * ((θ : ℂ) * Complex.I) =
        (Real.pi : ℂ) * Complex.I := by
      dsimp [θ]
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      field_simp <;> ring
    rw [harg, Complex.exp_pi_mul_I]
  refine ⟨v, hvre, ?_⟩
  rw [hvpow]
  simpa using (neg_neg_of_pos hcrepos)

/-- A nonnegative real part on the closed right half-plane rules out a
boundary zero with a local analytic factor of order at least two. -/
theorem paperBoundaryHighOrderFactor_impossible
    (f g : ℂ → ℂ) (z₀ : ℂ) (m : ℕ)
    (hz₀ : z₀.re = 0) (hm : 2 ≤ m)
    (hg : ContinuousAt g z₀) (hg₀ : g z₀ ≠ 0)
    (heq : ∀ᶠ z in 𝓝 z₀, f z = (z-z₀)^m * g z)
    (hweak : ∀ z : ℂ, 0 ≤ z.re → 0 ≤ (f z).re) :
    False := by
  obtain ⟨v, hvre, hneg⟩ :=
    paperComplexPower_negative_right_direction m hm (g z₀) hg₀
  have hcont : ContinuousAt (fun z : ℂ => (v^m * g z).re) z₀ :=
    Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hg)
  have hnegnear : ∀ᶠ z in 𝓝 z₀, (v^m * g z).re < 0 :=
    hcont.tendsto.eventually (isOpen_Iio.mem_nhds (by simpa [mul_comm] using hneg))
  let ray : ℝ → ℂ := fun t => z₀ + (t : ℂ) * v
  have hray : Tendsto ray (𝓝[>] (0 : ℝ)) (𝓝 z₀) := by
    have hcontRay : Continuous ray :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hlim : Tendsto ray (𝓝 (0 : ℝ)) (𝓝 z₀) := by
      convert hcontRay.tendsto 0 using 1 <;> simp [ray]
    exact hlim.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hfactor, hnegative⟩ :=
    (hpos.and (hray.eventually (heq.and hnegnear))).exists
  let w : ℂ := ray t
  have hw : w = z₀ + (t : ℂ) * v := rfl
  have hwre : 0 ≤ w.re := by
    rw [hw, Complex.add_re, Complex.mul_re]
    simp [hz₀]
    exact (mul_pos ht hvre).le
  have hsub : w-z₀ = (t : ℂ)*v := by rw [hw]; ring
  have hreal : (f w).re = t^m * (v^m * g w).re := by
    calc
      (f w).re = (((t^m : ℝ) : ℂ) * (v^m * g w)).re := by
        rw [hfactor, hsub, mul_pow]
        push_cast
        change (↑t ^ m * v ^ m * g w).re = (↑t ^ m * (v ^ m * g w)).re
        ring
      _ = t^m * (v^m * g w).re := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
  have hstrict : (f w).re < 0 := by
    rw [hreal]
    exact mul_neg_of_pos_of_neg (pow_pos ht m) hnegative
  exact (not_le_of_gt hstrict) (hweak w hwre)

/-- A nonzero analytic function with nonnegative real part in the right
half-plane has a simple zero at any point of its imaginary boundary. -/
theorem paperAnalyticBoundaryZero_deriv_ne_zero
    (f : ℂ → ℂ) (z₀ : ℂ)
    (hz₀ : z₀.re = 0)
    (hf : AnalyticAt ℂ f z₀)
    (hf₀ : f z₀ = 0)
    (hnotzero : ¬∀ᶠ z in 𝓝 z₀, f z = 0)
    (hweak : ∀ z : ℂ, 0 ≤ z.re → 0 ≤ (f z).re) :
    deriv f z₀ ≠ 0 := by
  intro hderiv₀
  obtain ⟨m, g, hgan, hg₀, heq⟩ :=
    hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnotzero
  have heq' : f =ᶠ[𝓝 z₀]
      (fun z : ℂ => (z-z₀)^m * g z) := by
    simpa only [smul_eq_mul] using heq
  have heq₀ : f z₀ = (z₀-z₀)^m * g z₀ := heq'.eq_of_nhds
  have hmzero_ne : m ≠ 0 := by
    intro hmzero
    have hgzero : g z₀ = 0 := by simpa [hmzero, hf₀] using heq₀.symm
    exact hg₀ hgzero
  have hmpos : 0 < m := Nat.pos_of_ne_zero hmzero_ne
  have hmneone : m ≠ 1 := by
    intro hmone
    have heqone : f =ᶠ[𝓝 z₀] (fun z : ℂ => (z-z₀)*g z) := by
      simpa only [hmone, pow_one] using heq'
    have hid : HasDerivAt (fun z : ℂ => z-z₀) 1 z₀ := by
      simpa using (hasDerivAt_id z₀).sub_const z₀
    have hprod := hid.mul hgan.differentiableAt.hasDerivAt
    have hderiv : deriv f z₀ = g z₀ := by
      rw [heqone.deriv_eq]
      simpa using hprod.deriv
    exact hg₀ (by simpa [hderiv] using hderiv₀)
  have hm : 2 ≤ m := by omega
  exact paperBoundaryHighOrderFactor_impossible
    f g z₀ m hz₀ hm hgan.continuousAt hg₀
    (by simpa only [smul_eq_mul] using heq) hweak

/-- A nonzero polynomial numerator cannot give a quotient identically zero
near a point where the denominator is nonzero. -/
theorem paperPolynomialQuotient_not_locally_zero
    (P D : Polynomial ℝ) (hP : P ≠ 0)
    (z₀ : ℂ) (hD₀ : (Polynomial.aeval z₀ D : ℂ) ≠ 0) :
    ¬∀ᶠ z in 𝓝 z₀,
      (Polynomial.aeval z P : ℂ) / Polynomial.aeval z D = 0 := by
  intro hloc
  have hDnear : ∀ᶠ z in 𝓝 z₀,
      (Polynomial.aeval z D : ℂ) ≠ 0 :=
    (D.differentiable_aeval.continuous.continuousAt).eventually_ne hD₀
  have hPnear : (fun z : ℂ => (Polynomial.aeval z P : ℂ)) =ᶠ[𝓝 z₀]
      (fun _ => 0) := by
    filter_upwards [hloc, hDnear] with z hz hDz
    simpa [hDz] using hz
  have hPanalytic : AnalyticOnNhd ℂ
      (fun z : ℂ => (Polynomial.aeval z P : ℂ)) Set.univ :=
    fun z _ => P.differentiable_aeval.analyticAt z
  have hPfun : (fun z : ℂ => (Polynomial.aeval z P : ℂ)) =
      (fun _ => 0) :=
    hPanalytic.eq_of_eventuallyEq analyticOnNhd_const hPnear
  have hPeval : ∀ x : ℝ, P.eval x = 0 := by
    intro x
    have hx := congrFun hPfun (x : ℂ)
    have hxcast : ((P.eval x : ℝ) : ℂ) = 0 := by
      rw [Polynomial.aeval_def] at hx
      change Polynomial.eval₂ (algebraMap ℝ ℂ)
        ((algebraMap ℝ ℂ) x) P = 0 at hx
      rw [Polynomial.eval₂_at_apply] at hx
      exact hx
    exact_mod_cast hxcast
  have hPzero : P = 0 := by
    apply Polynomial.funext
    intro x
    simpa using hPeval x
  exact hP hPzero

/-- A nonzero polynomial numerator with a weakly positive-real quotient
has only simple imaginary-axis zeros. -/
theorem paperPolynomialQuotient_imag_zero_simple
    (P D : Polynomial ℝ)
    (hP : P ≠ 0) (hD : paperPolynomialHurwitz D)
    (hweak : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ ((Polynomial.aeval z P : ℂ) /
        Polynomial.aeval z D).re)
    (ω : ℝ)
    (hzero : (Polynomial.aeval (jw ω) P : ℂ) = 0) :
    (Polynomial.aeval (jw ω) P.derivative : ℂ) ≠ 0 := by
  let z₀ := jw ω
  let f : ℂ → ℂ := fun z =>
    (Polynomial.aeval z P : ℂ) / Polynomial.aeval z D
  have hz₀ : z₀.re = 0 := by simp [z₀, jw]
  have hz₀le : 0 ≤ z₀.re := by rw [hz₀]
  have hD₀ : (Polynomial.aeval z₀ D : ℂ) ≠ 0 := hD z₀ hz₀le
  have hf : AnalyticAt ℂ f z₀ :=
    paperPolynomialQuotient_analyticAt_of_hurwitz P D hD z₀ hz₀le
  have hf₀ : f z₀ = 0 := by simp [f, z₀, hzero]
  have hnotzero : ¬∀ᶠ z in 𝓝 z₀, f z = 0 :=
    paperPolynomialQuotient_not_locally_zero P D hP z₀ hD₀
  have hsimple : deriv f z₀ ≠ 0 :=
    paperAnalyticBoundaryZero_deriv_ne_zero
      f z₀ hz₀ hf hf₀ hnotzero hweak
  intro hmultiple
  have hderivzero : deriv f z₀ = 0 :=
    paperPolynomialQuotient_deriv_zero_of_double_root
      P D hD z₀ hz₀le hzero hmultiple
  exact hsimple hderivzero

/-- The paper's weakly positive-real raised numerator has simple
imaginary-axis zeros whenever its leading coefficient is positive. -/
theorem paperWeakPositiveReal_imag_zero_simple
    (n : ℕ) (hn : 0 < n) (a x : ℕ → ℝ) (ε : ℝ)
    (ha0 : a 0 = 1) (hε : 0 < ε)
    (hstable : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hweak : ∀ ω : ℝ,
      0 ≤ ((Polynomial.aeval (jw ω)
        (paperDescendingNumerator n x +
          Polynomial.C ε * Polynomial.X^n) : ℂ) /
        Polynomial.aeval (jw ω)
          (paperDescendingDenominator n a)).re)
    (ω : ℝ)
    (hzero : Polynomial.aeval (jw ω)
      (paperDescendingNumerator n x +
        Polynomial.C ε * Polynomial.X^n) = (0 : ℂ)) :
    Polynomial.aeval (jw ω)
      (paperDescendingNumerator n x +
        Polynomial.C ε * Polynomial.X^n).derivative ≠ (0 : ℂ) := by
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let D := paperDescendingDenominator n a
  have hP : P ≠ 0 := by
    intro hpzero
    have hnat := paperDescendingNumerator_raise_natDegree_eq n x ε hε
    change P.natDegree = n at hnat
    rw [hpzero] at hnat
    simp at hnat
    omega
  have hclosed : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ ((Polynomial.aeval z P : ℂ) /
        Polynomial.aeval z D).re := by
    intro z hz
    exact paperWeakPositiveReal_closedRightHalfPlane
      n hn a x ε ha0 hε.le hstable hweak z hz
  exact paperPolynomialQuotient_imag_zero_simple
    P D hP hstable hclosed ω hzero

/-- Positive-leading critical support numerators have simple
imaginary-axis zeros. -/
theorem PaperCriticalCertificate.support_numerator_imag_zero_simple
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hε : 0 < C.support 0) :
    ∀ ω : ℝ,
      Polynomial.aeval (jw ω)
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n) = 0 →
      Polynomial.aeval (jw ω)
        (paperDescendingNumerator n
          (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
         Polynomial.C (C.support 0) * Polynomial.X^n).derivative ≠ 0 := by
  have hweak := C.support_numerator_weak_re_nonneg
    hn hstableA hstableB
  intro ω hzero
  exact paperWeakPositiveReal_imag_zero_simple
    n hn a (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
    (C.support 0) ha0 hε hstableA
    (fun ν => (hweak ν).1) ω hzero

/-- The positive-leading, interior-only even-order critical-certificate
branch is impossible without an extra zero-simplicity assumption. -/
theorem PaperCriticalCertificate.no_interior_even_certificate_positive_leading
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hinter : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1)
    (hε : 0 < C.support 0) : False := by
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hsimple := C.support_numerator_imag_zero_simple
    hn ha0 hstableA hstableB hε
  exact C.no_interior_even_certificate_of_imaginary_simple
    hn ha0 hb0 hsegment heven hinter hε hsimple

theorem paperEvenGroupedCertificate_gcd_degree_gap_of_positive_fiber
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) (hk : 0 < k)
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (side : ι → Bool) (w t : ι → ℝ)
    (x : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hposIndex : ∃ i ∈ s, 0 < t i)
    (hwpos : ∀ i ∈ s, 0 < w i)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k) a b q))
    (hbalance : ∀ r : Fin (2*k),
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial (2*k)
          (if side i then b else a)
          (paperFiniteNumeratorCoeffs (2*k)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0)
    (hcontact : ∀ i ∈ s,
      (paperRaisedCrossPolynomial (2*k)
        (if side i then b else a) x ε).eval (t i) = 0) :
    2*k < (s.image t).card +
      (GCDMonoid.gcd
        (paperAxisOdd (2*k)
          (paperDescendingNumerator (2*k) x +
            Polynomial.C ε * Polynomial.X^(2*k)))
        (paperAxisEven (2*k)
          (paperDescendingNumerator (2*k) x +
            Polynomial.C ε * Polynomial.X^(2*k)))).natDegree := by
  let n := 2*k
  let d : ι → ℕ → ℝ := fun i =>
    if side i then b else a
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let E := paperAxisEven n P
  let O := paperAxisOdd n P
  let z : ι → ℝ := fun i =>
    w i * (paperAxisEven n
      (paperDescendingDenominator n (d i))).eval (t i)
  let y : ι → ℝ := fun i =>
    w i * t i * (paperAxisOdd n
      (paperDescendingDenominator n (d i))).eval (t i)
  have hn : 0 < n := by dsimp [n]; omega
  have hmonic : ∀ i ∈ s, d i 0 = 1 := by
    intro i hi
    by_cases h : side i
    · simp [d, h, hb0]
    · simp [d, h, ha0]
  have hstable : ∀ i ∈ s,
      paperPolynomialHurwitz
        (paperDescendingDenominator n (d i)) := by
    intro i hi
    by_cases h : side i
    · simpa [d, h, paperSegmentDenominator] using
        (hsegment 1 (by norm_num) (by norm_num))
    · simpa [d, h, paperSegmentDenominator] using
        (hsegment 0 (by norm_num) (by norm_num))
  have hpdegree : P.natDegree = n := by
    exact paperDescendingNumerator_raise_natDegree_eq n x ε hε
  have hEbound : E.natDegree ≤ k := by
    simpa [E, n] using
      paperAxisEven_natDegree_le n P hpdegree.le
  have hEcoeff : E.coeff k = ε * (-1 : ℝ)^k := by
    have hPtop : P.coeff n = ε := by
      dsimp [P]
      rw [Polynomial.coeff_add, paperDescendingNumerator_coeff,
        if_neg (by omega : ¬ n < n),
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_pos rfl]
      ring
    change (paperAxisEven n P).coeff k = ε * (-1 : ℝ)^k
    rw [paperAxisEven_coeff, if_pos (by dsimp [n]; omega),
      show 2*k = n by rfl, hPtop]
  have hEcoe : E.coeff k ≠ 0 :=
    hEcoeff.symm ▸
      mul_ne_zero (ne_of_gt hε) (pow_ne_zero _ (by norm_num))
  have hEnat : E.natDegree = k :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      hEbound hEcoe
  have hEdegree : E.degree = (k : WithBot ℕ) := by
    have hEne : E ≠ 0 := by
      intro he
      simp [he] at hEcoe
    rw [Polynomial.degree_eq_natDegree hEne, hEnat]
  have hObound : O.natDegree ≤ k := by
    have h := paperAxisOdd_natDegree_le n P hpdegree.le
    change O.natDegree ≤ (n-1)/2 at h
    have hdiv : (n-1)/2 ≤ k := by dsimp [n]; omega
    exact h.trans hdiv
  have hOdegree : O.degree ≤ (k : WithBot ℕ) := by
    by_cases hOzero : O = 0
    · simp [hOzero]
    · rw [Polynomial.degree_eq_natDegree hOzero]
      exact_mod_cast hObound
  have hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0 := by
    intro j hj
    have hsmall : 2*j < n := by dsimp [n]; omega
    exact paperCoefficientBalance_even_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0 := by
    intro j hj
    have hsmall : 2*j+1 < n := by dsimp [n]; omega
    exact paperCoefficientBalance_odd_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hc : ∀ i ∈ s,
      E.eval (t i) * z i + O.eval (t i) * y i = 0 := by
    intro i hi
    have hid := paperRaisedCross_axis_identity_any
      n hn (d i) x ε (hmonic i hi) (hstable i hi)
    have hzero := hcontact i hi
    rw [hid] at hzero
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] at hzero
    calc
      E.eval (t i) * z i + O.eval (t i) * y i =
          w i * ((paperAxisEven n P).eval (t i) *
            (paperAxisEven n
              (paperDescendingDenominator n (d i))).eval (t i) +
            t i * (paperAxisOdd n P).eval (t i) *
              (paperAxisOdd n
                (paperDescendingDenominator n (d i))).eval (t i)) := by
          dsimp [E, O, z, y]
          ring
      _ = 0 := by
          rw [hzero]
          ring
  have hnode : ∃ r ∈ s.image t,
      paperGroupedResidue s t z r ≠ 0 ∨
        paperGroupedResidue s t y r ≠ 0 := by
    obtain ⟨i, hi, hti⟩ := hposIndex
    let sPos : Finset ι := s.filter (fun j => 0 < t j)
    have hiPos : i ∈ sPos := Finset.mem_filter.mpr ⟨hi, hti⟩
    have htPos : ∀ j ∈ sPos, 0 < t j := by
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    have hwPos : ∀ j ∈ sPos, 0 < w j := by
      intro j hj
      exact hwpos j (Finset.mem_filter.mp hj).1
    have hrPos : t i ∈ sPos.image t :=
      Finset.mem_image.mpr ⟨i, hiPos, rfl⟩
    have hr : t i ∈ s.image t :=
      Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hfilter : sPos.filter (fun j => t j = t i) =
        s.filter (fun j => t j = t i) := by
      ext j
      simp only [sPos, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hj, _⟩, hji⟩
        exact ⟨hj, hji⟩
      · rintro ⟨hj, hji⟩
        exact ⟨⟨hj, by rw [hji]; exact hti⟩, hji⟩
    have hres := paperGroupedAxisResidue_nontrivial
      n a b ha0 hb0 sPos t w side htPos hwPos
      hsegment (t i) hrPos
    refine ⟨t i, hr, ?_⟩
    simpa only [paperGroupedResidue, hfilter] using hres

  change 2*k < (s.image t).card +
    (GCDMonoid.gcd O E).natDegree
  exact paperContactResidue_grouped_gcd_degree_gap
    s t z y E O k hEdegree hOdegree hz hy hc hnode

/-- Every finite critical atom, including one at frequency zero, is a root
of its endpoint cross polynomial after decompactification. -/
theorem PaperCriticalCertificate.finite_contact_root
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (i : Fin C.atomCount)
    (hx1 : C.compactFrequency i < 1) :
    let d := if C.rightEndpoint i then b else a
    let p := paperRaisedCrossPolynomial n d
      (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
      (C.support 0)
    p.eval (C.compactFrequency i / (1-C.compactFrequency i)) = 0 := by
  dsimp
  let d := if C.rightEndpoint i then b else a
  let p := paperRaisedCrossPolynomial n d
    (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ))
    (C.support 0)
  let x := C.compactFrequency i
  have hp : p.natDegree ≤ n :=
    paperRaisedCrossPolynomial_natDegree_le n d _ _
  have hzero : paperHomogenizedPolynomial n p x = 0 := by
    simpa [p, d, x, paperFeatureDot_compactFeature] using
      C.support_zero_atom i
  have hfactor : 0 < (1-x)^n := pow_pos (sub_pos.mpr hx1) n
  have heq := paperHomogenizedPolynomial_eq n p hp x (ne_of_lt hx1)
  rw [hzero] at heq
  exact (mul_eq_zero.mp heq.symm).resolve_left (ne_of_gt hfactor)

/-- The grouped residue obstruction still yields a parity-gcd degree gap
when one or more critical atoms occur at zero frequency. -/
theorem PaperCriticalCertificate.even_gcd_degree_gap_with_zero_atoms
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hε : 0 < C.support 0) :
    n < C.positiveFiniteNodes.card + 1 +
      (GCDMonoid.gcd
        (paperAxisOdd n
          (paperDescendingNumerator n
            (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
           Polynomial.C (C.support 0) * Polynomial.X^n))
        (paperAxisEven n
          (paperDescendingNumerator n
            (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
           Polynomial.C (C.support 0) * Polynomial.X^n))).natDegree := by
  let k := n/2
  let w : Fin C.atomCount → ℝ :=
    fun i => C.weight i * (1-C.compactFrequency i)^n
  let t : Fin C.atomCount → ℝ :=
    fun i => C.compactFrequency i / (1-C.compactFrequency i)
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  have hk : 0 < k := by dsimp [k]; omega
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hfinite : ∀ i : Fin C.atomCount,
      C.compactFrequency i < 1 :=
    C.positive_leading_atoms_finite ha0 hb0 hε
  have hposIndex : ∃ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      0 < t i := by
    obtain ⟨r, hr⟩ := C.positiveFiniteNodes_nonempty
      hn ha0 hb0 hstableA hstableB
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hr
    have hxi := (Finset.mem_filter.mp hi).2
    refine ⟨i, Finset.mem_univ i, ?_⟩
    exact div_pos hxi.1 (sub_pos.mpr hxi.2)
  have hwpos : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      0 < w i := by
    intro i _
    exact mul_pos (C.weight_pos i)
      (pow_pos (sub_pos.mpr (hfinite i)) n)
  have hsegment' : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k) a b q) := by
    rw [←heven]
    exact hsegment
  have hbalance : ∀ r : Fin (2*k),
      (∑ i ∈ Finset.univ, w i *
        (paperGeneralCrossPolynomial (2*k)
          (if C.rightEndpoint i then b else a)
          (paperFiniteNumeratorCoeffs (2*k)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0 := by
    have hb := (C.ordinary_coefficient_balance_of_atoms_finite
      hfinite).2
    rw [←heven]
    intro r
    simpa [w, t] using hb r
  have hcontact : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      (paperRaisedCrossPolynomial (2*k)
        (if C.rightEndpoint i then b else a)
        x ε).eval (t i) = 0 := by
    intro i _
    rw [←heven]
    simpa [x, ε, t] using C.finite_contact_root i (hfinite i)
  have hgap := paperEvenGroupedCertificate_gcd_degree_gap_of_positive_fiber
    Finset.univ k hk a b ha0 hb0 C.rightEndpoint
    w t x ε hε hposIndex hwpos hsegment' hbalance hcontact
  have hsub : (Finset.univ.image t) ⊆
      insert 0 C.positiveFiniteNodes := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    by_cases hzero : C.compactFrequency i = 0
    · have htzero : t i = 0 := by simp [t, hzero]
      rw [htzero]
      exact Finset.mem_insert_self _ _
    · have hxi : 0 < C.compactFrequency i :=
        lt_of_le_of_ne (C.frequency_mem i).1 (Ne.symm hzero)
      have hi : i ∈ C.positiveFiniteIndices := by
        simp [PaperCriticalCertificate.positiveFiniteIndices,
          hxi, hfinite i]
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hcard := Finset.card_le_card hsub
  have hcardInsert := Finset.card_insert_le 0 C.positiveFiniteNodes
  rw [← heven] at hgap
  change n < (Finset.univ.image t).card +
      (GCDMonoid.gcd
        (paperAxisOdd n
          (paperDescendingNumerator n x +
            Polynomial.C ε * Polynomial.X^n))
        (paperAxisEven n
          (paperDescendingNumerator n x +
            Polynomial.C ε * Polynomial.X^n))).natDegree at hgap
  simpa only [x, ε] using (show n < C.positiveFiniteNodes.card + 1 +
      (GCDMonoid.gcd
        (paperAxisOdd n
          (paperDescendingNumerator n x +
            Polynomial.C ε * Polynomial.X^n))
        (paperAxisEven n
          (paperDescendingNumerator n x +
            Polynomial.C ε * Polynomial.X^n))).natDegree from by omega)

/-- A positive-leading even-order critical certificate whose support
numerator vanishes at the origin is impossible, even with zero-frequency
atoms. -/
theorem PaperCriticalCertificate.no_even_certificate_of_origin_zero_positive_leading
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hε : 0 < C.support 0)
    (hP0 : (paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n (fun j => C.support j.succ)) +
       Polynomial.C (C.support 0) * Polynomial.X^n).eval 0 = 0) : False := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hweak := C.support_numerator_weak_re_nonneg
    hn hstableA hstableB
  have hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ 0 := by
    intro z hz
    exact paperWeakPositiveReal_no_open_right_root
      n a x ε ha0 hε hstableA
      (fun ω => by simpa [x, ε] using (hweak ω).1) z hz
  have hPdegree : P.natDegree ≤ n :=
    (paperDescendingNumerator_raise_natDegree_eq n x ε hε).le
  have hqAne := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn a ha0 hstableA C.support C.support_ne
  have hqBne := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn b hb0 hstableB C.support C.support_ne
  have hEne : paperAxisEven n P ≠ 0 :=
    paperAxisEven_ne_zero_of_even_raised_positive_leading
      n x ε heven hε
  have hGne : GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P) ≠ 0 := gcd_ne_zero_of_right hEne
  have hsimple := C.support_numerator_imag_zero_simple
    hn ha0 hstableA hstableB hε
  have hnodup : ((GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P)).map (algebraMap ℝ ℂ)).roots.Nodup := by
    exact paperAxisGcd_roots_nodup_of_imaginary_simple
      n P hPdegree hopen hGne
      (by simpa [P, x, ε] using hsimple)
  have hbound := paperAxisGcd_degree_le_overlap_add_one_of_nodup
    n hn a b x ε P rfl hPdegree hopen
    hstableA hstableB
    (by simpa [x, ε] using hqAne)
    (by simpa [x, ε] using hqBne)
    hGne hnodup
  have hcontact := C.positiveFiniteNodes_card_add_overlap_le_of_origin_zero
    hn ha0 hb0 hstableA hstableB heven hP0
  have hgap := C.even_gcd_degree_gap_with_zero_atoms
    hn ha0 hb0 hsegment heven hε
  let S := (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a x ε)) ∩
    (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n b x ε))
  let G := GCDMonoid.gcd (paperAxisOdd n P)
    (paperAxisEven n P)
  change C.positiveFiniteNodes.card + S.card ≤ n-2 at hcontact
  change G.natDegree ≤ S.card + 1 at hbound
  change n < C.positiveFiniteNodes.card + 1 + G.natDegree at hgap
  omega

/-- Every positive-leading even-order critical certificate on a stable
segment is impossible, including certificates with zero-frequency atoms. -/
theorem PaperCriticalCertificate.no_even_certificate_positive_leading
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hε : 0 < C.support 0) : False := by
  have hfinite : ∀ i : Fin C.atomCount,
      C.compactFrequency i < 1 :=
    C.positive_leading_atoms_finite ha0 hb0 hε
  by_cases horigin : ∃ i : Fin C.atomCount,
      C.compactFrequency i = 0
  · obtain ⟨i, hi0⟩ := horigin
    let d : ℕ → ℝ := if C.rightEndpoint i then b else a
    let x := paperFiniteNumeratorCoeffs n
      (fun j => C.support j.succ)
    let ε := C.support 0
    have hd0 : d 0 = 1 := by
      by_cases h : C.rightEndpoint i
      · simp [d, h, hb0]
      · simp [d, h, ha0]
    have hstableD : paperPolynomialHurwitz
        (paperDescendingDenominator n d) := by
      by_cases h : C.rightEndpoint i
      · simpa [d, h, paperSegmentDenominator] using
          hsegment 1 (by norm_num) (by norm_num)
      · simpa [d, h, paperSegmentDenominator] using
          hsegment 0 (by norm_num) (by norm_num)
    have hcontact := C.finite_contact_root i (hfinite i)
    have hcross0 : (paperRaisedCrossPolynomial n d x ε).eval 0 = 0 := by
      simpa [d, x, ε, hi0] using hcontact
    have hconst : 0 < d n :=
      paperDescendingDenominator_const_pos_of_hurwitz
        n hn d hd0 hstableD
    have hx0 : x (n-1) = 0 := by
      rw [paperRaisedCrossPolynomial_eval_zero n hn d x ε] at hcross0
      exact (mul_eq_zero.mp hcross0).resolve_left (ne_of_gt hconst)
    have hP0 : (paperDescendingNumerator n x +
        Polynomial.C ε * Polynomial.X^n).eval 0 = 0 := by
      rw [paperRaisedNumerator_eval_zero n hn x ε]
      exact hx0
    exact C.no_even_certificate_of_origin_zero_positive_leading
      hn ha0 hb0 hsegment heven hε
      (by simpa [x, ε] using hP0)
  · have hinter : ∀ i : Fin C.atomCount,
        0 < C.compactFrequency i ∧
          C.compactFrequency i < 1 := by
      intro i
      have hnonneg := (C.frequency_mem i).1
      have hne : C.compactFrequency i ≠ 0 := by
        intro hzero
        exact horigin ⟨i, hzero⟩
      exact ⟨lt_of_le_of_ne hnonneg (Ne.symm hne), hfinite i⟩
    exact C.no_interior_even_certificate_positive_leading
      hn ha0 hb0 hsegment heven hinter hε

/-- Any even-order critical certificate on a stable segment must have zero
highest numerator coefficient. -/
theorem PaperCriticalCertificate.even_support_leading_zero
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2)) :
    C.support 0 = 0 := by
  have hε := C.support_leading_nonneg ha0
  rcases hε.eq_or_lt with hzero | hpos
  · exact hzero.symm
  · exact False.elim
      (C.no_even_certificate_positive_leading
        hn ha0 hb0 hsegment heven hpos)

/-- Every initial subsegment of a stable coefficient segment is stable. -/
theorem paperStableInitialSubsegment
    (n : ℕ) (a b : ℕ → ℝ)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b r))
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator n a
          (fun i => (1-r)*a i+r*b i) q) := by
  intro q hq0 hq1
  have heq : paperSegmentDenominator n a
      (fun i => (1-r)*a i+r*b i) q =
      paperSegmentDenominator n a b (q*r) := by
    unfold paperSegmentDenominator
    congr 1
    funext i
    ring
  rw [heq]
  have hqr0 : 0 ≤ q*r := mul_nonneg hq0 hr0
  have hqr1 : q*r ≤ 1 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hq1) hr0
    nlinarith
  exact hsegment (q*r) hqr0 hqr1

/-- A degree-four instance of the arbitrary-order synthesis theorem follows
from exclusion of positive-leading even certificates and the degree-drop
root count. -/
theorem paperTheorem2_fourth_order
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator 4
          (fun j => (1-r)*a j+r*b j))) :
    ∃ p : Polynomial ℝ,
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        paperPolynomialSPR 4 p
          (paperDescendingDenominator 4
            (fun j => (1-r)*a j+r*b j)) := by
  have hseg : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator 4 a b r) := by
    simpa [paperSegmentDenominator] using hsegment
  apply (paperTheorem2_iff_no_high_contact_certificate
    4 (by norm_num) a b ha0 hb0 hsegment).2
  rintro ⟨r, hr, C, hmany⟩
  let d : ℕ → ℝ := fun j => (1-r)*a j+r*b j
  have hd0 : d 0 = 1 := by
    dsimp [d]
    rw [ha0, hb0]
    ring
  have hsub := paperStableInitialSubsegment
    4 a b hseg r hr.1.le hr.2
  have hzero : C.support 0 = 0 := by
    exact C.even_support_leading_zero
      (by norm_num) ha0 hd0
      (by simpa [d] using hsub)
      (by norm_num)
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator 4 a) := by
    simpa [paperSegmentDenominator] using
      hsub 0 (by norm_num) (by norm_num)
  have hstableD : paperPolynomialHurwitz
      (paperDescendingDenominator 4 d) := by
    simpa [paperSegmentDenominator] using
      hsub 1 (by norm_num) (by norm_num)
  have hbound := C.even_zero_leading_card_le_two_below
    (by norm_num) ha0 hd0 hstableA hstableD
    (by norm_num) hzero
  omega

theorem paperTheorem2_fourth_order_iff
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    (∃ p : Polynomial ℝ,
      paperPolynomialSPR 4 p (paperDescendingDenominator 4 a) ∧
      paperPolynomialSPR 4 p (paperDescendingDenominator 4 b)) ↔
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator 4
          (fun j => (1-r)*a j+r*b j))) := by
  constructor
  · rintro ⟨p, hpA, hpB⟩
    exact paperTheorem2_necessity 4 a b p ha0 hb0 hpA hpB
  · intro hsegment
    obtain ⟨p, hp⟩ := paperTheorem2_fourth_order
      a b ha0 hb0 hsegment
    refine ⟨p, ?_, ?_⟩
    · simpa using hp 0 (by norm_num) (by norm_num)
    · simpa using hp 1 (by norm_num) (by norm_num)

/-- A nonzero weakly positive-real quotient whose numerator vanishes at
infinity must have relative degree exactly one.  The reflection converts
the zero at infinity into a boundary zero at the origin. -/
theorem paperWeakPositiveReal_zero_leading_next_coeff_ne_zero
    (n : ℕ) (hn : 0 < n) (P D : Polynomial ℝ)
    (hPdegree : P.natDegree ≤ n)
    (hDdegree : D.natDegree ≤ n)
    (hPtop : P.coeff n = 0) (hPne : P ≠ 0)
    (hDtop : D.coeff n ≠ 0)
    (hweak : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ ((Polynomial.aeval z P : ℂ) /
        Polynomial.aeval z D).re) :
    P.coeff (n-1) ≠ 0 := by
  let R := Polynomial.reflect n P
  let S := Polynomial.reflect n D
  let f : ℂ → ℂ := fun w =>
    (Polynomial.aeval w R : ℂ) / Polynomial.aeval w S
  have hRne : R ≠ 0 := by
    intro hRzero
    exact hPne (Polynomial.reflect_eq_zero_iff.mp hRzero)
  have hR0 : (Polynomial.aeval (0 : ℂ) R : ℂ) = 0 := by
    have hreal : R.eval 0 = 0 := by
      exact (paperReflect_eval_zero_eq_top_coeff n P).trans hPtop
    have hcoeff : R.coeff 0 = 0 := by
      simpa [Polynomial.coeff_zero_eq_eval_zero] using hreal
    simpa [Polynomial.aeval_def] using hcoeff
  have hS0 : (Polynomial.aeval (0 : ℂ) S : ℂ) ≠ 0 := by
    have hreal : S.eval 0 ≠ 0 := by
      rw [paperReflect_eval_zero_eq_top_coeff]
      exact hDtop
    have hcoeff : S.coeff 0 ≠ 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact hreal
    simpa [Polynomial.aeval_def] using hcoeff
  have hf0 : f 0 = 0 := by simp [f, hR0]
  have hfanalytic : AnalyticAt ℂ f 0 :=
    (R.differentiable_aeval.analyticAt 0).div
      (S.differentiable_aeval.analyticAt 0) hS0
  have hnotzero : ¬∀ᶠ w in 𝓝 (0 : ℂ), f w = 0 :=
    paperPolynomialQuotient_not_locally_zero R S hRne 0 hS0
  have hweakR : ∀ w : ℂ, 0 ≤ w.re → 0 ≤ (f w).re := by
    intro w hwre
    by_cases hwzero : w = 0
    · simp [hwzero, hf0]
    have hwinvre : 0 ≤ (w⁻¹).re := by
      rw [Complex.inv_re]
      exact div_nonneg hwre (Complex.normSq_nonneg w)
    have hId := paperReflect_ratio_identity
      n P D hPdegree hDdegree w⁻¹ (inv_ne_zero hwzero)
    have hId' : f w =
        (Polynomial.aeval w⁻¹ P : ℂ) /
          Polynomial.aeval w⁻¹ D := by
      simpa [f, R, S] using hId.symm
    rw [hId']
    exact hweak w⁻¹ hwinvre
  have hsimple : deriv f 0 ≠ 0 :=
    paperAnalyticBoundaryZero_deriv_ne_zero
      f 0 (by simp) hfanalytic hf0 hnotzero hweakR
  intro hPnext
  have hRcoeff1 : R.coeff 1 = 0 := by
    change (Polynomial.reflect n P).coeff 1 = 0
    rw [Polynomial.coeff_reflect, Polynomial.revAt_le (by omega : 1 ≤ n)]
    simpa using hPnext
  have hRderivcoeff0 : R.derivative.coeff 0 = 0 := by
    simpa [Polynomial.coeff_derivative] using hRcoeff1
  have hRderiv0 : (Polynomial.aeval (0 : ℂ) R.derivative : ℂ) = 0 := by
    simpa [Polynomial.aeval_def] using hRderivcoeff0
  have hderivFormula :=
    ((R.hasDerivAt_aeval (0 : ℂ)).div
      (S.hasDerivAt_aeval (0 : ℂ)) hS0).deriv
  have hderivZero : deriv f 0 = 0 := by
    simpa [f, hR0, hRderiv0] using hderivFormula
  exact hsimple hderivZero

/-- A zero-leading critical support numerator has degree exactly `n-1`.
This removes all deeper degree-drop cases from the arbitrary-order
certificate analysis. -/
theorem PaperCriticalCertificate.zero_leading_support_natDegree_eq_pred
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hzero : C.support 0 = 0) :
    (paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ))).natDegree = n-1 := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let P := paperDescendingNumerator n x
  let D := paperDescendingDenominator n a
  have htailne : (fun j : Fin n => C.support j.succ) ≠ 0 := by
    intro htail
    apply C.support_ne
    ext i
    refine Fin.cases ?_ ?_ i
    · simpa using hzero
    · intro j
      exact congrFun htail j
  have hPne : P ≠ 0 := by
    intro hPzero
    exact htailne
      (paperFiniteNumeratorCoeffs_eq_zero_of_descending_zero n _ hPzero)
  have hPdegree : P.natDegree ≤ n-1 :=
    paperDescendingNumerator_natDegree_le n hn x
  have hPdegree' : P.natDegree ≤ n := by omega
  have hDdegree : D.natDegree ≤ n :=
    (paperDescendingDenominator_natDegree_eq n a ha0).le
  have hPtop : P.coeff n = 0 := by
    change (paperDescendingNumerator n x).coeff n = 0
    rw [paperDescendingNumerator_coeff, if_neg (by omega : ¬n<n)]
  have hDtop : D.coeff n ≠ 0 := by
    change (paperDescendingDenominator n a).coeff n ≠ 0
    rw [paperDescendingDenominator_coeff, if_pos le_rfl,
      Nat.sub_self, ha0]
    norm_num
  have hweak : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ ((Polynomial.aeval z P : ℂ) /
        Polynomial.aeval z D).re := by
    intro z hz
    have h := (C.support_numerator_closedRightHalfPlane
      hn ha0 hb0 hstableA hstableB z hz).1
    simpa [P, D, x, hzero] using h
  have hPnext : P.coeff (n-1) ≠ 0 :=
    paperWeakPositiveReal_zero_leading_next_coeff_ne_zero
      n hn P D hPdegree' hDdegree hPtop hPne hDtop hweak
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    hPdegree hPnext

/-- In degree at least two, the surviving highest coefficient of a
zero-leading critical support numerator is strictly positive. -/
theorem PaperCriticalCertificate.zero_leading_support_next_coeff_pos
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 1 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hzero : C.support 0 = 0) :
    0 < (paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ))).coeff (n-1) := by
  let P := paperDescendingNumerator n
    (paperFiniteNumeratorCoeffs n
      (fun j => C.support j.succ))
  let D := paperDescendingDenominator n a
  have hPdegree : P.natDegree = n-1 :=
    C.zero_leading_support_natDegree_eq_pred
      (by omega) ha0 hb0 hstableA hstableB hzero
  have hPdegpos : 0 < P.degree := by
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    rw [hPdegree]
    omega
  have hDmonic : D.Monic :=
    paperDescendingDenominator_monic n a ha0
  have hDdegree : 0 < D.degree := by
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    rw [paperDescendingDenominator_natDegree_eq n a ha0]
    omega
  have hD0pos : 0 < D.eval 0 :=
    paperPolynomialHurwitz_monic_eval_zero_pos
      D hDmonic hDdegree hstableA
  have hDpos : ∀ t : ℝ, 0 ≤ t → 0 < D.eval t :=
    paperHurwitz_eval_pos_of_eval_zero_pos D hstableA hD0pos
  have hPnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ P.eval t := by
    intro t ht
    have hq := (C.support_numerator_closedRightHalfPlane
      (by omega : 0 < n) ha0 hb0 hstableA hstableB
      (t : ℂ) (by simpa using ht)).1
    have hPcast : (Polynomial.aeval (t : ℂ) P : ℂ) =
        ((P.eval t : ℝ) : ℂ) := by
      change Polynomial.eval₂ (algebraMap ℝ ℂ)
        ((algebraMap ℝ ℂ) t) P = (algebraMap ℝ ℂ) (P.eval t)
      exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) t
    have hDcast : (Polynomial.aeval (t : ℂ) D : ℂ) =
        ((D.eval t : ℝ) : ℂ) := by
      change Polynomial.eval₂ (algebraMap ℝ ℂ)
        ((algebraMap ℝ ℂ) t) D = (algebraMap ℝ ℂ) (D.eval t)
      exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) t
    have hqreal : 0 ≤ P.eval t / D.eval t := by
      simpa [P, D, hzero, hPcast, hDcast] using hq
    have hprod := mul_nonneg hqreal (hDpos t ht).le
    simpa only [div_mul_cancel₀ _ (ne_of_gt (hDpos t ht))] using hprod
  have hlead : 0 < P.leadingCoeff :=
    paperPolynomial_leadingCoeff_pos_of_nonneg_on_nonneg
      P hPdegpos hPnonneg
  simpa only [← Polynomial.coeff_natDegree, hPdegree] using hlead

/-- Degree drop also bounds the distinct positive contacts together with
the overlap of the two endpoint root sets. -/
theorem PaperCriticalCertificate.zero_leading_positiveFiniteNodes_card_add_overlap_le
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hzero : C.support 0 = 0) :
    C.positiveFiniteNodes.card +
      ((MonicQuinticCoeff.positiveRealRoots
          (paperRaisedCrossPolynomial n a
            (paperFiniteNumeratorCoeffs n
              (fun j => C.support j.succ)) (C.support 0))) ∩
        (MonicQuinticCoeff.positiveRealRoots
          (paperRaisedCrossPolynomial n b
            (paperFiniteNumeratorCoeffs n
              (fun j => C.support j.succ)) (C.support 0)))).card
      ≤ 2*((n-1)/2) := by
  let rootsA := MonicQuinticCoeff.positiveRealRoots
    (paperRaisedCrossPolynomial n a
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ)) (C.support 0))
  let rootsB := MonicQuinticCoeff.positiveRealRoots
    (paperRaisedCrossPolynomial n b
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ)) (C.support 0))
  have hsub : C.positiveFiniteNodes ⊆ rootsA ∪ rootsB :=
    C.positiveFiniteNodes_subset_endpoint_roots
      hn ha0 hb0 hstableA hstableB
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_add_card_inter rootsA rootsB
  have hbound := C.endpoint_positiveRoots_bounds_of_leading_zero
    hn ha0 hb0 hstableA hstableB hzero
  change 2*rootsA.card ≤ n-1 ∧ 2*rootsB.card ≤ n-1 at hbound
  change C.positiveFiniteNodes.card + (rootsA ∩ rootsB).card
    ≤ 2*((n-1)/2)
  omega

/-- With an even-order zero-leading support vector, the odd-frequency
component has its maximal possible degree. -/
theorem PaperCriticalCertificate.even_zero_leading_axisOdd_natDegree
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 1 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (heven : n = 2*(n/2))
    (hzero : C.support 0 = 0) :
    (paperAxisOdd n
      (paperDescendingNumerator n
        (paperFiniteNumeratorCoeffs n
          (fun j => C.support j.succ)))).natDegree = n/2-1 := by
  let P := paperDescendingNumerator n
    (paperFiniteNumeratorCoeffs n
      (fun j => C.support j.succ))
  let O := paperAxisOdd n P
  let k := n/2
  have hk : 0 < k := by dsimp [k]; omega
  have hPdegree : P.natDegree = n-1 :=
    C.zero_leading_support_natDegree_eq_pred
      (by omega) ha0 hb0 hstableA hstableB hzero
  have hnextpos : 0 < P.coeff (n-1) :=
    C.zero_leading_support_next_coeff_pos
      hn ha0 hb0 hstableA hstableB hzero
  have hObound : O.natDegree ≤ k-1 := by
    have h := paperAxisOdd_natDegree_le n P
      (hPdegree.le.trans (Nat.pred_le n))
    change O.natDegree ≤ (n-1)/2 at h
    dsimp [k]
    omega
  have hOcoeff : O.coeff (k-1) ≠ 0 := by
    change (paperAxisOdd n P).coeff (k-1) ≠ 0
    rw [paperAxisOdd_coeff, if_pos (by dsimp [k]; omega)]
    have hidx : 2*(k-1)+1 = n-1 := by dsimp [k]; omega
    rw [hidx]
    exact mul_ne_zero (ne_of_gt hnextpos)
      (pow_ne_zero _ (by norm_num))
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    hObound hOcoeff

/-- A nonzero analytic function with nonnegative real part on the closed
right half-plane cannot vanish in its open interior. -/
theorem paperAnalyticInteriorZero_impossible
    (f : ℂ → ℂ) (z₀ : ℂ)
    (hz₀ : 0 < z₀.re)
    (hf : AnalyticAt ℂ f z₀)
    (hf₀ : f z₀ = 0)
    (hnotzero : ¬∀ᶠ z in 𝓝 z₀, f z = 0)
    (hweak : ∀ z : ℂ, 0 ≤ z.re → 0 ≤ (f z).re) : False := by
  obtain ⟨m, g, hgan, hg₀, heq⟩ :=
    hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnotzero
  have heq' : f =ᶠ[𝓝 z₀]
      (fun z : ℂ => (z-z₀)^m * g z) := by
    simpa only [smul_eq_mul] using heq
  have heq₀ : f z₀ = (z₀-z₀)^m * g z₀ := heq'.eq_of_nhds
  have hmzero_ne : m ≠ 0 := by
    intro hmzero
    have hgzero : g z₀ = 0 := by
      simpa [hmzero, hf₀] using heq₀.symm
    exact hg₀ hgzero
  have hmpos : 0 < m := Nat.pos_of_ne_zero hmzero_ne
  obtain ⟨v, hvneg⟩ :
      ∃ v : ℂ, (v^m * g z₀).re < 0 := by
    by_cases hmone : m = 1
    · refine ⟨-conj (g z₀), ?_⟩
      rw [hmone, pow_one]
      have hmul : (g z₀ * (-conj (g z₀))).re < 0 := by
        rw [mul_neg, Complex.neg_re, Complex.mul_conj]
        exact neg_neg_of_pos (Complex.normSq_pos.mpr hg₀)
      simpa [mul_comm] using hmul
    · obtain ⟨v, _, hv⟩ :=
        paperComplexPower_negative_right_direction
          m (by omega) (g z₀) hg₀
      exact ⟨v, by simpa [mul_comm] using hv⟩
  have hcont : ContinuousAt (fun z : ℂ => (v^m * g z).re) z₀ :=
    Complex.continuous_re.continuousAt.comp
      (continuousAt_const.mul hgan.continuousAt)
  have hnegnear : ∀ᶠ z in 𝓝 z₀, (v^m * g z).re < 0 :=
    hcont.tendsto.eventually (isOpen_Iio.mem_nhds hvneg)
  let ray : ℝ → ℂ := fun t => z₀ + (t : ℂ) * v
  have hray : Tendsto ray (𝓝[>] (0 : ℝ)) (𝓝 z₀) := by
    have hcontRay : Continuous ray :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hlim : Tendsto ray (𝓝 (0 : ℝ)) (𝓝 z₀) := by
      convert hcontRay.tendsto 0 using 1 <;> simp [ray]
    exact hlim.mono_left nhdsWithin_le_nhds
  have hrightnear : ∀ᶠ z in 𝓝 z₀, 0 < z.re :=
    (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hz₀
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hfactor, hnegative, hright⟩ :=
    (hpos.and (hray.eventually
      (heq'.and (hnegnear.and hrightnear)))).exists
  let w : ℂ := ray t
  change f w = (w-z₀)^m * g w at hfactor
  have hsub : w-z₀ = (t : ℂ)*v := by dsimp [w, ray]; ring
  have hreal : (f w).re = t^m * (v^m * g w).re := by
    calc
      (f w).re = (((t^m : ℝ) : ℂ) * (v^m * g w)).re := by
        rw [hfactor, hsub, mul_pow]
        push_cast
        change (↑t ^ m * v ^ m * g w).re =
          (↑t ^ m * (v ^ m * g w)).re
        ring
      _ = t^m * (v^m * g w).re := by
        simp only [Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
  have hstrict : (f w).re < 0 := by
    rw [hreal]
    exact mul_neg_of_pos_of_neg (pow_pos ht m) hnegative
  exact (not_le_of_gt hstrict) (hweak w hright.le)

/-- A nonzero weakly positive-real polynomial quotient has no numerator root
in the open right half-plane, regardless of its value at the origin. -/
theorem paperWeakPositiveReal_nonzero_no_open_right_root
    (P D : Polynomial ℝ) (hPne : P ≠ 0)
    (hDst : paperPolynomialHurwitz D)
    (hweak : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ ((Polynomial.aeval z P : ℂ) /
        Polynomial.aeval z D).re) :
    ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ) := by
  intro z hz hroot
  let f : ℂ → ℂ := fun w =>
    (Polynomial.aeval w P : ℂ) / Polynomial.aeval w D
  have hD₀ : (Polynomial.aeval z D : ℂ) ≠ 0 :=
    hDst z hz.le
  have hf : AnalyticAt ℂ f z :=
    paperPolynomialQuotient_analyticAt_of_hurwitz
      P D hDst z hz.le
  have hf₀ : f z = 0 := by simp [f, hroot]
  have hnotzero : ¬∀ᶠ w in 𝓝 z, f w = 0 :=
    paperPolynomialQuotient_not_locally_zero P D hPne z hD₀
  exact paperAnalyticInteriorZero_impossible
    f z hz hf hf₀ hnotzero hweak

/-- If the odd axis component is nonzero at the origin, every parity-gcd
root is a shared positive endpoint contact.  Squarefreeness then bounds
the gcd degree by the number of shared contacts. -/
theorem paperAxisGcd_degree_le_overlap_of_odd_origin_ne_zero
    (n : ℕ) (hn : 0 < n) (a b x : ℕ → ℝ) (ε : ℝ)
    (P : Polynomial ℝ)
    (hPform : P = paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n)
    (hPdegree : P.natDegree ≤ n)
    (hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ))
    (hOdd0 : (Polynomial.aeval (0 : ℂ)
      (paperAxisOdd n P) : ℂ) ≠ 0)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hqAne : paperRaisedCrossPolynomial n a x ε ≠ 0)
    (hqBne : paperRaisedCrossPolynomial n b x ε ≠ 0)
    (hGne : GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P) ≠ 0)
    (hnodup : ((GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P)).map (algebraMap ℝ ℂ)).roots.Nodup) :
    (GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P)).natDegree ≤
      ((MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n a x ε)) ∩
        (MonicQuinticCoeff.positiveRealRoots
          (paperRaisedCrossPolynomial n b x ε))).card := by
  classical
  let G := GCDMonoid.gcd (paperAxisOdd n P)
    (paperAxisEven n P)
  let q := G.map (algebraMap ℝ ℂ)
  let R := q.roots.toFinset
  let S := (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a x ε)) ∩
    (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n b x ε))
  have hqne : q ≠ 0 := Polynomial.map_ne_zero hGne
  have hG0 : (Polynomial.aeval (0 : ℂ) G : ℂ) ≠ 0 := by
    intro hzero
    obtain ⟨M, hM⟩ :=
      GCDMonoid.gcd_dvd_left (paperAxisOdd n P)
        (paperAxisEven n P)
    apply hOdd0
    rw [hM, Polynomial.aeval_mul]
    rw [show (Polynomial.aeval (0 : ℂ) G : ℂ) = 0 from hzero]
    simp
  have hroot (z : ℂ) (hz : z ∈ R) :
      Polynomial.aeval z G = 0 := by
    have hz' : z ∈ q.roots := Multiset.mem_toFinset.mp hz
    have hqzero := (Polynomial.mem_roots hqne).mp hz'
    simpa [q, G] using hqzero
  have hsubset : R.image Complex.re ⊆ S := by
    intro r hr
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
    have hnonneg := (paperAxisGcd_root_nonnegative_real
      n P hPdegree hopen z (hroot z hz)).1
    have hreal : 0 < z.re := by
      by_contra hnot
      have hzre : z.re = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
      have hzim := (paperAxisGcd_root_nonnegative_real
        n P hPdegree hopen z (hroot z hz)).2
      have hz0 : z = 0 := by
        apply Complex.ext
        · simpa using hzre
        · simpa using hzim
      exact hG0 (by simpa [hz0] using hroot z hz)
    exact paperAxisGcd_root_in_endpoint_overlap_of_positive_re
      n hn a b x ε P hPform hPdegree hopen
        hstableA hstableB hqAne hqBne z hreal (hroot z hz)
  have hinj : Set.InjOn Complex.re R := by
    intro z hz v hv hreal
    have hzi := (paperAxisGcd_root_nonnegative_real
      n P hPdegree hopen z (hroot z hz)).2
    have hvi := (paperAxisGcd_root_nonnegative_real
      n P hPdegree hopen v (hroot v hv)).2
    apply Complex.ext
    · exact hreal
    · rw [hzi, hvi]
  have hcardImage : (R.image Complex.re).card = R.card :=
    Finset.card_image_of_injOn hinj
  have hcardSubset := Finset.card_le_card hsubset
  have hdistinct : R.card ≤ S.card := by omega
  have hsplit : q.Splits (RingHom.id ℂ) := IsAlgClosed.splits q
  have hdegree : G.natDegree = q.roots.card := by
    have h := Polynomial.natDegree_eq_card_roots' hsplit
    simpa [q, Polynomial.natDegree_map] using h
  have hcard : R.card = q.roots.card :=
    Multiset.toFinset_card_of_nodup hnodup
  change G.natDegree ≤ S.card
  rw [hdegree, ←hcard]
  exact hdistinct

/-- The grouped residue obstruction for an even-order numerator of degree
exactly one below its denominator.  The odd axis component now carries the
highest coefficient, so the parity roles are interchanged. -/
theorem paperEvenZeroLeadingGroupedCertificate_gcd_degree_gap
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) (hk : 0 < k)
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (side : ι → Bool) (w t : ι → ℝ)
    (x : ℕ → ℝ)
    (hPnext : (paperDescendingNumerator (2*k) x).coeff (2*k-1) ≠ 0)
    (hsne : s.Nonempty)
    (htpos : ∀ i ∈ s, 0 < t i)
    (hwpos : ∀ i ∈ s, 0 < w i)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k) a b q))
    (hbalance : ∀ r : Fin (2*k),
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial (2*k)
          (if side i then b else a)
          (paperFiniteNumeratorCoeffs (2*k)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0)
    (hcontact : ∀ i ∈ s,
      (paperRaisedCrossPolynomial (2*k)
        (if side i then b else a) x 0).eval (t i) = 0) :
    2*(k-1) < (s.image t).card +
      (GCDMonoid.gcd
        (paperAxisEven (2*k)
          (paperDescendingNumerator (2*k) x))
        (paperAxisOdd (2*k)
          (paperDescendingNumerator (2*k) x))).natDegree := by
  let n := 2*k
  let d : ι → ℕ → ℝ := fun i => if side i then b else a
  let P := paperDescendingNumerator n x
  let E := paperAxisOdd n P
  let O := paperAxisEven n P
  let z : ι → ℝ := fun i =>
    w i * t i * (paperAxisOdd n
      (paperDescendingDenominator n (d i))).eval (t i)
  let y : ι → ℝ := fun i =>
    w i * (paperAxisEven n
      (paperDescendingDenominator n (d i))).eval (t i)
  have hn : 0 < n := by dsimp [n]; omega
  have hmonic : ∀ i ∈ s, d i 0 = 1 := by
    intro i hi
    by_cases h : side i
    · simp [d, h, hb0]
    · simp [d, h, ha0]
  have hstable : ∀ i ∈ s,
      paperPolynomialHurwitz
        (paperDescendingDenominator n (d i)) := by
    intro i hi
    by_cases h : side i
    · simpa [d, h, paperSegmentDenominator] using
        hsegment 1 (by norm_num) (by norm_num)
    · simpa [d, h, paperSegmentDenominator] using
        hsegment 0 (by norm_num) (by norm_num)
  have hPdegree : P.natDegree ≤ n-1 :=
    paperDescendingNumerator_natDegree_le n hn x
  have hEbound : E.natDegree ≤ k-1 := by
    have h := paperAxisOdd_natDegree_le n P
      (hPdegree.trans (Nat.pred_le n))
    change E.natDegree ≤ (n-1)/2 at h
    dsimp [n] at h
    omega
  have hEcoeff : E.coeff (k-1) ≠ 0 := by
    change (paperAxisOdd n P).coeff (k-1) ≠ 0
    rw [paperAxisOdd_coeff, if_pos (by dsimp [n]; omega)]
    have hidx : 2*(k-1)+1 = n-1 := by dsimp [n]; omega
    rw [hidx]
    exact mul_ne_zero (by simpa [P, n] using hPnext)
      (pow_ne_zero _ (by norm_num))
  have hEnat : E.natDegree = k-1 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      hEbound hEcoeff
  have hEdegree : E.degree = (((k-1 : ℕ)) : WithBot ℕ) := by
    have hEne : E ≠ 0 := by
      intro he
      simp [he] at hEcoeff
    rw [Polynomial.degree_eq_natDegree hEne, hEnat]
  have hObound : O.natDegree ≤ k-1 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    change (paperAxisEven n P).coeff j = 0
    rw [paperAxisEven_coeff]
    by_cases hjn : j ≤ n
    · rw [if_pos hjn]
      have hlt : P.natDegree < 2*j := by dsimp [n] at *; omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
      simp
    · rw [if_neg hjn]
  have hOdegree : O.degree ≤ (((k-1 : ℕ)) : WithBot ℕ) := by
    by_cases hOzero : O = 0
    · simp [hOzero]
    · rw [Polynomial.degree_eq_natDegree hOzero]
      exact_mod_cast hObound
  have hz : ∀ j < k-1, (∑ i ∈ s, (t i)^j * z i) = 0 := by
    intro j hj
    have hsmall : 2*j+1 < n := by dsimp [n]; omega
    exact paperCoefficientBalance_odd_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hy : ∀ j < k-1, (∑ i ∈ s, (t i)^j * y i) = 0 := by
    intro j hj
    have hsmall : 2*j < n := by dsimp [n]; omega
    exact paperCoefficientBalance_even_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hc : ∀ i ∈ s,
      E.eval (t i) * z i + O.eval (t i) * y i = 0 := by
    intro i hi
    have hid := paperRaisedCross_axis_identity_any
      n hn (d i) x 0 (hmonic i hi) (hstable i hi)
    have hzero := hcontact i hi
    rw [hid] at hzero
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] at hzero
    calc
      E.eval (t i) * z i + O.eval (t i) * y i =
          w i * ((paperAxisEven n P).eval (t i) *
            (paperAxisEven n
              (paperDescendingDenominator n (d i))).eval (t i) +
            t i * (paperAxisOdd n P).eval (t i) *
              (paperAxisOdd n
                (paperDescendingDenominator n (d i))).eval (t i)) := by
          dsimp [E, O, z, y]
          ring
      _ = 0 := by
          have hzero' :
              (paperAxisEven n P).eval (t i) *
                (paperAxisEven n
                  (paperDescendingDenominator n (d i))).eval (t i) +
                t i * (paperAxisOdd n P).eval (t i) *
                  (paperAxisOdd n
                    (paperDescendingDenominator n (d i))).eval (t i) = 0 := by
            simpa [P] using hzero
          rw [hzero']
          ring
  have hnode : ∃ r ∈ s.image t,
      paperGroupedResidue s t z r ≠ 0 ∨
        paperGroupedResidue s t y r ≠ 0 := by
    obtain ⟨i, hi⟩ := hsne
    have hr : t i ∈ s.image t :=
      Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hres := paperGroupedAxisResidue_nontrivial
      n a b ha0 hb0 s t w side htpos hwpos
      hsegment (t i) hr
    refine ⟨t i, hr, ?_⟩
    rcases hres with hreal | himag
    · exact Or.inr (by simpa [y, d] using hreal)
    · exact Or.inl (by simpa [z, d] using himag)
  change 2*(k-1) < (s.image t).card +
    (GCDMonoid.gcd O E).natDegree
  exact paperContactResidue_grouped_gcd_degree_gap
    s t z y E O (k-1) hEdegree hOdegree hz hy hc hnode

/-- Interior even-order critical certificates with zero highest numerator
coefficient require a parity gcd larger than the degree-drop contact budget. -/
theorem PaperCriticalCertificate.interior_even_zero_leading_gcd_degree_gap
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hinter : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1)
    (hzero : C.support 0 = 0) :
    2*(n/2-1) < C.positiveFiniteNodes.card +
      (GCDMonoid.gcd
        (paperAxisEven n
          (paperDescendingNumerator n
            (paperFiniteNumeratorCoeffs n
              (fun j => C.support j.succ))))
        (paperAxisOdd n
          (paperDescendingNumerator n
            (paperFiniteNumeratorCoeffs n
              (fun j => C.support j.succ))))).natDegree := by
  let k := n/2
  let w : Fin C.atomCount → ℝ :=
    fun i => C.weight i * (1-C.compactFrequency i)^n
  let t : Fin C.atomCount → ℝ :=
    fun i => C.compactFrequency i /
      (1-C.compactFrequency i)
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  have hk : 0 < k := by dsimp [k]; omega
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hindices : C.positiveFiniteIndices = Finset.univ := by
    ext i
    simp [PaperCriticalCertificate.positiveFiniteIndices,
      (hinter i).1, (hinter i).2]
  have hsne : (Finset.univ : Finset (Fin C.atomCount)).Nonempty := by
    obtain ⟨r, hr⟩ := C.positiveFiniteNodes_nonempty
      hn ha0 hb0 hstableA hstableB
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hr
    exact ⟨i, Finset.mem_univ i⟩
  have htpos : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      0 < t i := by
    intro i _
    exact div_pos (hinter i).1 (sub_pos.mpr (hinter i).2)
  have hwpos : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      0 < w i := by
    intro i _
    exact mul_pos (C.weight_pos i)
      (pow_pos (sub_pos.mpr (hinter i).2) n)
  have hsegment' : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k) a b q) := by
    rw [←heven]
    exact hsegment
  have hbalance : ∀ r : Fin (2*k),
      (∑ i ∈ Finset.univ, w i *
        (paperGeneralCrossPolynomial (2*k)
          (if C.rightEndpoint i then b else a)
          (paperFiniteNumeratorCoeffs (2*k)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0 := by
    have hb := (C.ordinary_coefficient_balance_of_atoms_interior
      hinter).2
    rw [←heven]
    intro r
    simpa [w, t] using hb r
  have hcontact : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      (paperRaisedCrossPolynomial (2*k)
        (if C.rightEndpoint i then b else a)
        x 0).eval (t i) = 0 := by
    intro i _
    rw [←heven]
    simpa [x, t, hzero] using
      (C.positive_contact_root_and_deriv
        i (hinter i).1 (hinter i).2).1
  have hnext :
      (paperDescendingNumerator (2*k) x).coeff (2*k-1) ≠ 0 := by
    have hpos := C.zero_leading_support_next_coeff_pos
      (by omega : 1 < n) ha0 hb0 hstableA hstableB hzero
    rw [←heven]
    simpa [x] using ne_of_gt hpos
  have hgap := paperEvenZeroLeadingGroupedCertificate_gcd_degree_gap
    Finset.univ k hk a b ha0 hb0 C.rightEndpoint
    w t x hnext hsne htpos hwpos hsegment' hbalance hcontact
  have hcardEq : C.positiveFiniteNodes.card =
      (Finset.univ.image t).card := by
    simp only [PaperCriticalCertificate.positiveFiniteNodes, hindices]
    rfl
  rw [←heven] at hgap
  rw [←hcardEq] at hgap
  simpa only [k, x] using hgap

/-- The zero-leading, interior-only even certificate is impossible whenever
the support numerator is positive at the origin. -/
theorem PaperCriticalCertificate.no_interior_even_zero_leading_certificate_of_origin_pos
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hinter : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1)
    (hzero : C.support 0 = 0)
    (hP0 : 0 < (paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ))).eval 0) : False := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let P := paperDescendingNumerator n x
  let D := paperDescendingDenominator n a
  have hn2 : 1 < n := by omega
  have hstableA : paperPolynomialHurwitz D := by
    simpa [D, paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hPdeg : P.natDegree = n-1 :=
    C.zero_leading_support_natDegree_eq_pred
      hn ha0 hb0 hstableA hstableB hzero
  have hPne : P ≠ 0 := by
    intro hPzero
    rw [hPzero] at hPdeg
    simp at hPdeg
    omega
  have hPdegree : P.natDegree ≤ n := by omega
  have hweak := C.support_numerator_weak_re_nonneg
    hn hstableA hstableB
  have hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ) := by
    intro z hz
    exact paperWeakPositiveReal_zero_leading_no_open_right_root
      n hn a x ha0 hstableA
      (fun ω => by simpa [P, x, hzero] using (hweak ω).1)
      (by simpa [P, x] using hP0) z hz
  have hweakClosed : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ ((Polynomial.aeval z P : ℂ) /
        Polynomial.aeval z D).re := by
    intro z hz
    have h := (C.support_numerator_closedRightHalfPlane
      hn ha0 hb0 hstableA hstableB z hz).1
    simpa [P, D, x, hzero] using h
  have hsimple : ∀ ω : ℝ,
      Polynomial.aeval (jw ω) P = 0 →
      Polynomial.aeval (jw ω) P.derivative ≠ 0 := by
    intro ω hroot
    exact paperPolynomialQuotient_imag_zero_simple
      P D hPne hstableA hweakClosed ω hroot
  have hqAne := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn a ha0 hstableA C.support C.support_ne
  have hqBne := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn b hb0 hstableB C.support C.support_ne
  have hGne : GCDMonoid.gcd
      (paperAxisOdd n P) (paperAxisEven n P) ≠ 0 :=
    gcd_ne_zero_of_right
      (paperAxisEven_ne_zero_of_eval_zero_pos
        n P (by simpa [P, x] using hP0))
  have hnodup := paperAxisGcd_roots_nodup_of_imaginary_simple
    n P hPdegree hopen hGne hsimple
  have hbound := paperAxisGcd_degree_le_overlap_of_nodup
    n hn a b x 0 P (by simp [P]) hPdegree
    (by simpa [P, x] using hP0) hopen
    hstableA hstableB
    (by simpa [x, hzero] using hqAne)
    (by simpa [x, hzero] using hqBne)
    hGne hnodup
  have hbudget :=
    C.zero_leading_positiveFiniteNodes_card_add_overlap_le
      hn ha0 hb0 hstableA hstableB hzero
  have hgap :=
    C.interior_even_zero_leading_gcd_degree_gap
      hn ha0 hb0 hsegment heven hinter hzero
  let S := (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a x 0)) ∩
    (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n b x 0))
  let G := GCDMonoid.gcd (paperAxisOdd n P)
    (paperAxisEven n P)
  change G.natDegree ≤ S.card at hbound
  have hbudget' : C.positiveFiniteNodes.card + S.card ≤
      2*((n-1)/2) := by
    simpa [S, x, hzero] using hbudget
  have hgap' : 2*(n/2-1) <
      C.positiveFiniteNodes.card + G.natDegree := by
    change 2*(n/2-1) < C.positiveFiniteNodes.card +
      (GCDMonoid.gcd (paperAxisEven n P)
        (paperAxisOdd n P)).natDegree at hgap
    rw [gcd_comm] at hgap
    exact hgap
  omega

/-- The zero-leading, interior-only even certificate is also impossible when
its weak support numerator vanishes at the origin.  The origin zero is
simple, so the parity gcd has no origin root. -/
theorem PaperCriticalCertificate.no_interior_even_zero_leading_certificate_of_origin_zero
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hinter : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1)
    (hzero : C.support 0 = 0)
    (hP0 : (paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ))).eval 0 = 0) : False := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let P := paperDescendingNumerator n x
  let D := paperDescendingDenominator n a
  have hstableA : paperPolynomialHurwitz D := by
    simpa [D, paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hPdeg : P.natDegree = n-1 :=
    C.zero_leading_support_natDegree_eq_pred
      hn ha0 hb0 hstableA hstableB hzero
  have hPne : P ≠ 0 := by
    intro hPzero
    rw [hPzero] at hPdeg
    simp at hPdeg
    omega
  have hPdegree : P.natDegree ≤ n := by omega
  have hweakClosed : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ ((Polynomial.aeval z P : ℂ) /
        Polynomial.aeval z D).re := by
    intro z hz
    have h := (C.support_numerator_closedRightHalfPlane
      hn ha0 hb0 hstableA hstableB z hz).1
    simpa [P, D, x, hzero] using h
  have hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ) :=
    paperWeakPositiveReal_nonzero_no_open_right_root
      P D hPne hstableA hweakClosed
  have hsimple : ∀ ω : ℝ,
      Polynomial.aeval (jw ω) P = 0 →
      Polynomial.aeval (jw ω) P.derivative ≠ 0 := by
    intro ω hroot
    exact paperPolynomialQuotient_imag_zero_simple
      P D hPne hstableA hweakClosed ω hroot
  have hPzero : Polynomial.aeval (jw 0) P = (0 : ℂ) := by
    have hcoeff : P.coeff 0 = 0 := by
      simpa [P, x, Polynomial.coeff_zero_eq_eval_zero] using hP0
    simpa [jw, Polynomial.aeval_def] using hcoeff
  have hderiv0 :
      (Polynomial.aeval (0 : ℂ) P.derivative : ℂ) ≠ 0 := by
    simpa [jw] using hsimple 0 hPzero
  have hOdd0coeff : (paperAxisOdd n P).coeff 0 =
      P.derivative.coeff 0 := by
    rw [paperAxisOdd_coeff, if_pos (Nat.zero_le n),
      Polynomial.coeff_derivative]
    norm_num
  have hOdd0 : (Polynomial.aeval (0 : ℂ)
      (paperAxisOdd n P) : ℂ) ≠ 0 := by
    have hderivCoeff : P.derivative.coeff 0 ≠ 0 := by
      simpa [Polynomial.aeval_def] using hderiv0
    have hOddCoeff : (paperAxisOdd n P).coeff 0 ≠ 0 := by
      rw [hOdd0coeff]
      exact hderivCoeff
    simpa [Polynomial.aeval_def] using hOddCoeff
  have hqAne := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn a ha0 hstableA C.support C.support_ne
  have hqBne := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn b hb0 hstableB C.support C.support_ne
  have hOddne : paperAxisOdd n P ≠ 0 := by
    intro hz
    apply hOdd0
    simp [hz]
  have hGne : GCDMonoid.gcd
      (paperAxisOdd n P) (paperAxisEven n P) ≠ 0 :=
    gcd_ne_zero_of_left hOddne
  have hnodup := paperAxisGcd_roots_nodup_of_imaginary_simple
    n P hPdegree hopen hGne hsimple
  have hbound := paperAxisGcd_degree_le_overlap_of_odd_origin_ne_zero
    n hn a b x 0 P (by simp [P]) hPdegree hopen hOdd0
    hstableA hstableB
    (by simpa [x, hzero] using hqAne)
    (by simpa [x, hzero] using hqBne)
    hGne hnodup
  have hbudget :=
    C.zero_leading_positiveFiniteNodes_card_add_overlap_le
      hn ha0 hb0 hstableA hstableB hzero
  have hgap :=
    C.interior_even_zero_leading_gcd_degree_gap
      hn ha0 hb0 hsegment heven hinter hzero
  let S := (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a x 0)) ∩
    (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n b x 0))
  let G := GCDMonoid.gcd (paperAxisOdd n P)
    (paperAxisEven n P)
  change G.natDegree ≤ S.card at hbound
  have hbudget' : C.positiveFiniteNodes.card + S.card ≤
      2*((n-1)/2) := by
    simpa [S, x, hzero] using hbudget
  have hgap' : 2*(n/2-1) <
      C.positiveFiniteNodes.card + G.natDegree := by
    change 2*(n/2-1) < C.positiveFiniteNodes.card +
      (GCDMonoid.gcd (paperAxisEven n P)
        (paperAxisOdd n P)).natDegree at hgap
    rw [gcd_comm] at hgap
    exact hgap
  omega

/-- No even-order critical certificate on a stable segment can have only
strictly positive finite contact frequencies. -/
theorem PaperCriticalCertificate.no_interior_even_certificate
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hinter : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i ∧ C.compactFrequency i < 1) :
    False := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let P := paperDescendingNumerator n x
  let D := paperDescendingDenominator n a
  have hzero : C.support 0 = 0 :=
    C.even_support_leading_zero hn ha0 hb0 hsegment heven
  have hstableA : paperPolynomialHurwitz D := by
    simpa [D, paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hDmonic : D.Monic :=
    paperDescendingDenominator_monic n a ha0
  have hDdegree : 0 < D.degree := by
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    rw [paperDescendingDenominator_natDegree_eq n a ha0]
    exact hn
  have hD0pos : 0 < D.eval 0 :=
    paperPolynomialHurwitz_monic_eval_zero_pos
      D hDmonic hDdegree hstableA
  have hP0nonneg : 0 ≤ P.eval 0 := by
    have hq := (C.support_numerator_closedRightHalfPlane
      hn ha0 hb0 hstableA hstableB
      (0 : ℂ) (by simp)).1
    have hPcast : (Polynomial.aeval (0 : ℂ) P : ℂ) =
        ((P.eval 0 : ℝ) : ℂ) := by
      change Polynomial.eval₂ (algebraMap ℝ ℂ)
        ((algebraMap ℝ ℂ) (0 : ℝ)) P =
          (algebraMap ℝ ℂ) (P.eval 0)
      exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) 0
    have hDcast : (Polynomial.aeval (0 : ℂ) D : ℂ) =
        ((D.eval 0 : ℝ) : ℂ) := by
      change Polynomial.eval₂ (algebraMap ℝ ℂ)
        ((algebraMap ℝ ℂ) (0 : ℝ)) D =
          (algebraMap ℝ ℂ) (D.eval 0)
      exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) 0
    have hqreal : 0 ≤ P.eval 0 / D.eval 0 := by
      simpa [P, D, x, hzero, hPcast, hDcast] using hq
    have hprod := mul_nonneg hqreal hD0pos.le
    simpa only [div_mul_cancel₀ _ (ne_of_gt hD0pos)] using hprod
  rcases hP0nonneg.eq_or_lt with hP0zero | hP0pos
  · exact C.no_interior_even_zero_leading_certificate_of_origin_zero
      hn ha0 hb0 hsegment heven hinter hzero
      (by simpa [P, x] using hP0zero.symm)
  · exact C.no_interior_even_zero_leading_certificate_of_origin_pos
      hn ha0 hb0 hsegment heven hinter hzero
      (by simpa [P, x] using hP0pos)

/-- For every zero-leading even support vector, imaginary-axis simplicity
bounds the parity-gcd degree by the shared positive endpoint contacts. -/
theorem PaperCriticalCertificate.zero_leading_support_gcd_degree_le_overlap
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 1 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hzero : C.support 0 = 0) :
    let x := paperFiniteNumeratorCoeffs n
      (fun j => C.support j.succ)
    let P := paperDescendingNumerator n x
    (GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P)).natDegree ≤
      ((MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n a x 0)) ∩
        (MonicQuinticCoeff.positiveRealRoots
          (paperRaisedCrossPolynomial n b x 0))).card := by
  dsimp
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let P := paperDescendingNumerator n x
  let D := paperDescendingDenominator n a
  have hPdeg : P.natDegree = n-1 :=
    C.zero_leading_support_natDegree_eq_pred
      (by omega) ha0 hb0 hstableA hstableB hzero
  have hPne : P ≠ 0 := by
    intro hPzero
    rw [hPzero] at hPdeg
    simp at hPdeg
    omega
  have hPdegree : P.natDegree ≤ n := by omega
  have hweakClosed : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ ((Polynomial.aeval z P : ℂ) /
        Polynomial.aeval z D).re := by
    intro z hz
    have h := (C.support_numerator_closedRightHalfPlane
      (by omega : 0 < n) ha0 hb0 hstableA hstableB z hz).1
    simpa [P, D, x, hzero] using h
  have hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ) :=
    paperWeakPositiveReal_nonzero_no_open_right_root
      P D hPne hstableA hweakClosed
  have hsimple : ∀ ω : ℝ,
      Polynomial.aeval (jw ω) P = 0 →
      Polynomial.aeval (jw ω) P.derivative ≠ 0 := by
    intro ω hroot
    exact paperPolynomialQuotient_imag_zero_simple
      P D hPne hstableA hweakClosed ω hroot
  have hqAne := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n (by omega) a ha0 hstableA C.support C.support_ne
  have hqBne := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n (by omega) b hb0 hstableB C.support C.support_ne
  have hDmonic : D.Monic :=
    paperDescendingDenominator_monic n a ha0
  have hDdegree : 0 < D.degree := by
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    rw [paperDescendingDenominator_natDegree_eq n a ha0]
    omega
  have hD0pos : 0 < D.eval 0 :=
    paperPolynomialHurwitz_monic_eval_zero_pos
      D hDmonic hDdegree hstableA
  have hP0nonneg : 0 ≤ P.eval 0 := by
    have hq := hweakClosed 0 (by simp)
    have hPcast : (Polynomial.aeval (0 : ℂ) P : ℂ) =
        ((P.eval 0 : ℝ) : ℂ) := by
      change Polynomial.eval₂ (algebraMap ℝ ℂ)
        ((algebraMap ℝ ℂ) (0 : ℝ)) P =
          (algebraMap ℝ ℂ) (P.eval 0)
      exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) 0
    have hDcast : (Polynomial.aeval (0 : ℂ) D : ℂ) =
        ((D.eval 0 : ℝ) : ℂ) := by
      change Polynomial.eval₂ (algebraMap ℝ ℂ)
        ((algebraMap ℝ ℂ) (0 : ℝ)) D =
          (algebraMap ℝ ℂ) (D.eval 0)
      exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) 0
    have hqreal : 0 ≤ P.eval 0 / D.eval 0 := by
      simpa [hPcast, hDcast] using hq
    have hprod := mul_nonneg hqreal hD0pos.le
    simpa only [div_mul_cancel₀ _ (ne_of_gt hD0pos)] using hprod
  rcases hP0nonneg.eq_or_lt with hP0zero | hP0pos
  · have hPzero : Polynomial.aeval (jw 0) P = (0 : ℂ) := by
      have hcoeff : P.coeff 0 = 0 := by
        simpa [Polynomial.coeff_zero_eq_eval_zero] using hP0zero.symm
      simpa [jw, Polynomial.aeval_def] using hcoeff
    have hderiv0 :
        (Polynomial.aeval (0 : ℂ) P.derivative : ℂ) ≠ 0 := by
      simpa [jw] using hsimple 0 hPzero
    have hOdd0coeff : (paperAxisOdd n P).coeff 0 =
        P.derivative.coeff 0 := by
      rw [paperAxisOdd_coeff, if_pos (Nat.zero_le n),
        Polynomial.coeff_derivative]
      norm_num
    have hOdd0 : (Polynomial.aeval (0 : ℂ)
        (paperAxisOdd n P) : ℂ) ≠ 0 := by
      have hderivCoeff : P.derivative.coeff 0 ≠ 0 := by
        simpa [Polynomial.aeval_def] using hderiv0
      have hOddCoeff : (paperAxisOdd n P).coeff 0 ≠ 0 := by
        rw [hOdd0coeff]
        exact hderivCoeff
      simpa [Polynomial.aeval_def] using hOddCoeff
    have hOddne : paperAxisOdd n P ≠ 0 := by
      intro hz
      apply hOdd0
      simp [hz]
    have hGne : GCDMonoid.gcd
        (paperAxisOdd n P) (paperAxisEven n P) ≠ 0 :=
      gcd_ne_zero_of_left hOddne
    have hnodup := paperAxisGcd_roots_nodup_of_imaginary_simple
      n P hPdegree hopen hGne hsimple
    have hbound := paperAxisGcd_degree_le_overlap_of_odd_origin_ne_zero
      n (by omega) a b x 0 P (by simp [P]) hPdegree hopen hOdd0
      hstableA hstableB
      (by simpa [x, hzero] using hqAne)
      (by simpa [x, hzero] using hqBne)
      hGne hnodup
    simpa [P, x] using hbound
  · have hEvenne : paperAxisEven n P ≠ 0 :=
      paperAxisEven_ne_zero_of_eval_zero_pos n P hP0pos
    have hGne : GCDMonoid.gcd
        (paperAxisOdd n P) (paperAxisEven n P) ≠ 0 :=
      gcd_ne_zero_of_right hEvenne
    have hnodup := paperAxisGcd_roots_nodup_of_imaginary_simple
      n P hPdegree hopen hGne hsimple
    have hbound := paperAxisGcd_degree_le_overlap_of_nodup
      n (by omega) a b x 0 P (by simp [P]) hPdegree hP0pos hopen
      hstableA hstableB
      (by simpa [x, hzero] using hqAne)
      (by simpa [x, hzero] using hqBne)
      hGne hnodup
    simpa [P, x] using hbound

/-- Infinity atoms disappear from the finite coefficient moments.  If no
atom occurs at zero frequency, the swapped parity residue gap therefore
holds even when some atoms occur at infinity. -/
theorem PaperCriticalCertificate.even_zero_leading_gcd_gap_of_no_origin
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hzero : C.support 0 = 0)
    (hnoOrigin : ∀ i : Fin C.atomCount,
      C.compactFrequency i ≠ 0) :
    2*(n/2-1) < C.positiveFiniteNodes.card +
      (GCDMonoid.gcd
        (paperAxisEven n
          (paperDescendingNumerator n
            (paperFiniteNumeratorCoeffs n
              (fun j => C.support j.succ))))
        (paperAxisOdd n
          (paperDescendingNumerator n
            (paperFiniteNumeratorCoeffs n
              (fun j => C.support j.succ))))).natDegree := by
  let k := n/2
  let s := C.positiveFiniteIndices
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let t : Fin C.atomCount → ℝ := fun i =>
    C.compactFrequency i / (1-C.compactFrequency i)
  let w : Fin C.atomCount → ℝ := fun i =>
    C.weight i * (1-C.compactFrequency i)^n
  have hk : 0 < k := by dsimp [k]; omega
  have hupos : ∀ i : Fin C.atomCount,
      0 < C.compactFrequency i := by
    intro i
    exact lt_of_le_of_ne (C.frequency_mem i).1
      (Ne.symm (hnoOrigin i))
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hsne : s.Nonempty := by
    obtain ⟨r, hr⟩ := C.positiveFiniteNodes_nonempty
      hn ha0 hb0 hstableA hstableB
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hr
    exact ⟨i, hi⟩
  have htpos : ∀ i ∈ s, 0 < t i := by
    intro i hi
    have hfinite := (Finset.mem_filter.mp hi).2.2
    exact div_pos (hupos i) (sub_pos.mpr hfinite)
  have hwpos : ∀ i ∈ s, 0 < w i := by
    intro i hi
    have hfinite := (Finset.mem_filter.mp hi).2.2
    exact mul_pos (C.weight_pos i)
      (pow_pos (sub_pos.mpr hfinite) n)
  have hsegment' : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k) a b q) := by
    rw [←heven]
    exact hsegment
  have hnext :
      (paperDescendingNumerator (2*k) x).coeff (2*k-1) ≠ 0 := by
    have hpos := C.zero_leading_support_next_coeff_pos
      (by omega : 1 < n) ha0 hb0 hstableA hstableB hzero
    rw [←heven]
    simpa [x] using ne_of_gt hpos
  have hbalance : ∀ r : Fin (2*k),
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial (2*k)
          (if C.rightEndpoint i then b else a)
          (paperFiniteNumeratorCoeffs (2*k)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0 := by
    rw [←heven]
    intro r
    have hb := C.finite_coefficient_balance_with_infinity
      hn ha0 hb0 r
    calc
      _ = ∑ i : Fin C.atomCount, w i *
          (paperGeneralCrossPolynomial n
            (if C.rightEndpoint i then b else a)
            (paperFiniteNumeratorCoeffs n
              (fun j => if r = j then 1 else 0))).eval (t i) := by
        change (∑ i ∈ Finset.univ.filter
          (fun i : Fin C.atomCount =>
            0 < C.compactFrequency i ∧ C.compactFrequency i < 1),
          w i *
            (paperGeneralCrossPolynomial n
              (if C.rightEndpoint i then b else a)
              (paperFiniteNumeratorCoeffs n
                (fun j => if r = j then 1 else 0))).eval (t i)) = _
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : 0 < C.compactFrequency i ∧
            C.compactFrequency i < 1
        · simp [hi]
        · have hu1 : C.compactFrequency i = 1 := by
            have hle := (C.frequency_mem i).2
            have hnot : ¬ C.compactFrequency i < 1 := by
              intro hlt
              exact hi ⟨hupos i, hlt⟩
            exact le_antisymm hle (le_of_not_gt hnot)
          have hn0 : n ≠ 0 := by omega
          have hwzero : w i = 0 := by simp [w, hu1, hn0]
          simp [hi, hwzero]
      _ = 0 := by simpa [w, t] using hb
  have hcontact : ∀ i ∈ s,
      (paperRaisedCrossPolynomial (2*k)
        (if C.rightEndpoint i then b else a)
        x 0).eval (t i) = 0 := by
    intro i hi
    have hfinite := (Finset.mem_filter.mp hi).2.2
    rw [←heven]
    simpa [x, t, hzero] using
      (C.positive_contact_root_and_deriv
        i (hupos i) hfinite).1
  have hgap := paperEvenZeroLeadingGroupedCertificate_gcd_degree_gap
    s k hk a b ha0 hb0 C.rightEndpoint
    w t x hnext hsne htpos hwpos hsegment' hbalance hcontact
  have hcardEq : C.positiveFiniteNodes.card = (s.image t).card := rfl
  rw [←heven] at hgap
  rw [←hcardEq] at hgap
  simpa only [k, s, x] using hgap

/-- An even-order critical certificate cannot avoid zero-frequency atoms;
possible atoms at infinity are eliminated from the moment balance. -/
theorem PaperCriticalCertificate.no_even_certificate_of_no_origin
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hnoOrigin : ∀ i : Fin C.atomCount,
      C.compactFrequency i ≠ 0) : False := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let P := paperDescendingNumerator n x
  let S := (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a x 0)) ∩
    (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n b x 0))
  let G := GCDMonoid.gcd (paperAxisOdd n P)
    (paperAxisEven n P)
  have hn2 : 1 < n := by omega
  have hzero : C.support 0 = 0 :=
    C.even_support_leading_zero hn ha0 hb0 hsegment heven
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hgap := C.even_zero_leading_gcd_gap_of_no_origin
    hn ha0 hb0 hsegment heven hzero hnoOrigin
  have hbound := C.zero_leading_support_gcd_degree_le_overlap
    hn2 ha0 hb0 hstableA hstableB hzero
  have hbudget :=
    C.zero_leading_positiveFiniteNodes_card_add_overlap_le
      hn ha0 hb0 hstableA hstableB hzero
  have hgap' : 2*(n/2-1) <
      C.positiveFiniteNodes.card + G.natDegree := by
    change 2*(n/2-1) < C.positiveFiniteNodes.card +
      (GCDMonoid.gcd (paperAxisEven n P)
        (paperAxisOdd n P)).natDegree at hgap
    rw [gcd_comm] at hgap
    exact hgap
  have hbound' : G.natDegree ≤ S.card := by
    simpa [G, S, P, x] using hbound
  have hbudget' : C.positiveFiniteNodes.card + S.card ≤
      2*((n-1)/2) := by
    simpa [S, x, hzero] using hbudget
  omega

/-- Hence every even-order critical certificate on a stable segment must
carry a zero-frequency atom. -/
theorem PaperCriticalCertificate.even_certificate_has_origin_atom
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2)) :
    ∃ i : Fin C.atomCount, C.compactFrequency i = 0 := by
  by_contra hnone
  push_neg at hnone
  exact C.no_even_certificate_of_no_origin
    hn ha0 hb0 hsegment heven hnone

/-- One extra moment of `y` improves the contact-residue gcd degree gap by
one.  This is the missing count for zero-frequency atoms. -/
theorem paperContactResidue_gcd_degree_gap_extra_y
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z y : ι → ℝ)
    (ht : Set.InjOn t s) (E O : Polynomial ℝ) (k : ℕ)
    (hEdegree : E.degree = (k : WithBot ℕ))
    (hOdegree : O.degree ≤ k)
    (hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0)
    (hy : ∀ j < k+1, (∑ i ∈ s, (t i)^j * y i) = 0)
    (hc : ∀ i ∈ s, E.eval (t i) * z i +
      O.eval (t i) * y i = 0)
    (hnode : ∃ i ∈ s, z i ≠ 0 ∨ y i ≠ 0) :
    2*k+1 < s.card + (GCDMonoid.gcd O E).natDegree := by
  classical
  let U := MonicQuinticCoeff.quinticResiduePolynomial s t z
  let V := MonicQuinticCoeff.quinticResiduePolynomial s t y
  let G := GCDMonoid.gcd O E
  let E' := E / G
  let O' := O / G
  have hEne : E ≠ 0 := by
    intro he
    simp [he] at hEdegree
  have hGne : G ≠ 0 := gcd_ne_zero_of_right hEne
  have hE'ne : E' ≠ 0 := right_div_gcd_ne_zero hEne
  have hEfactor : G * E' = E := by
    simpa [G, E'] using
      (EuclideanDomain.mul_div_cancel' hGne
        (GCDMonoid.gcd_dvd_right O E))
  have hOfactor : G * O' = O := by
    simpa [G, O'] using
      (EuclideanDomain.mul_div_cancel' hGne
        (GCDMonoid.gcd_dvd_left O E))
  have hcop : IsCoprime E' O' := by
    simpa [E', O', G] using
      (isCoprime_div_gcd_div_gcd (p := O) (q := E) hEne).symm
  have hid : E*U+O*V=0 :=
    paperContactResiduePolynomial_identity s t z y ht E O k
      hEdegree.le hOdegree hz (fun j hj => hy j (by omega)) hc
  have hid' : E'*U+O'*V=0 := by
    have h : G * (E'*U+O'*V) = 0 := by
      calc
        _ = E*U+O*V := by rw [←hEfactor, ←hOfactor]; ring
        _ = 0 := hid
    exact (mul_eq_zero.mp h).resolve_left hGne
  have hdiv : E' ∣ V := by
    have h : E' ∣ O'*V := by
      refine ⟨-U, ?_⟩
      calc
        O'*V = -(E'*U) := by linear_combination hid'
        _ = E'*(-U) := by ring
    exact hcop.dvd_of_dvd_mul_left h
  have hVne : V ≠ 0 := by
    intro hVzero
    rw [hVzero, mul_zero, add_zero] at hid
    have hUzero : U = 0 :=
      (mul_eq_zero.mp hid).resolve_left hEne
    exact (paperContactResidue_nontrivial s t z y ht hnode).elim
      (fun h => h hUzero) (fun h => h hVzero)
  have hVbound := MonicQuinticCoeff.degree_quinticResiduePolynomial_of_moments
    s t y (k+1) hy
  change V.degree + (k+1) < (s.card : WithBot ℕ) at hVbound
  have hVnat : V.natDegree + (k+1) < s.card := by
    rw [Polynomial.degree_eq_natDegree hVne] at hVbound
    exact_mod_cast hVbound
  have hEnat : E.natDegree = k := by
    rw [Polynomial.degree_eq_natDegree hEne] at hEdegree
    exact_mod_cast hEdegree
  have hfactorDegree : G.natDegree + E'.natDegree = k := by
    rw [← Polynomial.natDegree_mul hGne hE'ne, hEfactor]
    exact hEnat
  have hE'leV : E'.natDegree ≤ V.natDegree :=
    Polynomial.natDegree_le_of_dvd hdiv hVne
  change 2*k+1 < s.card + G.natDegree
  omega

theorem paperContactResidue_grouped_gcd_degree_gap_extra_y
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t z y : ι → ℝ)
    (E O : Polynomial ℝ) (k : ℕ)
    (hEdegree : E.degree = (k : WithBot ℕ))
    (hOdegree : O.degree ≤ k)
    (hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0)
    (hy : ∀ j < k+1, (∑ i ∈ s, (t i)^j * y i) = 0)
    (hc : ∀ i ∈ s, E.eval (t i) * z i +
      O.eval (t i) * y i = 0)
    (hnode : ∃ r ∈ s.image t,
      paperGroupedResidue s t z r ≠ 0 ∨
        paperGroupedResidue s t y r ≠ 0) :
    2*k+1 < (s.image t).card +
      (GCDMonoid.gcd O E).natDegree := by
  classical
  let u : ℝ → ℝ := paperGroupedResidue s t z
  let v : ℝ → ℝ := paperGroupedResidue s t y
  apply paperContactResidue_gcd_degree_gap_extra_y
    (s.image t) id u v
    (by intro r _ q _ h; exact h)
    E O k hEdegree hOdegree
  · intro j hj
    simpa [u] using
      (paperGroupedResidue_moment s t z j).trans (hz j hj)
  · intro j hj
    simpa [v] using
      (paperGroupedResidue_moment s t y j).trans (hy j hj)
  · intro r hr
    exact paperGroupedResidue_contact s t z y E O hc r
  · exact hnode


theorem paperEvenZeroLeadingGroupedCertificate_gcd_degree_gap_with_zero_atoms
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) (hk : 0 < k)
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (side : ι → Bool) (w t : ι → ℝ)
    (x : ℕ → ℝ)
    (hPnext : (paperDescendingNumerator (2*k) x).coeff (2*k-1) ≠ 0)
    (hposIndex : ∃ i ∈ s, 0 < t i)
    (hwpos : ∀ i ∈ s, 0 < w i)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k) a b q))
    (hbalance : ∀ r : Fin (2*k),
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial (2*k)
          (if side i then b else a)
          (paperFiniteNumeratorCoeffs (2*k)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0)
    (hcontact : ∀ i ∈ s,
      (paperRaisedCrossPolynomial (2*k)
        (if side i then b else a) x 0).eval (t i) = 0) :
    2*(k-1)+1 < (s.image t).card +
      (GCDMonoid.gcd
        (paperAxisEven (2*k)
          (paperDescendingNumerator (2*k) x))
        (paperAxisOdd (2*k)
          (paperDescendingNumerator (2*k) x))).natDegree := by
  let n := 2*k
  let d : ι → ℕ → ℝ := fun i => if side i then b else a
  let P := paperDescendingNumerator n x
  let E := paperAxisOdd n P
  let O := paperAxisEven n P
  let z : ι → ℝ := fun i =>
    w i * t i * (paperAxisOdd n
      (paperDescendingDenominator n (d i))).eval (t i)
  let y : ι → ℝ := fun i =>
    w i * (paperAxisEven n
      (paperDescendingDenominator n (d i))).eval (t i)
  have hn : 0 < n := by dsimp [n]; omega
  have hmonic : ∀ i ∈ s, d i 0 = 1 := by
    intro i hi
    by_cases h : side i
    · simp [d, h, hb0]
    · simp [d, h, ha0]
  have hstable : ∀ i ∈ s,
      paperPolynomialHurwitz
        (paperDescendingDenominator n (d i)) := by
    intro i hi
    by_cases h : side i
    · simpa [d, h, paperSegmentDenominator] using
        hsegment 1 (by norm_num) (by norm_num)
    · simpa [d, h, paperSegmentDenominator] using
        hsegment 0 (by norm_num) (by norm_num)
  have hPdegree : P.natDegree ≤ n-1 :=
    paperDescendingNumerator_natDegree_le n hn x
  have hEbound : E.natDegree ≤ k-1 := by
    have h := paperAxisOdd_natDegree_le n P
      (hPdegree.trans (Nat.pred_le n))
    change E.natDegree ≤ (n-1)/2 at h
    dsimp [n] at h
    omega
  have hEcoeff : E.coeff (k-1) ≠ 0 := by
    change (paperAxisOdd n P).coeff (k-1) ≠ 0
    rw [paperAxisOdd_coeff, if_pos (by dsimp [n]; omega)]
    have hidx : 2*(k-1)+1 = n-1 := by dsimp [n]; omega
    rw [hidx]
    exact mul_ne_zero (by simpa [P, n] using hPnext)
      (pow_ne_zero _ (by norm_num))
  have hEnat : E.natDegree = k-1 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      hEbound hEcoeff
  have hEdegree : E.degree = (((k-1 : ℕ)) : WithBot ℕ) := by
    have hEne : E ≠ 0 := by
      intro he
      simp [he] at hEcoeff
    rw [Polynomial.degree_eq_natDegree hEne, hEnat]
  have hObound : O.natDegree ≤ k-1 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    change (paperAxisEven n P).coeff j = 0
    rw [paperAxisEven_coeff]
    by_cases hjn : j ≤ n
    · rw [if_pos hjn]
      have hlt : P.natDegree < 2*j := by dsimp [n] at *; omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
      simp
    · rw [if_neg hjn]
  have hOdegree : O.degree ≤ (((k-1 : ℕ)) : WithBot ℕ) := by
    by_cases hOzero : O = 0
    · simp [hOzero]
    · rw [Polynomial.degree_eq_natDegree hOzero]
      exact_mod_cast hObound
  have hz : ∀ j < k-1, (∑ i ∈ s, (t i)^j * z i) = 0 := by
    intro j hj
    have hsmall : 2*j+1 < n := by dsimp [n]; omega
    exact paperCoefficientBalance_odd_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0 := by
    intro j hj
    have hsmall : 2*j < n := by dsimp [n]; omega
    exact paperCoefficientBalance_even_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hc : ∀ i ∈ s,
      E.eval (t i) * z i + O.eval (t i) * y i = 0 := by
    intro i hi
    have hid := paperRaisedCross_axis_identity_any
      n hn (d i) x 0 (hmonic i hi) (hstable i hi)
    have hzero := hcontact i hi
    rw [hid] at hzero
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] at hzero
    calc
      E.eval (t i) * z i + O.eval (t i) * y i =
          w i * ((paperAxisEven n P).eval (t i) *
            (paperAxisEven n
              (paperDescendingDenominator n (d i))).eval (t i) +
            t i * (paperAxisOdd n P).eval (t i) *
              (paperAxisOdd n
                (paperDescendingDenominator n (d i))).eval (t i)) := by
          dsimp [E, O, z, y]
          ring
      _ = 0 := by
          have hzero' :
              (paperAxisEven n P).eval (t i) *
                (paperAxisEven n
                  (paperDescendingDenominator n (d i))).eval (t i) +
                t i * (paperAxisOdd n P).eval (t i) *
                  (paperAxisOdd n
                    (paperDescendingDenominator n (d i))).eval (t i) = 0 := by
            simpa [P] using hzero
          rw [hzero']
          ring
  have hnode : ∃ r ∈ s.image t,
      paperGroupedResidue s t z r ≠ 0 ∨
        paperGroupedResidue s t y r ≠ 0 := by
    obtain ⟨i, hi, hti⟩ := hposIndex
    let sPos : Finset ι := s.filter (fun j => 0 < t j)
    have hiPos : i ∈ sPos := Finset.mem_filter.mpr ⟨hi, hti⟩
    have htPos : ∀ j ∈ sPos, 0 < t j := by
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    have hwPos : ∀ j ∈ sPos, 0 < w j := by
      intro j hj
      exact hwpos j (Finset.mem_filter.mp hj).1
    have hrPos : t i ∈ sPos.image t :=
      Finset.mem_image.mpr ⟨i, hiPos, rfl⟩
    have hr : t i ∈ s.image t :=
      Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hfilter : sPos.filter (fun j => t j = t i) =
        s.filter (fun j => t j = t i) := by
      ext j
      simp only [sPos, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hj, _⟩, hji⟩
        exact ⟨hj, hji⟩
      · rintro ⟨hj, hji⟩
        exact ⟨⟨hj, by rw [hji]; exact hti⟩, hji⟩
    have hres := paperGroupedAxisResidue_nontrivial
      n a b ha0 hb0 sPos t w side htPos hwPos
      hsegment (t i) hrPos
    refine ⟨t i, hr, ?_⟩
    rcases hres with hreal | himag
    · exact Or.inr (by simpa only [paperGroupedResidue, hfilter] using hreal)
    · exact Or.inl (by simpa only [paperGroupedResidue, hfilter] using himag)
  change 2*(k-1)+1 < (s.image t).card +
    (GCDMonoid.gcd O E).natDegree
  exact paperContactResidue_grouped_gcd_degree_gap_extra_y
    s t z y E O (k-1) hEdegree hOdegree hz
      (fun j hj => hy j (by omega)) hc hnode

/-- The extra even moment yields a strict gcd gap for every zero-leading
even certificate, including atoms at zero and infinity. -/
theorem PaperCriticalCertificate.even_zero_leading_gcd_gap_all
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2))
    (hzero : C.support 0 = 0) :
    2*(n/2-1)+1 < C.positiveFiniteNodes.card + 1 +
      (GCDMonoid.gcd
        (paperAxisEven n
          (paperDescendingNumerator n
            (paperFiniteNumeratorCoeffs n
              (fun j => C.support j.succ))))
        (paperAxisOdd n
          (paperDescendingNumerator n
            (paperFiniteNumeratorCoeffs n
              (fun j => C.support j.succ))))).natDegree := by
  let k := n/2
  let s : Finset (Fin C.atomCount) :=
    Finset.univ.filter (fun i => C.compactFrequency i < 1)
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let t : Fin C.atomCount → ℝ := fun i =>
    C.compactFrequency i / (1-C.compactFrequency i)
  let w : Fin C.atomCount → ℝ := fun i =>
    C.weight i * (1-C.compactFrequency i)^n
  have hk : 0 < k := by dsimp [k]; omega
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hposIndex : ∃ i ∈ s, 0 < t i := by
    obtain ⟨r, hr⟩ := C.positiveFiniteNodes_nonempty
      hn ha0 hb0 hstableA hstableB
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hr
    have hdata := (Finset.mem_filter.mp hi).2
    refine ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, hdata.2⟩, ?_⟩
    exact div_pos hdata.1 (sub_pos.mpr hdata.2)
  have hwpos : ∀ i ∈ s, 0 < w i := by
    intro i hi
    have hfinite := (Finset.mem_filter.mp hi).2
    exact mul_pos (C.weight_pos i)
      (pow_pos (sub_pos.mpr hfinite) n)
  have hsegment' : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k) a b q) := by
    rw [←heven]
    exact hsegment
  have hnext :
      (paperDescendingNumerator (2*k) x).coeff (2*k-1) ≠ 0 := by
    have hpos := C.zero_leading_support_next_coeff_pos
      (by omega : 1 < n) ha0 hb0 hstableA hstableB hzero
    rw [←heven]
    simpa [x] using ne_of_gt hpos
  have hbalance : ∀ r : Fin (2*k),
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial (2*k)
          (if C.rightEndpoint i then b else a)
          (paperFiniteNumeratorCoeffs (2*k)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0 := by
    rw [←heven]
    intro r
    have hb := C.finite_coefficient_balance_with_infinity
      hn ha0 hb0 r
    calc
      _ = ∑ i : Fin C.atomCount, w i *
          (paperGeneralCrossPolynomial n
            (if C.rightEndpoint i then b else a)
            (paperFiniteNumeratorCoeffs n
              (fun j => if r = j then 1 else 0))).eval (t i) := by
        change (∑ i ∈ Finset.univ.filter
          (fun i : Fin C.atomCount =>
            C.compactFrequency i < 1),
          w i *
            (paperGeneralCrossPolynomial n
              (if C.rightEndpoint i then b else a)
              (paperFiniteNumeratorCoeffs n
                (fun j => if r = j then 1 else 0))).eval (t i)) = _
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : C.compactFrequency i < 1
        · simp [hi]
        · have hu1 : C.compactFrequency i = 1 :=
            le_antisymm (C.frequency_mem i).2
              (le_of_not_gt hi)
          have hn0 : n ≠ 0 := by omega
          have hwzero : w i = 0 := by simp [w, hu1, hn0]
          simp [hi, hwzero]
      _ = 0 := by simpa [w, t] using hb
  have hcontact : ∀ i ∈ s,
      (paperRaisedCrossPolynomial (2*k)
        (if C.rightEndpoint i then b else a)
        x 0).eval (t i) = 0 := by
    intro i hi
    have hfinite := (Finset.mem_filter.mp hi).2
    rw [←heven]
    simpa [x, t, hzero] using C.finite_contact_root i hfinite
  have hgap :=
    paperEvenZeroLeadingGroupedCertificate_gcd_degree_gap_with_zero_atoms
      s k hk a b ha0 hb0 C.rightEndpoint
      w t x hnext hposIndex hwpos hsegment' hbalance hcontact
  have hsubset : s.image t ⊆ insert 0 C.positiveFiniteNodes := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    have hfinite := (Finset.mem_filter.mp hi).2
    by_cases hi0 : C.compactFrequency i = 0
    · simp [t, hi0]
    · have hpos : 0 < C.compactFrequency i :=
        lt_of_le_of_ne (C.frequency_mem i).1 (Ne.symm hi0)
      apply Finset.mem_insert_of_mem
      change t i ∈ C.positiveFiniteNodes
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, ⟨hpos, hfinite⟩⟩, rfl⟩
  have hcardLe : (s.image t).card ≤
      C.positiveFiniteNodes.card + 1 := by
    have hcard := Finset.card_le_card hsubset
    have hinsert := Finset.card_insert_le 0 C.positiveFiniteNodes
    omega
  rw [←heven] at hgap
  have hgap' : 2*(n/2-1)+1 <
      (s.image t).card +
      (GCDMonoid.gcd
        (paperAxisEven n
          (paperDescendingNumerator n x))
        (paperAxisOdd n
          (paperDescendingNumerator n x))).natDegree := by
    simpa only [k] using hgap
  change 2*(n/2-1)+1 < C.positiveFiniteNodes.card+1+
    (GCDMonoid.gcd
      (paperAxisEven n (paperDescendingNumerator n x))
      (paperAxisOdd n (paperDescendingNumerator n x))).natDegree
  omega

/-- All even-order critical certificates are impossible on a stable
polynomial segment, including zero-frequency and infinity atoms. -/
theorem PaperCriticalCertificate.no_even_certificate
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (heven : n = 2*(n/2)) : False := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let P := paperDescendingNumerator n x
  let S := (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a x 0)) ∩
    (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n b x 0))
  let G := GCDMonoid.gcd (paperAxisOdd n P)
    (paperAxisEven n P)
  have hn2 : 1 < n := by omega
  have hzero : C.support 0 = 0 :=
    C.even_support_leading_zero hn ha0 hb0 hsegment heven
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hgap := C.even_zero_leading_gcd_gap_all
    hn ha0 hb0 hsegment heven hzero
  have hbound := C.zero_leading_support_gcd_degree_le_overlap
    hn2 ha0 hb0 hstableA hstableB hzero
  have hbudget :=
    C.zero_leading_positiveFiniteNodes_card_add_overlap_le
      hn ha0 hb0 hstableA hstableB hzero
  have hgap' : 2*(n/2-1)+1 <
      C.positiveFiniteNodes.card + 1 + G.natDegree := by
    change 2*(n/2-1)+1 < C.positiveFiniteNodes.card + 1 +
      (GCDMonoid.gcd (paperAxisEven n P)
        (paperAxisOdd n P)).natDegree at hgap
    rw [gcd_comm] at hgap
    exact hgap
  have hbound' : G.natDegree ≤ S.card := by
    simpa [G, S, P, x] using hbound
  have hbudget' : C.positiveFiniteNodes.card + S.card ≤
      2*((n-1)/2) := by
    simpa [S, x, hzero] using hbudget
  omega

/-- The arbitrary-order synthesis theorem holds for every positive even
order. The sixth-order result is a special case; odd orders are handled below. -/
theorem paperTheorem2_even_order
    (n : ℕ) (hn : 0 < n) (heven : n = 2*(n/2))
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun j => (1-r)*a j+r*b j))) :
    ∃ p : Polynomial ℝ,
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        paperPolynomialSPR n p
          (paperDescendingDenominator n
            (fun j => (1-r)*a j+r*b j)) := by
  have hseg : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator n a b r) := by
    simpa [paperSegmentDenominator] using hsegment
  apply (paperTheorem2_iff_no_high_contact_certificate
    n hn a b ha0 hb0 hsegment).2
  rintro ⟨r, hr, C, _⟩
  let d : ℕ → ℝ := fun j => (1-r)*a j+r*b j
  have hd0 : d 0 = 1 := by
    dsimp [d]
    rw [ha0, hb0]
    ring
  have hsub := paperStableInitialSubsegment
    n a b hseg r hr.1.le hr.2
  exact C.no_even_certificate
    hn ha0 hd0 (by simpa [d] using hsub) heven

theorem paperTheorem2_even_order_iff
    (n : ℕ) (hn : 0 < n) (heven : n = 2*(n/2))
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    (∃ p : Polynomial ℝ,
      paperPolynomialSPR n p (paperDescendingDenominator n a) ∧
      paperPolynomialSPR n p (paperDescendingDenominator n b)) ↔
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun j => (1-r)*a j+r*b j))) := by
  constructor
  · rintro ⟨p, hpA, hpB⟩
    exact paperTheorem2_necessity n a b p ha0 hb0 hpA hpB
  · intro hsegment
    obtain ⟨p, hp⟩ := paperTheorem2_even_order
      n hn heven a b ha0 hb0 hsegment
    refine ⟨p, ?_, ?_⟩
    · simpa using hp 0 (by norm_num) (by norm_num)
    · simpa using hp 1 (by norm_num) (by norm_num)

/-- At odd order with a positive highest numerator coefficient, the odd
axis component has degree `k` and the even moments contain one spare
equation.  The extra-moment residue lemma gives a strict degree gap. -/
theorem paperOddPositiveGroupedCertificate_gcd_degree_gap
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ)
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (side : ι → Bool) (w t : ι → ℝ)
    (x : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hposIndex : ∃ i ∈ s, 0 < t i)
    (hwpos : ∀ i ∈ s, 0 < w i)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k+1) a b q))
    (hbalance : ∀ r : Fin (2*k+1),
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial (2*k+1)
          (if side i then b else a)
          (paperFiniteNumeratorCoeffs (2*k+1)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0)
    (hcontact : ∀ i ∈ s,
      (paperRaisedCrossPolynomial (2*k+1)
        (if side i then b else a) x ε).eval (t i) = 0) :
    2*k+1 < (s.image t).card +
      (GCDMonoid.gcd
        (paperAxisEven (2*k+1)
          (paperDescendingNumerator (2*k+1) x +
            Polynomial.C ε * Polynomial.X^(2*k+1)))
        (paperAxisOdd (2*k+1)
          (paperDescendingNumerator (2*k+1) x +
            Polynomial.C ε * Polynomial.X^(2*k+1)))).natDegree := by
  let n := 2*k+1
  let d : ι → ℕ → ℝ := fun i => if side i then b else a
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let E := paperAxisOdd n P
  let O := paperAxisEven n P
  let z : ι → ℝ := fun i =>
    w i * t i * (paperAxisOdd n
      (paperDescendingDenominator n (d i))).eval (t i)
  let y : ι → ℝ := fun i =>
    w i * (paperAxisEven n
      (paperDescendingDenominator n (d i))).eval (t i)
  have hn : 0 < n := by dsimp [n]; omega
  have hmonic : ∀ i ∈ s, d i 0 = 1 := by
    intro i hi
    by_cases h : side i
    · simp [d, h, hb0]
    · simp [d, h, ha0]
  have hstable : ∀ i ∈ s,
      paperPolynomialHurwitz
        (paperDescendingDenominator n (d i)) := by
    intro i hi
    by_cases h : side i
    · simpa [d, h, paperSegmentDenominator] using
        hsegment 1 (by norm_num) (by norm_num)
    · simpa [d, h, paperSegmentDenominator] using
        hsegment 0 (by norm_num) (by norm_num)
  have hPdegree : P.natDegree = n :=
    paperDescendingNumerator_raise_natDegree_eq n x ε hε
  have hEbound : E.natDegree ≤ k := by
    have h := paperAxisOdd_natDegree_le n P hPdegree.le
    change E.natDegree ≤ (n-1)/2 at h
    dsimp [n] at h
    omega
  have hEcoeff : E.coeff k ≠ 0 := by
    have hPtop : P.coeff n = ε := by
      dsimp [P]
      rw [Polynomial.coeff_add, paperDescendingNumerator_coeff,
        if_neg (by omega : ¬n<n),
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_pos rfl]
      ring
    change (paperAxisOdd n P).coeff k ≠ 0
    rw [paperAxisOdd_coeff, if_pos (by dsimp [n]; omega),
      show 2*k+1 = n by rfl, hPtop]
    exact mul_ne_zero (ne_of_gt hε)
      (pow_ne_zero _ (by norm_num))
  have hEnat : E.natDegree = k :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      hEbound hEcoeff
  have hEdegree : E.degree = (k : WithBot ℕ) := by
    have hEne : E ≠ 0 := by
      intro he
      simp [he] at hEcoeff
    rw [Polynomial.degree_eq_natDegree hEne, hEnat]
  have hObound : O.natDegree ≤ k := by
    have h := paperAxisEven_natDegree_le n P hPdegree.le
    change O.natDegree ≤ n/2 at h
    dsimp [n] at h
    omega
  have hOdegree : O.degree ≤ (k : WithBot ℕ) := by
    by_cases hOzero : O = 0
    · simp [hOzero]
    · rw [Polynomial.degree_eq_natDegree hOzero]
      exact_mod_cast hObound
  have hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0 := by
    intro j hj
    have hsmall : 2*j+1 < n := by dsimp [n]; omega
    exact paperCoefficientBalance_odd_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hy : ∀ j < k+1, (∑ i ∈ s, (t i)^j * y i) = 0 := by
    intro j hj
    have hsmall : 2*j < n := by dsimp [n]; omega
    exact paperCoefficientBalance_even_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hc : ∀ i ∈ s,
      E.eval (t i) * z i + O.eval (t i) * y i = 0 := by
    intro i hi
    have hid := paperRaisedCross_axis_identity_any
      n hn (d i) x ε (hmonic i hi) (hstable i hi)
    have hzero := hcontact i hi
    rw [hid] at hzero
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] at hzero
    calc
      E.eval (t i) * z i + O.eval (t i) * y i =
          w i * ((paperAxisEven n P).eval (t i) *
            (paperAxisEven n
              (paperDescendingDenominator n (d i))).eval (t i) +
            t i * (paperAxisOdd n P).eval (t i) *
              (paperAxisOdd n
                (paperDescendingDenominator n (d i))).eval (t i)) := by
          dsimp [E, O, z, y]
          ring
      _ = 0 := by
          rw [hzero]
          ring
  have hnode : ∃ r ∈ s.image t,
      paperGroupedResidue s t z r ≠ 0 ∨
        paperGroupedResidue s t y r ≠ 0 := by
    obtain ⟨i, hi, hti⟩ := hposIndex
    let sPos : Finset ι := s.filter (fun j => 0 < t j)
    have hiPos : i ∈ sPos := Finset.mem_filter.mpr ⟨hi, hti⟩
    have htPos : ∀ j ∈ sPos, 0 < t j := by
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    have hwPos : ∀ j ∈ sPos, 0 < w j := by
      intro j hj
      exact hwpos j (Finset.mem_filter.mp hj).1
    have hrPos : t i ∈ sPos.image t :=
      Finset.mem_image.mpr ⟨i, hiPos, rfl⟩
    have hr : t i ∈ s.image t :=
      Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hfilter : sPos.filter (fun j => t j = t i) =
        s.filter (fun j => t j = t i) := by
      ext j
      simp only [sPos, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hj, _⟩, hji⟩
        exact ⟨hj, hji⟩
      · rintro ⟨hj, hji⟩
        exact ⟨⟨hj, by rw [hji]; exact hti⟩, hji⟩
    have hres := paperGroupedAxisResidue_nontrivial
      n a b ha0 hb0 sPos t w side htPos hwPos
      hsegment (t i) hrPos
    refine ⟨t i, hr, ?_⟩
    rcases hres with hreal | himag
    · exact Or.inr (by simpa only [paperGroupedResidue, hfilter] using hreal)
    · exact Or.inl (by simpa only [paperGroupedResidue, hfilter] using himag)
  change 2*k+1 < (s.image t).card +
    (GCDMonoid.gcd O E).natDegree
  exact paperContactResidue_grouped_gcd_degree_gap_extra_y
    s t z y E O k hEdegree hOdegree hz hy hc hnode

/-- Positive-leading odd critical certificates inherit the strict
extra-moment gcd gap, even if a zero-frequency atom is present. -/
theorem PaperCriticalCertificate.odd_positive_leading_gcd_gap
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hodd : n = 2*(n/2)+1)
    (hε : 0 < C.support 0) :
    n < C.positiveFiniteNodes.card + 1 +
      (GCDMonoid.gcd
        (paperAxisEven n
          (paperDescendingNumerator n
            (paperFiniteNumeratorCoeffs n
              (fun j => C.support j.succ)) +
            Polynomial.C (C.support 0) * Polynomial.X^n))
        (paperAxisOdd n
          (paperDescendingNumerator n
            (paperFiniteNumeratorCoeffs n
              (fun j => C.support j.succ)) +
            Polynomial.C (C.support 0) * Polynomial.X^n))).natDegree := by
  let k := n/2
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let t : Fin C.atomCount → ℝ := fun i =>
    C.compactFrequency i / (1-C.compactFrequency i)
  let w : Fin C.atomCount → ℝ := fun i =>
    C.weight i * (1-C.compactFrequency i)^n
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hfinite : ∀ i : Fin C.atomCount,
      C.compactFrequency i < 1 :=
    C.positive_leading_atoms_finite ha0 hb0 hε
  have hposIndex : ∃ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      0 < t i := by
    obtain ⟨r, hr⟩ := C.positiveFiniteNodes_nonempty
      hn ha0 hb0 hstableA hstableB
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hr
    have hdata := (Finset.mem_filter.mp hi).2
    refine ⟨i, Finset.mem_univ i, ?_⟩
    exact div_pos hdata.1 (sub_pos.mpr hdata.2)
  have hwpos : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      0 < w i := by
    intro i _
    exact mul_pos (C.weight_pos i)
      (pow_pos (sub_pos.mpr (hfinite i)) n)
  have hsegment' : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k+1) a b q) := by
    rw [←hodd]
    exact hsegment
  have hbalance : ∀ r : Fin (2*k+1),
      (∑ i ∈ Finset.univ, w i *
        (paperGeneralCrossPolynomial (2*k+1)
          (if C.rightEndpoint i then b else a)
          (paperFiniteNumeratorCoeffs (2*k+1)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0 := by
    have hb := (C.ordinary_coefficient_balance_of_atoms_finite
      hfinite).2
    rw [←hodd]
    intro r
    simpa [w, t] using hb r
  have hcontact : ∀ i ∈ (Finset.univ : Finset (Fin C.atomCount)),
      (paperRaisedCrossPolynomial (2*k+1)
        (if C.rightEndpoint i then b else a)
        x ε).eval (t i) = 0 := by
    intro i _
    rw [←hodd]
    simpa [x, ε, t] using C.finite_contact_root i (hfinite i)
  have hgap := paperOddPositiveGroupedCertificate_gcd_degree_gap
    Finset.univ k a b ha0 hb0 C.rightEndpoint
    w t x ε hε hposIndex hwpos hsegment' hbalance hcontact
  have hsubset : (Finset.univ.image t) ⊆
      insert 0 C.positiveFiniteNodes := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    by_cases hi0 : C.compactFrequency i = 0
    · simp [t, hi0]
    · have hpos : 0 < C.compactFrequency i :=
        lt_of_le_of_ne (C.frequency_mem i).1 (Ne.symm hi0)
      apply Finset.mem_insert_of_mem
      change t i ∈ C.positiveFiniteNodes
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, ⟨hpos, hfinite i⟩⟩, rfl⟩
  have hcardLe : (Finset.univ.image t).card ≤
      C.positiveFiniteNodes.card + 1 := by
    have hcard := Finset.card_le_card hsubset
    have hinsert := Finset.card_insert_le 0 C.positiveFiniteNodes
    omega
  rw [←hodd] at hgap
  have hgap' : n < (Finset.univ.image t).card +
      (GCDMonoid.gcd
        (paperAxisEven n
          (paperDescendingNumerator n x +
            Polynomial.C ε * Polynomial.X^n))
        (paperAxisOdd n
          (paperDescendingNumerator n x +
            Polynomial.C ε * Polynomial.X^n))).natDegree := by
    simpa only [k] using hgap
  change n < C.positiveFiniteNodes.card+1+
    (GCDMonoid.gcd
      (paperAxisEven n
        (paperDescendingNumerator n x +
          Polynomial.C ε * Polynomial.X^n))
      (paperAxisOdd n
        (paperDescendingNumerator n x +
          Polynomial.C ε * Polynomial.X^n))).natDegree
  omega

/-- A nonzero weakly positive-real numerator has no open right-half-plane
roots and only simple imaginary-axis roots.  If its value at the origin is
nonnegative, these facts bound the parity-gcd degree by the shared endpoint
contacts, whether or not the numerator vanishes at zero. -/
theorem paperAxisGcd_degree_le_overlap_of_weakPR
    (n : ℕ) (hn : 0 < n) (a b x : ℕ → ℝ) (ε : ℝ)
    (P : Polynomial ℝ)
    (hPform : P = paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n)
    (hPne : P ≠ 0) (hPdegree : P.natDegree ≤ n)
    (hP0nonneg : 0 ≤ P.eval 0)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hweak : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ ((Polynomial.aeval z P : ℂ) /
        Polynomial.aeval z
          (paperDescendingDenominator n a)).re)
    (hqAne : paperRaisedCrossPolynomial n a x ε ≠ 0)
    (hqBne : paperRaisedCrossPolynomial n b x ε ≠ 0) :
    (GCDMonoid.gcd (paperAxisOdd n P)
      (paperAxisEven n P)).natDegree ≤
      ((MonicQuinticCoeff.positiveRealRoots
        (paperRaisedCrossPolynomial n a x ε)) ∩
        (MonicQuinticCoeff.positiveRealRoots
          (paperRaisedCrossPolynomial n b x ε))).card := by
  let D := paperDescendingDenominator n a
  have hopen : ∀ z : ℂ, 0 < z.re →
      Polynomial.aeval z P ≠ (0 : ℂ) :=
    paperWeakPositiveReal_nonzero_no_open_right_root
      P D hPne hstableA hweak
  have hsimple : ∀ ω : ℝ,
      Polynomial.aeval (jw ω) P = 0 →
      Polynomial.aeval (jw ω) P.derivative ≠ 0 := by
    intro ω hroot
    exact paperPolynomialQuotient_imag_zero_simple
      P D hPne hstableA hweak ω hroot
  rcases hP0nonneg.eq_or_lt with hP0zero | hP0pos
  · have hPzero : Polynomial.aeval (jw 0) P = (0 : ℂ) := by
      have hcoeff : P.coeff 0 = 0 := by
        simpa [Polynomial.coeff_zero_eq_eval_zero] using hP0zero.symm
      simpa [jw, Polynomial.aeval_def] using hcoeff
    have hderiv0 :
        (Polynomial.aeval (0 : ℂ) P.derivative : ℂ) ≠ 0 := by
      simpa [jw] using hsimple 0 hPzero
    have hOdd0coeff : (paperAxisOdd n P).coeff 0 =
        P.derivative.coeff 0 := by
      rw [paperAxisOdd_coeff, if_pos (Nat.zero_le n),
        Polynomial.coeff_derivative]
      norm_num
    have hOdd0 : (Polynomial.aeval (0 : ℂ)
        (paperAxisOdd n P) : ℂ) ≠ 0 := by
      have hderivCoeff : P.derivative.coeff 0 ≠ 0 := by
        simpa [Polynomial.aeval_def] using hderiv0
      have hOddCoeff : (paperAxisOdd n P).coeff 0 ≠ 0 := by
        rw [hOdd0coeff]
        exact hderivCoeff
      simpa [Polynomial.aeval_def] using hOddCoeff
    have hOddne : paperAxisOdd n P ≠ 0 := by
      intro hz
      apply hOdd0
      simp [hz]
    have hGne : GCDMonoid.gcd
        (paperAxisOdd n P) (paperAxisEven n P) ≠ 0 :=
      gcd_ne_zero_of_left hOddne
    have hnodup := paperAxisGcd_roots_nodup_of_imaginary_simple
      n P hPdegree hopen hGne hsimple
    exact paperAxisGcd_degree_le_overlap_of_odd_origin_ne_zero
      n hn a b x ε P hPform hPdegree hopen hOdd0
      hstableA hstableB hqAne hqBne hGne hnodup
  · have hEvenne : paperAxisEven n P ≠ 0 :=
      paperAxisEven_ne_zero_of_eval_zero_pos n P hP0pos
    have hGne : GCDMonoid.gcd
        (paperAxisOdd n P) (paperAxisEven n P) ≠ 0 :=
      gcd_ne_zero_of_right hEvenne
    have hnodup := paperAxisGcd_roots_nodup_of_imaginary_simple
      n P hPdegree hopen hGne hsimple
    exact paperAxisGcd_degree_le_overlap_of_nodup
      n hn a b x ε P hPform hPdegree hP0pos hopen
      hstableA hstableB hqAne hqBne hGne hnodup

/-- No odd-order critical certificate on a stable segment can have a
positive highest support coefficient. -/
theorem PaperCriticalCertificate.no_odd_certificate_positive_leading
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hodd : n = 2*(n/2)+1)
    (hε : 0 < C.support 0) : False := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let P := paperDescendingNumerator n x +
    Polynomial.C ε * Polynomial.X^n
  let D := paperDescendingDenominator n a
  let S := (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a x ε)) ∩
    (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n b x ε))
  let G := GCDMonoid.gcd (paperAxisOdd n P)
    (paperAxisEven n P)
  have hstableA : paperPolynomialHurwitz D := by
    simpa [D, paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hPdeg : P.natDegree = n :=
    paperDescendingNumerator_raise_natDegree_eq n x ε hε
  have hPne : P ≠ 0 := by
    intro hPzero
    rw [hPzero] at hPdeg
    simp at hPdeg
    omega
  have hweakClosed : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ ((Polynomial.aeval z P : ℂ) /
        Polynomial.aeval z D).re := by
    intro z hz
    have h := (C.support_numerator_closedRightHalfPlane
      hn ha0 hb0 hstableA hstableB z hz).1
    simpa [P, D, x, ε] using h
  have hDmonic : D.Monic :=
    paperDescendingDenominator_monic n a ha0
  have hDdegree : 0 < D.degree := by
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    rw [paperDescendingDenominator_natDegree_eq n a ha0]
    exact hn
  have hD0pos : 0 < D.eval 0 :=
    paperPolynomialHurwitz_monic_eval_zero_pos
      D hDmonic hDdegree hstableA
  have hP0nonneg : 0 ≤ P.eval 0 := by
    have hq := hweakClosed 0 (by simp)
    have hPcast : (Polynomial.aeval (0 : ℂ) P : ℂ) =
        ((P.eval 0 : ℝ) : ℂ) := by
      change Polynomial.eval₂ (algebraMap ℝ ℂ)
        ((algebraMap ℝ ℂ) (0 : ℝ)) P =
          (algebraMap ℝ ℂ) (P.eval 0)
      exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) 0
    have hDcast : (Polynomial.aeval (0 : ℂ) D : ℂ) =
        ((D.eval 0 : ℝ) : ℂ) := by
      change Polynomial.eval₂ (algebraMap ℝ ℂ)
        ((algebraMap ℝ ℂ) (0 : ℝ)) D =
          (algebraMap ℝ ℂ) (D.eval 0)
      exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) 0
    have hqreal : 0 ≤ P.eval 0 / D.eval 0 := by
      simpa [hPcast, hDcast] using hq
    have hprod := mul_nonneg hqreal hD0pos.le
    simpa only [div_mul_cancel₀ _ (ne_of_gt hD0pos)] using hprod
  have hqAne := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn a ha0 hstableA C.support C.support_ne
  have hqBne := paperRaisedCrossPolynomial_ne_zero_of_hurwitz
    n hn b hb0 hstableB C.support C.support_ne
  have hbound := paperAxisGcd_degree_le_overlap_of_weakPR
    n hn a b x ε P rfl hPne hPdeg.le hP0nonneg
    hstableA hstableB hweakClosed
    (by simpa [x, ε] using hqAne)
    (by simpa [x, ε] using hqBne)
  have hbudget := C.positiveFiniteNodes_card_add_overlap_le
    hn ha0 hb0 hstableA hstableB
  have hgap := C.odd_positive_leading_gcd_gap
    hn ha0 hb0 hsegment hodd hε
  have hbound' : G.natDegree ≤ S.card := by
    simpa [G, S, P, x, ε] using hbound
  have hbudget' : C.positiveFiniteNodes.card + S.card ≤
      2*(n/2) := by
    simpa [S, x, ε] using hbudget
  have hgap' : n < C.positiveFiniteNodes.card + 1 +
      G.natDegree := by
    change n < C.positiveFiniteNodes.card + 1 +
      (GCDMonoid.gcd (paperAxisEven n P)
        (paperAxisOdd n P)).natDegree at hgap
    rw [gcd_comm] at hgap
    exact hgap
  omega

/-- A critical certificate at odd order can only have a zero highest
support coefficient. -/
theorem PaperCriticalCertificate.odd_support_leading_zero
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hodd : n = 2*(n/2)+1) :
    C.support 0 = 0 := by
  have hε := C.support_leading_nonneg ha0
  rcases hε.eq_or_lt with hzero | hpos
  · exact hzero.symm
  · exact False.elim
      (C.no_odd_certificate_positive_leading
        hn ha0 hb0 hsegment hodd hpos)

/-- With a zero leading support coefficient and a zero numerator value at the
origin, each endpoint cross has a zero at the origin as well as its double
positive contacts. This saves two units in the combined contact budget. -/
theorem PaperCriticalCertificate.zero_leading_positiveFiniteNodes_card_add_overlap_le_of_origin_zero
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a))
    (hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b))
    (hodd : n = 2*(n/2)+1)
    (hzero : C.support 0 = 0)
    (hP0 : (paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ))).eval 0 = 0) :
    C.positiveFiniteNodes.card +
      ((MonicQuinticCoeff.positiveRealRoots
          (paperRaisedCrossPolynomial n a
            (paperFiniteNumeratorCoeffs n
              (fun j => C.support j.succ)) (C.support 0))) ∩
        (MonicQuinticCoeff.positiveRealRoots
          (paperRaisedCrossPolynomial n b
            (paperFiniteNumeratorCoeffs n
              (fun j => C.support j.succ)) (C.support 0)))).card
      ≤ 2*((n-1)/2)-2 := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  let qA := paperRaisedCrossPolynomial n a x ε
  let qB := paperRaisedCrossPolynomial n b x ε
  let rootsA := MonicQuinticCoeff.positiveRealRoots qA
  let rootsB := MonicQuinticCoeff.positiveRealRoots qB
  have hx0 : x (n-1) = 0 := by
    change (paperDescendingNumerator n x).eval 0 = 0 at hP0
    have h : (paperDescendingNumerator n x +
        Polynomial.C (0 : ℝ) * Polynomial.X^n).eval 0 = 0 := by
      simpa using hP0
    rw [paperRaisedNumerator_eval_zero n hn x 0] at h
    exact h
  have hqA0 : qA.eval 0 = 0 := by
    rw [paperRaisedCrossPolynomial_eval_zero n hn a x ε, hx0, mul_zero]
  have hqB0 : qB.eval 0 = 0 := by
    rw [paperRaisedCrossPolynomial_eval_zero n hn b x ε, hx0, mul_zero]
  have hneA : qA ≠ 0 :=
    paperRaisedCrossPolynomial_ne_zero_of_hurwitz
      n hn a ha0 hstableA C.support C.support_ne
  have hneB : qB ≠ 0 :=
    paperRaisedCrossPolynomial_ne_zero_of_hurwitz
      n hn b hb0 hstableB C.support C.support_ne
  have hnonnegA : ∀ t : ℝ, 0 ≤ t → 0 ≤ qA.eval t :=
    paperFeature_nonneg_cross_nonneg n a C.support C.support_nonneg_left
  have hnonnegB : ∀ t : ℝ, 0 ≤ t → 0 ≤ qB.eval t :=
    paperFeature_nonneg_cross_nonneg n b C.support C.support_nonneg_right
  have hboundA : 2*rootsA.card+1 ≤ n-1 :=
    (MonicQuinticCoeff.twice_card_positiveRealRoots_add_one_le_natDegree_of_zero_root
      qA hneA hnonnegA hqA0).trans
      (paperRaisedCrossPolynomial_natDegree_le_pred_of_top_zero
        n hn a x ε ha0 hzero)
  have hboundB : 2*rootsB.card+1 ≤ n-1 :=
    (MonicQuinticCoeff.twice_card_positiveRealRoots_add_one_le_natDegree_of_zero_root
      qB hneB hnonnegB hqB0).trans
      (paperRaisedCrossPolynomial_natDegree_le_pred_of_top_zero
        n hn b x ε hb0 hzero)
  have hsub : C.positiveFiniteNodes ⊆ rootsA ∪ rootsB :=
    C.positiveFiniteNodes_subset_endpoint_roots
      hn ha0 hb0 hstableA hstableB
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_add_card_inter rootsA rootsB
  change C.positiveFiniteNodes.card + (rootsA ∩ rootsB).card
    ≤ 2*((n-1)/2)-2
  omega

/-- A zero-frequency contact forces the support numerator to vanish at
the origin, independently of its leading coefficient. -/
theorem PaperCriticalCertificate.support_numerator_origin_zero_of_origin_atom
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 0 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (i : Fin C.atomCount) (hi0 : C.compactFrequency i = 0) :
    (paperDescendingNumerator n
      (paperFiniteNumeratorCoeffs n
        (fun j => C.support j.succ))).eval 0 = 0 := by
  let d : ℕ → ℝ := if C.rightEndpoint i then b else a
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let ε := C.support 0
  have hd0 : d 0 = 1 := by
    by_cases h : C.rightEndpoint i
    · simp [d, h, hb0]
    · simp [d, h, ha0]
  have hstableD : paperPolynomialHurwitz
      (paperDescendingDenominator n d) := by
    by_cases h : C.rightEndpoint i
    · simpa [d, h, paperSegmentDenominator] using
        hsegment 1 (by norm_num) (by norm_num)
    · simpa [d, h, paperSegmentDenominator] using
        hsegment 0 (by norm_num) (by norm_num)
  have hfinite : C.compactFrequency i < 1 := by
    rw [hi0]
    norm_num
  have hcontact := C.finite_contact_root i hfinite
  have hcross0 : (paperRaisedCrossPolynomial n d x ε).eval 0 = 0 := by
    simpa [d, x, ε, hi0] using hcontact
  have hconst : 0 < d n :=
    paperDescendingDenominator_const_pos_of_hurwitz
      n hn d hd0 hstableD
  have hx0 : x (n-1) = 0 := by
    rw [paperRaisedCrossPolynomial_eval_zero n hn d x ε] at hcross0
    exact (mul_eq_zero.mp hcross0).resolve_left (ne_of_gt hconst)
  change (paperDescendingNumerator n x).eval 0 = 0
  have hP0 : (paperDescendingNumerator n x +
      Polynomial.C ε * Polynomial.X^n).eval 0 = 0 := by
    rw [paperRaisedNumerator_eval_zero n hn x ε]
    exact hx0
  simpa [hn.ne'] using hP0

/-- For odd degree `2*k+1`, a zero-leading support numerator has degree
`2*k`. Its even axis polynomial has degree `k`, so the first `k` even and
odd moment equations force a strict contact/gcd gap. -/
theorem paperOddZeroLeadingGroupedCertificate_gcd_degree_gap
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ)
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (side : ι → Bool) (w t : ι → ℝ)
    (x : ℕ → ℝ)
    (hPnext : (paperDescendingNumerator (2*k+1) x).coeff (2*k) ≠ 0)
    (hposIndex : ∃ i ∈ s, 0 < t i)
    (hwpos : ∀ i ∈ s, 0 < w i)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k+1) a b q))
    (hbalance : ∀ r : Fin (2*k+1),
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial (2*k+1)
          (if side i then b else a)
          (paperFiniteNumeratorCoeffs (2*k+1)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0)
    (hcontact : ∀ i ∈ s,
      (paperRaisedCrossPolynomial (2*k+1)
        (if side i then b else a) x 0).eval (t i) = 0) :
    2*k < (s.image t).card +
      (GCDMonoid.gcd
        (paperAxisOdd (2*k+1)
          (paperDescendingNumerator (2*k+1) x))
        (paperAxisEven (2*k+1)
          (paperDescendingNumerator (2*k+1) x))).natDegree := by
  let n := 2*k+1
  let d : ι → ℕ → ℝ := fun i => if side i then b else a
  let P := paperDescendingNumerator n x
  let E := paperAxisEven n P
  let O := paperAxisOdd n P
  let z : ι → ℝ := fun i =>
    w i * (paperAxisEven n
      (paperDescendingDenominator n (d i))).eval (t i)
  let y : ι → ℝ := fun i =>
    w i * t i * (paperAxisOdd n
      (paperDescendingDenominator n (d i))).eval (t i)
  have hn : 0 < n := by dsimp [n]; omega
  have hmonic : ∀ i ∈ s, d i 0 = 1 := by
    intro i hi
    by_cases h : side i
    · simp [d, h, hb0]
    · simp [d, h, ha0]
  have hstable : ∀ i ∈ s,
      paperPolynomialHurwitz
        (paperDescendingDenominator n (d i)) := by
    intro i hi
    by_cases h : side i
    · simpa [d, h, paperSegmentDenominator] using
        hsegment 1 (by norm_num) (by norm_num)
    · simpa [d, h, paperSegmentDenominator] using
        hsegment 0 (by norm_num) (by norm_num)
  have hPdegree : P.natDegree ≤ n-1 :=
    paperDescendingNumerator_natDegree_le n hn x
  have hEbound : E.natDegree ≤ k := by
    have h := paperAxisEven_natDegree_le n P
      (hPdegree.trans (Nat.pred_le n))
    change E.natDegree ≤ n/2 at h
    dsimp [n] at h
    omega
  have hEcoeff : E.coeff k ≠ 0 := by
    change (paperAxisEven n P).coeff k ≠ 0
    rw [paperAxisEven_coeff, if_pos (by dsimp [n]; omega)]
    have hidx : 2*k = n-1 := by omega
    rw [hidx]
    exact mul_ne_zero (by simpa [P, n] using hPnext)
      (pow_ne_zero _ (by norm_num))
  have hEnat : E.natDegree = k :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      hEbound hEcoeff
  have hEdegree : E.degree = (k : WithBot ℕ) := by
    have hEne : E ≠ 0 := by
      intro he
      simp [he] at hEcoeff
    rw [Polynomial.degree_eq_natDegree hEne, hEnat]
  have hObound : O.natDegree ≤ k := by
    have h := paperAxisOdd_natDegree_le n P
      (hPdegree.trans (Nat.sub_le n 1))
    change O.natDegree ≤ (n-1)/2 at h
    dsimp [n] at h
    omega
  have hOdegree : O.degree ≤ (k : WithBot ℕ) := by
    by_cases hOzero : O = 0
    · simp [hOzero]
    · rw [Polynomial.degree_eq_natDegree hOzero]
      exact_mod_cast hObound
  have hz : ∀ j < k, (∑ i ∈ s, (t i)^j * z i) = 0 := by
    intro j hj
    have hsmall : 2*j < n := by dsimp [n]; omega
    exact paperCoefficientBalance_even_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hy : ∀ j < k, (∑ i ∈ s, (t i)^j * y i) = 0 := by
    intro j hj
    have hsmall : 2*j+1 < n := by dsimp [n]; omega
    exact paperCoefficientBalance_odd_moments
      s n hn d w t hmonic hstable hbalance j hsmall
  have hc : ∀ i ∈ s,
      E.eval (t i) * z i + O.eval (t i) * y i = 0 := by
    intro i hi
    have hid := paperRaisedCross_axis_identity_any
      n hn (d i) x 0 (hmonic i hi) (hstable i hi)
    have hzero := hcontact i hi
    rw [hid] at hzero
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] at hzero
    calc
      E.eval (t i) * z i + O.eval (t i) * y i =
          w i * ((paperAxisEven n P).eval (t i) *
            (paperAxisEven n
              (paperDescendingDenominator n (d i))).eval (t i) +
            t i * (paperAxisOdd n P).eval (t i) *
              (paperAxisOdd n
                (paperDescendingDenominator n (d i))).eval (t i)) := by
          dsimp [E, O, z, y]
          ring
      _ = 0 := by
          have hzero' :
              (paperAxisEven n P).eval (t i) *
                (paperAxisEven n
                  (paperDescendingDenominator n (d i))).eval (t i) +
                t i * (paperAxisOdd n P).eval (t i) *
                  (paperAxisOdd n
                    (paperDescendingDenominator n (d i))).eval (t i) = 0 := by
            simpa [P] using hzero
          rw [hzero']
          ring
  have hnode : ∃ r ∈ s.image t,
      paperGroupedResidue s t z r ≠ 0 ∨
        paperGroupedResidue s t y r ≠ 0 := by
    obtain ⟨i, hi, hti⟩ := hposIndex
    let sPos : Finset ι := s.filter (fun j => 0 < t j)
    have hiPos : i ∈ sPos := Finset.mem_filter.mpr ⟨hi, hti⟩
    have htPos : ∀ j ∈ sPos, 0 < t j := by
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    have hwPos : ∀ j ∈ sPos, 0 < w j := by
      intro j hj
      exact hwpos j (Finset.mem_filter.mp hj).1
    have hrPos : t i ∈ sPos.image t :=
      Finset.mem_image.mpr ⟨i, hiPos, rfl⟩
    have hr : t i ∈ s.image t :=
      Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hfilter : sPos.filter (fun j => t j = t i) =
        s.filter (fun j => t j = t i) := by
      ext j
      simp only [sPos, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hj, _⟩, hji⟩
        exact ⟨hj, hji⟩
      · rintro ⟨hj, hji⟩
        exact ⟨⟨hj, by rw [hji]; exact hti⟩, hji⟩
    have hres := paperGroupedAxisResidue_nontrivial
      n a b ha0 hb0 sPos t w side htPos hwPos
      hsegment (t i) hrPos
    refine ⟨t i, hr, ?_⟩
    rcases hres with hreal | himag
    · exact Or.inl (by simpa only [paperGroupedResidue, hfilter] using hreal)
    · exact Or.inr (by simpa only [paperGroupedResidue, hfilter] using himag)
  change 2*k < (s.image t).card +
    (GCDMonoid.gcd O E).natDegree
  exact paperContactResidue_grouped_gcd_degree_gap
    s t z y E O k hEdegree hOdegree hz hy hc hnode

/-- A zero-leading odd-order certificate has a strict gap between finite
frequency nodes and the parity gcd, with zero and infinity atoms allowed. -/
theorem PaperCriticalCertificate.odd_zero_leading_gcd_gap_all
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 1 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hodd : n = 2*(n/2)+1)
    (hzero : C.support 0 = 0) :
    2*(n/2) < C.positiveFiniteNodes.card +
      (if ∃ i : Fin C.atomCount,
          C.compactFrequency i = 0 then 1 else 0) +
      (GCDMonoid.gcd
        (paperAxisOdd n
          (paperDescendingNumerator n
            (paperFiniteNumeratorCoeffs n
              (fun j => C.support j.succ))))
        (paperAxisEven n
          (paperDescendingNumerator n
            (paperFiniteNumeratorCoeffs n
              (fun j => C.support j.succ))))).natDegree := by
  let k := n/2
  let s : Finset (Fin C.atomCount) :=
    Finset.univ.filter (fun i => C.compactFrequency i < 1)
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let t : Fin C.atomCount → ℝ := fun i =>
    C.compactFrequency i / (1-C.compactFrequency i)
  let w : Fin C.atomCount → ℝ := fun i =>
    C.weight i * (1-C.compactFrequency i)^n
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hposIndex : ∃ i ∈ s, 0 < t i := by
    obtain ⟨r, hr⟩ := C.positiveFiniteNodes_nonempty
      (by omega : 0 < n) ha0 hb0 hstableA hstableB
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hr
    have hdata := (Finset.mem_filter.mp hi).2
    refine ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, hdata.2⟩, ?_⟩
    exact div_pos hdata.1 (sub_pos.mpr hdata.2)
  have hwpos : ∀ i ∈ s, 0 < w i := by
    intro i hi
    have hfinite := (Finset.mem_filter.mp hi).2
    exact mul_pos (C.weight_pos i)
      (pow_pos (sub_pos.mpr hfinite) n)
  have hsegment' : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator (2*k+1) a b q) := by
    rw [←hodd]
    exact hsegment
  have hnext :
      (paperDescendingNumerator (2*k+1) x).coeff (2*k) ≠ 0 := by
    have hpos := C.zero_leading_support_next_coeff_pos
      hn ha0 hb0 hstableA hstableB hzero
    have hidx : 2*k = n-1 := by dsimp [k]; omega
    rw [←hodd]
    rw [hidx]
    simpa [x] using ne_of_gt hpos
  have hbalance : ∀ r : Fin (2*k+1),
      (∑ i ∈ s, w i *
        (paperGeneralCrossPolynomial (2*k+1)
          (if C.rightEndpoint i then b else a)
          (paperFiniteNumeratorCoeffs (2*k+1)
            (fun j => if r = j then 1 else 0))).eval (t i)) = 0 := by
    rw [←hodd]
    intro r
    have hb := C.finite_coefficient_balance_with_infinity
      (by omega : 0 < n) ha0 hb0 r
    calc
      _ = ∑ i : Fin C.atomCount, w i *
          (paperGeneralCrossPolynomial n
            (if C.rightEndpoint i then b else a)
            (paperFiniteNumeratorCoeffs n
              (fun j => if r = j then 1 else 0))).eval (t i) := by
        change (∑ i ∈ Finset.univ.filter
          (fun i : Fin C.atomCount =>
            C.compactFrequency i < 1),
          w i *
            (paperGeneralCrossPolynomial n
              (if C.rightEndpoint i then b else a)
              (paperFiniteNumeratorCoeffs n
                (fun j => if r = j then 1 else 0))).eval (t i)) = _
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : C.compactFrequency i < 1
        · simp [hi]
        · have hu1 : C.compactFrequency i = 1 :=
            le_antisymm (C.frequency_mem i).2
              (le_of_not_gt hi)
          have hn0 : n ≠ 0 := by omega
          have hwzero : w i = 0 := by simp [w, hu1, hn0]
          simp [hi, hwzero]
      _ = 0 := by simpa [w, t] using hb
  have hcontact : ∀ i ∈ s,
      (paperRaisedCrossPolynomial (2*k+1)
        (if C.rightEndpoint i then b else a)
        x 0).eval (t i) = 0 := by
    intro i hi
    have hfinite := (Finset.mem_filter.mp hi).2
    rw [←hodd]
    simpa [x, t, hzero] using C.finite_contact_root i hfinite
  have hgap :=
    paperOddZeroLeadingGroupedCertificate_gcd_degree_gap
      s k a b ha0 hb0 C.rightEndpoint
      w t x hnext hposIndex hwpos hsegment' hbalance hcontact
  have hsubset : s.image t ⊆ insert 0 C.positiveFiniteNodes := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    have hfinite := (Finset.mem_filter.mp hi).2
    by_cases hi0 : C.compactFrequency i = 0
    · simp [t, hi0]
    · have hpos : 0 < C.compactFrequency i :=
        lt_of_le_of_ne (C.frequency_mem i).1 (Ne.symm hi0)
      apply Finset.mem_insert_of_mem
      change t i ∈ C.positiveFiniteNodes
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, ⟨hpos, hfinite⟩⟩, rfl⟩
  have hcardLe : (s.image t).card ≤
      C.positiveFiniteNodes.card +
        (if ∃ i : Fin C.atomCount,
          C.compactFrequency i = 0 then 1 else 0) := by
    by_cases horigin : ∃ i : Fin C.atomCount,
        C.compactFrequency i = 0
    · simp only [if_pos horigin]
      have hcard := Finset.card_le_card hsubset
      have hinsert := Finset.card_insert_le 0 C.positiveFiniteNodes
      omega
    · simp only [if_neg horigin, add_zero]
      have hsubset' : s.image t ⊆ C.positiveFiniteNodes := by
        intro r hr
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
        have hfinite := (Finset.mem_filter.mp hi).2
        have hi0 : C.compactFrequency i ≠ 0 := by
          intro h
          exact horigin ⟨i, h⟩
        have hpos : 0 < C.compactFrequency i :=
          lt_of_le_of_ne (C.frequency_mem i).1 (Ne.symm hi0)
        change t i ∈ C.positiveFiniteNodes
        apply Finset.mem_image.mpr
        exact ⟨i, Finset.mem_filter.mpr
          ⟨Finset.mem_univ i, ⟨hpos, hfinite⟩⟩, rfl⟩
      exact Finset.card_le_card hsubset'
  rw [←hodd] at hgap
  have hgap' : 2*(n/2) <
      (s.image t).card +
      (GCDMonoid.gcd
        (paperAxisOdd n
          (paperDescendingNumerator n x))
        (paperAxisEven n
          (paperDescendingNumerator n x))).natDegree := by
    simpa only [k] using hgap
  change 2*(n/2) < C.positiveFiniteNodes.card+
      (if ∃ i : Fin C.atomCount,
        C.compactFrequency i = 0 then 1 else 0)+
    (GCDMonoid.gcd
      (paperAxisOdd n (paperDescendingNumerator n x))
      (paperAxisEven n (paperDescendingNumerator n x))).natDegree
  omega

/-- The grouped-residue gap contradicts endpoint contact counts in both
cases: no origin atom, or an origin atom forcing an additional origin root. -/
theorem PaperCriticalCertificate.no_odd_zero_leading_certificate
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 1 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hodd : n = 2*(n/2)+1)
    (hzero : C.support 0 = 0) : False := by
  let x := paperFiniteNumeratorCoeffs n
    (fun j => C.support j.succ)
  let P := paperDescendingNumerator n x
  let S := (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n a x 0)) ∩
    (MonicQuinticCoeff.positiveRealRoots
      (paperRaisedCrossPolynomial n b x 0))
  let G := GCDMonoid.gcd (paperAxisOdd n P)
    (paperAxisEven n P)
  have hstableA : paperPolynomialHurwitz
      (paperDescendingDenominator n a) := by
    simpa [paperSegmentDenominator] using
      hsegment 0 (by norm_num) (by norm_num)
  have hstableB : paperPolynomialHurwitz
      (paperDescendingDenominator n b) := by
    simpa [paperSegmentDenominator] using
      hsegment 1 (by norm_num) (by norm_num)
  have hgap := C.odd_zero_leading_gcd_gap_all
    hn ha0 hb0 hsegment hodd hzero
  have hbound := C.zero_leading_support_gcd_degree_le_overlap
    hn ha0 hb0 hstableA hstableB hzero
  have hbudget :=
    C.zero_leading_positiveFiniteNodes_card_add_overlap_le
      (by omega : 0 < n) ha0 hb0 hstableA hstableB hzero
  have hbound' : G.natDegree ≤ S.card := by
    simpa [G, S, P, x] using hbound
  have hbudget' : C.positiveFiniteNodes.card + S.card ≤
      2*((n-1)/2) := by
    simpa [S, x, hzero] using hbudget
  by_cases horigin : ∃ i : Fin C.atomCount,
      C.compactFrequency i = 0
  · obtain ⟨i, hi0⟩ := horigin
    have hyes : ∃ j : Fin C.atomCount,
        C.compactFrequency j = 0 := ⟨i, hi0⟩
    have hP0 := C.support_numerator_origin_zero_of_origin_atom
      (by omega : 0 < n) ha0 hb0 hsegment i hi0
    have hbudget0 :=
      C.zero_leading_positiveFiniteNodes_card_add_overlap_le_of_origin_zero
        (by omega : 0 < n) ha0 hb0 hstableA hstableB
        hodd hzero (by simpa [x] using hP0)
    have hbudget0' : C.positiveFiniteNodes.card + S.card ≤
        2*((n-1)/2)-2 := by
      simpa [S, x, hzero] using hbudget0
    have hgap' : 2*(n/2) <
        C.positiveFiniteNodes.card + 1 + G.natDegree := by
      simpa [hyes] using hgap
    omega
  · have hgap' : 2*(n/2) <
        C.positiveFiniteNodes.card + G.natDegree := by
      simpa [horigin] using hgap
    omega

/-- Every critical certificate at odd order greater than one is
impossible: its leading support coefficient is zero, and the degree-drop
residue argument excludes that remaining case. -/
theorem PaperCriticalCertificate.no_odd_certificate
    {n : ℕ} {a b : ℕ → ℝ}
    (C : PaperCriticalCertificate n a b) (hn : 1 < n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      paperPolynomialHurwitz (paperSegmentDenominator n a b q))
    (hodd : n = 2*(n/2)+1) : False := by
  have hzero := C.odd_support_leading_zero
    (by omega : 0 < n) ha0 hb0 hsegment hodd
  exact C.no_odd_zero_leading_certificate
    hn ha0 hb0 hsegment hodd hzero

/-- The paper's synthesis theorem holds for every positive odd order. -/
theorem paperTheorem2_odd_order
    (n : ℕ) (hn : 0 < n) (hodd : n = 2*(n/2)+1)
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun j => (1-r)*a j+r*b j))) :
    ∃ p : Polynomial ℝ,
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        paperPolynomialSPR n p
          (paperDescendingDenominator n
            (fun j => (1-r)*a j+r*b j)) := by
  by_cases hone : n = 1
  · subst n
    exact paperTheorem2_first_order a b ha0 hb0 hsegment
  have hn2 : 1 < n := by omega
  have hseg : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperSegmentDenominator n a b r) := by
    simpa [paperSegmentDenominator] using hsegment
  apply (paperTheorem2_iff_no_high_contact_certificate
    n hn a b ha0 hb0 hsegment).2
  rintro ⟨r, hr, C, _⟩
  let d : ℕ → ℝ := fun j => (1-r)*a j+r*b j
  have hd0 : d 0 = 1 := by
    dsimp [d]
    rw [ha0, hb0]
    ring
  have hsub := paperStableInitialSubsegment
    n a b hseg r hr.1.le hr.2
  exact C.no_odd_certificate
    hn2 ha0 hd0 (by simpa [d] using hsub) hodd

/-- The arbitrary-order sufficiency assertion of Theorem 2, including
both parities and the first-order base case. -/
theorem paperTheorem2_arbitrary_order
    (n : ℕ) (hn : 0 < n)
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hsegment : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun j => (1-r)*a j+r*b j))) :
    ∃ p : Polynomial ℝ,
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        paperPolynomialSPR n p
          (paperDescendingDenominator n
            (fun j => (1-r)*a j+r*b j)) := by
  by_cases heven : n = 2*(n/2)
  · exact paperTheorem2_even_order
      n hn heven a b ha0 hb0 hsegment
  · have hodd : n = 2*(n/2)+1 := by omega
    exact paperTheorem2_odd_order
      n hn hodd a b ha0 hb0 hsegment

/-- The paper's complete arbitrary-order endpoint equivalence. -/
theorem paperTheorem2_arbitrary_order_iff
    (n : ℕ) (hn : 0 < n)
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    (∃ p : Polynomial ℝ,
      paperPolynomialSPR n p (paperDescendingDenominator n a) ∧
      paperPolynomialSPR n p (paperDescendingDenominator n b)) ↔
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun j => (1-r)*a j+r*b j))) := by
  constructor
  · rintro ⟨p, hpA, hpB⟩
    exact paperTheorem2_necessity n a b p ha0 hb0 hpA hpB
  · intro hsegment
    obtain ⟨p, hp⟩ := paperTheorem2_arbitrary_order
      n hn a b ha0 hb0 hsegment
    refine ⟨p, ?_, ?_⟩
    · simpa using hp 0 (by norm_num) (by norm_num)
    · simpa using hp 1 (by norm_num) (by norm_num)

/-- Positive normalization makes a degree-matched SPR numerator monic. -/
theorem paperPolynomialSPR_monic_normalize
    (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (p : Polynomial ℝ) (ha0 : a 0 = 1)
    (hSPR : paperPolynomialSPR n p (paperDescendingDenominator n a)) :
    (Polynomial.C p.leadingCoeff⁻¹ * p).Monic ∧
      paperPolynomialSPR n (Polynomial.C p.leadingCoeff⁻¹ * p)
        (paperDescendingDenominator n a) := by
  have hlead : 0 < p.leadingCoeff := by
    simpa [← hSPR.1, Polynomial.coeff_natDegree] using
      paperSPR_top_coeff_pos n hn a p ha0 hSPR
  have hinv : p.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hlead)
  refine ⟨Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    (inv_mul_cancel₀ (ne_of_gt hlead)), ?_⟩
  refine ⟨?_, hSPR.2.1, hSPR.2.2.1, ?_⟩
  · rw [Polynomial.natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hinv), hSPR.1]
  · intro ω
    rw [Polynomial.aeval_mul, Polynomial.aeval_C, mul_div_assoc, Complex.mul_re]
    simpa using mul_pos (inv_pos.mpr hlead) (hSPR.2.2.2 ω)

/-- The endpoint equivalence with the monic numerator required in the manuscript. -/
theorem paperTheorem2_arbitrary_order_monic_iff
    (n : ℕ) (hn : 0 < n)
    (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    (∃ p : Polynomial ℝ, p.Monic ∧
      paperPolynomialSPR n p (paperDescendingDenominator n a) ∧
      paperPolynomialSPR n p (paperDescendingDenominator n b)) ↔
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      paperPolynomialHurwitz
        (paperDescendingDenominator n
          (fun j => (1-r)*a j+r*b j))) := by
  constructor
  · rintro ⟨p, _, hpA, hpB⟩
    exact (paperTheorem2_arbitrary_order_iff n hn a b ha0 hb0).mp ⟨p, hpA, hpB⟩
  · intro hsegment
    obtain ⟨p, hpA, hpB⟩ :=
      (paperTheorem2_arbitrary_order_iff n hn a b ha0 hb0).mpr hsegment
    obtain ⟨hmonic, hnormA⟩ := paperPolynomialSPR_monic_normalize n hn a p ha0 hpA
    have hnormB := (paperPolynomialSPR_monic_normalize n hn b p hb0 hpB).2
    exact ⟨Polynomial.C p.leadingCoeff⁻¹ * p, hmonic, hnormA, hnormB⟩

end
end
end SixthOrder
end SPR
end MKNumina
