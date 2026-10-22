import Lester.Bridge

/-!
# Layer 14: Mathlib-only restatement and a witness for Lester's circle

`l14_lester` mentions only Mathlib notions:
* the nine-point centre is `t.ninePointCircle.center` and the circumcentre `t.circumcenter`;
* the six apexes are given by their **defining property**. `Xa` is a point with
  `dist Xa B = dist Xa C = dist B C` lying strictly on the other side of line `BC` from `A`
  (`AffineSubspace.SOppSide`): the apex of the equilateral triangle erected outwards on `BC`.
  `Ya` is the same with `SSameSide` (erected inwards). The other four are obtained cyclically;
* the Fermat points `F₁`, `F₂` are given by concurrency: `F₁` lies on the three lines
  `line[ℝ, A, Xa]`, `line[ℝ, B, Xb]`, `line[ℝ, C, Xc]`, and `F₂` likewise with the `Y`'s.
The bridges `l14b_apexOut` / `l14b_apexIn` show that such points are the library's
`apexOut` / `apexIn`. `l14w_lester` is the scalene triangle `A = 2`, `B = -3/2 + (3√3/2) i`,
`C = -2 - 2√3 i` (`AB² = 19`, `BC² = 37`, `CA² = 28`). For it, all six apexes, both Fermat points
(`F₁ = 0`, `F₂ = -2 + (4√3/3) i`), the circumcentre `-14/13 - (11√3/39) i` and the nine-point
centre `-11/52 - (17√3/156) i` are computed. The four concyclic points have pairwise distinct real
parts.
-/

namespace Lester

open Complex ComplexConjugate EuclideanGeometry

attribute [local instance] Complex.finrank_real_complex_fact

/-! ### Bridges -/

theorem l14b_cross_eq (B C z : ℂ) : (conj (C - B) * (z - B)).im =
    (C.re - B.re) * (z.im - B.im) - (C.im - B.im) * (z.re - B.re) := by
  simp only [mul_im, conj_re, conj_im, sub_re, sub_im]; ring

/-- A point with vanishing area form relative to `BC` lies on line `BC`. -/
theorem l14b_mem_line_of_cross {B C z : ℂ} (hBC : B ≠ C)
    (h : (conj (C - B) * (z - B)).im = 0) : z ∈ line[ℝ, B, C] := by
  rw [l14b_cross_eq] at h
  have hn : (C.re - B.re) ^ 2 + (C.im - B.im) ^ 2 ≠ 0 := by
    intro h0
    apply hBC
    have h1 : C.re - B.re = 0 := by nlinarith [sq_nonneg (C.re - B.re), sq_nonneg (C.im - B.im)]
    have h2 : C.im - B.im = 0 := by nlinarith [sq_nonneg (C.re - B.re), sq_nonneg (C.im - B.im)]
    exact (Complex.ext (by linarith) (by linarith))
  refine (mem_affineSpan_pair_iff_exists_lineMap_eq).2
    ⟨((z.re - B.re) * (C.re - B.re) + (z.im - B.im) * (C.im - B.im)) /
      ((C.re - B.re) ^ 2 + (C.im - B.im) ^ 2), ?_⟩
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul,
      sub_re, sub_im] <;> field_simp
  · linear_combination (C.im - B.im) * h
  · linear_combination -(C.re - B.re) * h

theorem l14b_sign_neg {x a r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) (k : r₁ * x = -(r₂ * a)) :
    x * a ≤ 0 := by
  have e : r₁ * (x * a) = -(r₂ * a ^ 2) := by linear_combination a * k
  by_contra hc
  have := mul_pos h₁ (lt_of_not_ge hc)
  nlinarith [mul_nonneg h₂.le (sq_nonneg a)]

theorem l14b_sign_pos {x a r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) (k : r₁ * x = r₂ * a) :
    0 ≤ x * a := by
  have e : r₁ * (x * a) = r₂ * a ^ 2 := by linear_combination a * k
  by_contra hc
  have := mul_neg_of_pos_of_neg h₁ (lt_of_not_ge hc)
  nlinarith [mul_nonneg h₂.le (sq_nonneg a)]

/-- Strictly opposite sides of line `BC`: the area forms have opposite signs. -/
theorem l14b_cross_of_sOppSide {B C X A : ℂ} (h : line[ℝ, B, C].SOppSide X A) :
    (conj (C - B) * (X - B)).im * (conj (C - B) * (A - B)).im ≤ 0 := by
  obtain ⟨hX, hA, p, hp, hray⟩ :=
    (AffineSubspace.sOppSide_iff_exists_left (left_mem_affineSpan_pair ℝ B C)).1 h
  obtain ⟨r, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hp
  have hX0 : X -ᵥ B ≠ 0 := by
    rw [vsub_ne_zero]; rintro rfl; exact hX (left_mem_affineSpan_pair ℝ _ _)
  have hp0 : AffineMap.lineMap B C r -ᵥ A ≠ 0 := by
    rw [vsub_ne_zero]; intro e; exact hA (e ▸ AffineMap.lineMap_mem_affineSpan_pair r B C)
  obtain ⟨r₁, r₂, h₁, h₂, e⟩ := hray.exists_pos hX0 hp0
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vsub_eq_sub, vsub_eq_sub, vadd_eq_add,
    Complex.real_smul, Complex.real_smul, Complex.real_smul] at e
  have e' := congrArg (fun z => (conj (C - B) * z).im) e
  simp only [mul_im, mul_re, conj_re, conj_im, sub_re, sub_im, add_re, add_im, ofReal_re,
    ofReal_im] at e'
  rw [l14b_cross_eq, l14b_cross_eq]
  exact l14b_sign_neg h₁ h₂ (by linear_combination e')

/-- Strictly the same side of line `BC`: the area forms have the same sign. -/
theorem l14b_cross_of_sSameSide {B C X A : ℂ} (h : line[ℝ, B, C].SSameSide X A) :
    0 ≤ (conj (C - B) * (X - B)).im * (conj (C - B) * (A - B)).im := by
  obtain ⟨hX, hA, p, hp, hray⟩ :=
    (AffineSubspace.sSameSide_iff_exists_left (left_mem_affineSpan_pair ℝ B C)).1 h
  obtain ⟨r, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hp
  have hX0 : X -ᵥ B ≠ 0 := by
    rw [vsub_ne_zero]; rintro rfl; exact hX (left_mem_affineSpan_pair ℝ _ _)
  have hp0 : A -ᵥ AffineMap.lineMap B C r ≠ 0 := by
    rw [vsub_ne_zero]; intro e; exact hA (e ▸ AffineMap.lineMap_mem_affineSpan_pair r B C)
  obtain ⟨r₁, r₂, h₁, h₂, e⟩ := hray.exists_pos hX0 hp0
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vsub_eq_sub, vsub_eq_sub, vadd_eq_add,
    Complex.real_smul, Complex.real_smul, Complex.real_smul] at e
  have e' := congrArg (fun z => (conj (C - B) * z).im) e
  simp only [mul_im, mul_re, conj_re, conj_im, sub_re, sub_im, add_re, add_im, ofReal_re,
    ofReal_im] at e'
  rw [l14b_cross_eq, l14b_cross_eq]
  exact l14b_sign_pos h₁ h₂ (by linear_combination e')

/-- A point at distance `BC` from both `B` and `C` is one of the two equilateral apexes. -/
theorem l14b_equilateral {B C X : ℂ} (hBC : B ≠ C) (h1 : dist X B = dist B C)
    (h2 : dist X C = dist B C) : X = B + (C - B) * ω ∨ X = B + (C - B) * conj ω := by
  have hd : C - B ≠ 0 := sub_ne_zero.2 hBC.symm
  set w := (X - B) / (C - B) with hw
  have hX : X = B + (C - B) * w := by rw [hw]; field_simp; ring
  have hdn : 0 < ‖C - B‖ := norm_pos_iff.2 hd
  have eXB : X - B = (C - B) * w := by rw [hw]; field_simp
  have eXC : X - C = (C - B) * (w - 1) := by rw [mul_sub, ← eXB]; ring
  have n1 : ‖w‖ = 1 := by
    have : ‖C - B‖ * ‖w‖ = ‖C - B‖ * 1 := by
      rw [mul_one, ← norm_mul, ← eXB, ← Complex.dist_eq, h1, dist_comm, Complex.dist_eq]
    exact mul_left_cancel₀ hdn.ne' this
  have n2 : ‖w - 1‖ = 1 := by
    have : ‖C - B‖ * ‖w - 1‖ = ‖C - B‖ * 1 := by
      rw [mul_one, ← norm_mul, ← eXC, ← Complex.dist_eq, h2, dist_comm, Complex.dist_eq]
    exact mul_left_cancel₀ hdn.ne' this
  have s1 : w.re ^ 2 + w.im ^ 2 = 1 := by
    have := congrArg (· ^ 2) n1
    simp only [Complex.sq_norm, Complex.normSq_apply, one_pow] at this
    linarith
  have s2 : (w.re - 1) ^ 2 + w.im ^ 2 = 1 := by
    have := congrArg (· ^ 2) n2
    simp only [Complex.sq_norm, Complex.normSq_apply, one_pow, sub_re, sub_im, one_re,
      one_im, sub_zero] at this
    linarith
  have hre : w.re = 1 / 2 := by linarith
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have him : (w.im - Real.sqrt 3 / 2) * (w.im + Real.sqrt 3 / 2) = 0 := by
    rw [hre] at s1; linear_combination s1 - h3 / 4
  rcases mul_eq_zero.1 him with h | h
  · left; rw [hX]; congr 2; apply Complex.ext <;> simp [ω] <;> linarith
  · right; rw [hX]; congr 2; apply Complex.ext <;> simp [ω] <;> linarith

theorem l14b_ccw_iff (A B C : ℂ) : Ccw A B C ↔ 0 < (conj (C - B) * (A - B)).im := by
  unfold Ccw
  simp only [mul_im, conj_re, conj_im, sub_re, sub_im]
  constructor <;> intro h <;> linarith

theorem l14b_cross_apex (B C : ℂ) :
    (conj (C - B) * (B + (C - B) * ω - B)).im = ‖C - B‖ ^ 2 * (Real.sqrt 3 / 2) ∧
    (conj (C - B) * (B + (C - B) * conj ω - B)).im = -(‖C - B‖ ^ 2 * (Real.sqrt 3 / 2)) := by
  simp only [add_sub_cancel_left, Complex.sq_norm, Complex.normSq_apply]
  constructor <;> simp [ω, mul_im, mul_re] <;> ring

/-- An outward equilateral apex, defined by its property, is the library's `apexOut`. -/
theorem l14b_apexOut {A B C X : ℂ} (hBC : B ≠ C) (h1 : dist X B = dist B C)
    (h2 : dist X C = dist B C) (h3 : line[ℝ, B, C].SOppSide X A) : X = apexOut A B C := by
  have hk := l14b_cross_of_sOppSide h3
  have hA : (conj (C - B) * (A - B)).im ≠ 0 := fun h0 =>
    h3.2.2 (l14b_mem_line_of_cross hBC h0)
  have hpos : 0 < ‖C - B‖ ^ 2 * (Real.sqrt 3 / 2) := by
    have := norm_pos_iff.2 (sub_ne_zero.2 hBC.symm)
    have : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    positivity
  obtain ⟨cω, cω'⟩ := l14b_cross_apex B C
  unfold apexOut
  rcases l14b_equilateral hBC h1 h2 with rfl | rfl
  · rw [cω] at hk
    split_ifs with hc
    · exfalso; rw [l14b_ccw_iff] at hc; nlinarith
    · rfl
  · rw [cω'] at hk
    split_ifs with hc
    · rfl
    · exfalso; rw [l14b_ccw_iff] at hc
      have : (conj (C - B) * (A - B)).im < 0 := lt_of_le_of_ne (not_lt.1 hc) hA
      nlinarith

/-- An inward equilateral apex, defined by its property, is the library's `apexIn`. -/
theorem l14b_apexIn {A B C X : ℂ} (hBC : B ≠ C) (h1 : dist X B = dist B C)
    (h2 : dist X C = dist B C) (h3 : line[ℝ, B, C].SSameSide X A) : X = apexIn A B C := by
  have hk := l14b_cross_of_sSameSide h3
  have hA : (conj (C - B) * (A - B)).im ≠ 0 := fun h0 =>
    h3.2.2 (l14b_mem_line_of_cross hBC h0)
  have hpos : 0 < ‖C - B‖ ^ 2 * (Real.sqrt 3 / 2) := by
    have := norm_pos_iff.2 (sub_ne_zero.2 hBC.symm)
    have : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    positivity
  obtain ⟨cω, cω'⟩ := l14b_cross_apex B C
  unfold apexIn
  rcases l14b_equilateral hBC h1 h2 with rfl | rfl
  · rw [cω] at hk
    split_ifs with hc
    · rfl
    · exfalso; rw [l14b_ccw_iff] at hc
      have : (conj (C - B) * (A - B)).im < 0 := lt_of_le_of_ne (not_lt.1 hc) hA
      nlinarith
  · rw [cω'] at hk
    split_ifs with hc
    · exfalso; rw [l14b_ccw_iff] at hc; nlinarith
    · rfl

/-! ### Mathlib-only statement -/

/-- **Lester's circle theorem**, Mathlib-only statement (apexes and Fermat points by their
defining properties, Mathlib's circumcentre and nine-point circle). -/
theorem l14_lester (t : Affine.Triangle ℝ ℂ)
    (h01 : dist (t.points 0) (t.points 1) ≠ dist (t.points 1) (t.points 2))
    (h12 : dist (t.points 1) (t.points 2) ≠ dist (t.points 2) (t.points 0))
    (h20 : dist (t.points 2) (t.points 0) ≠ dist (t.points 0) (t.points 1))
    (Xa Xb Xc Ya Yb Yc F₁ F₂ : ℂ)
    (hXa : dist Xa (t.points 1) = dist (t.points 1) (t.points 2) ∧
      dist Xa (t.points 2) = dist (t.points 1) (t.points 2) ∧
      line[ℝ, t.points 1, t.points 2].SOppSide Xa (t.points 0))
    (hXb : dist Xb (t.points 2) = dist (t.points 2) (t.points 0) ∧
      dist Xb (t.points 0) = dist (t.points 2) (t.points 0) ∧
      line[ℝ, t.points 2, t.points 0].SOppSide Xb (t.points 1))
    (hXc : dist Xc (t.points 0) = dist (t.points 0) (t.points 1) ∧
      dist Xc (t.points 1) = dist (t.points 0) (t.points 1) ∧
      line[ℝ, t.points 0, t.points 1].SOppSide Xc (t.points 2))
    (hYa : dist Ya (t.points 1) = dist (t.points 1) (t.points 2) ∧
      dist Ya (t.points 2) = dist (t.points 1) (t.points 2) ∧
      line[ℝ, t.points 1, t.points 2].SSameSide Ya (t.points 0))
    (hYb : dist Yb (t.points 2) = dist (t.points 2) (t.points 0) ∧
      dist Yb (t.points 0) = dist (t.points 2) (t.points 0) ∧
      line[ℝ, t.points 2, t.points 0].SSameSide Yb (t.points 1))
    (hYc : dist Yc (t.points 0) = dist (t.points 0) (t.points 1) ∧
      dist Yc (t.points 1) = dist (t.points 0) (t.points 1) ∧
      line[ℝ, t.points 0, t.points 1].SSameSide Yc (t.points 2))
    (hF₁ : F₁ ∈ line[ℝ, t.points 0, Xa] ∧ F₁ ∈ line[ℝ, t.points 1, Xb] ∧
      F₁ ∈ line[ℝ, t.points 2, Xc])
    (hF₂ : F₂ ∈ line[ℝ, t.points 0, Ya] ∧ F₂ ∈ line[ℝ, t.points 1, Yb] ∧
      F₂ ∈ line[ℝ, t.points 2, Yc]) :
    Concyclic ({t.ninePointCircle.center, t.circumcenter, F₁, F₂} : Set ℂ) := by
  have hinj := t.independent.injective
  have n12 : t.points 1 ≠ t.points 2 := fun h => absurd (hinj h) (by decide)
  have n20 : t.points 2 ≠ t.points 0 := fun h => absurd (hinj h) (by decide)
  have n01 : t.points 0 ≠ t.points 1 := fun h => absurd (hinj h) (by decide)
  rw [l14b_apexOut n12 hXa.1 hXa.2.1 hXa.2.2, l14b_apexOut n20 hXb.1 hXb.2.1 hXb.2.2,
    l14b_apexOut n01 hXc.1 hXc.2.1 hXc.2.2] at hF₁
  rw [l14b_apexIn n12 hYa.1 hYa.2.1 hYa.2.2, l14b_apexIn n20 hYb.1 hYb.2.1 hYb.2.2,
    l14b_apexIn n01 hYc.1 hYc.2.1 hYc.2.2] at hF₂
  rw [← bridge_ninePointCenter]
  exact lester t h01 h12 h20 F₁ F₂ hF₁ hF₂

/-! ### Witness -/

theorem l14b_dist_eq {a b c d : ℂ}
    (h : (a.re - b.re) ^ 2 + (a.im - b.im) ^ 2 = (c.re - d.re) ^ 2 + (c.im - d.im) ^ 2) :
    dist a b = dist c d := by
  rw [Complex.dist_eq, Complex.dist_eq, Complex.norm_def, Complex.norm_def,
    Complex.normSq_apply, Complex.normSq_apply]
  congr 1
  simp only [sub_re, sub_im]
  linear_combination h

theorem l14b_dist_ne {a b c d : ℂ}
    (h : (a.re - b.re) ^ 2 + (a.im - b.im) ^ 2 ≠ (c.re - d.re) ^ 2 + (c.im - d.im) ^ 2) :
    dist a b ≠ dist c d := by
  intro e
  apply h
  have e2 := congrArg (· ^ 2) e
  simp only [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im] at e2
  linear_combination e2

theorem l14b_not_collinear {a b c : ℂ}
    (h : (b - a).re * (c - a).im - (b - a).im * (c - a).re ≠ 0) :
    ¬Collinear ℝ ({a, b, c} : Set ℂ) := by
  rw [collinear_iff_of_mem (p₀ := a) (by simp)]
  rintro ⟨v, hv⟩
  obtain ⟨s, hs⟩ := hv b (by simp)
  obtain ⟨t, ht⟩ := hv c (by simp)
  apply h
  rw [hs, ht]
  simp only [vadd_eq_add, add_sub_cancel_right, Complex.real_smul, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem l14b_notMem_line {a b c : ℂ}
    (h : (conj (c - b) * (a - b)).im ≠ 0) : a ∉ line[ℝ, b, c] := by
  intro ha
  obtain ⟨r, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 ha
  apply h
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  simp only [mul_im, mul_re, conj_re, conj_im, sub_re, sub_im, add_re, add_im, ofReal_re,
    ofReal_im]
  ring

theorem l14b_oppSide {b c a x : ℂ} (u s : ℝ) (hs : s < 0)
    (ha : (conj (c - b) * (a - b)).im ≠ 0)
    (hx : x = AffineMap.lineMap (AffineMap.lineMap b c u) a s) :
    line[ℝ, b, c].SOppSide x a := by
  rw [hx]
  exact AffineSubspace.sOppSide_lineMap_left (AffineMap.lineMap_mem_affineSpan_pair u b c)
    (l14b_notMem_line ha) hs

theorem l14b_sameSide {b c a x : ℂ} (u s : ℝ) (hs : 0 < s)
    (ha : (conj (c - b) * (a - b)).im ≠ 0)
    (hx : x = AffineMap.lineMap (AffineMap.lineMap b c u) a s) :
    line[ℝ, b, c].SSameSide x a := by
  rw [hx]
  exact AffineSubspace.sSameSide_lineMap_left (AffineMap.lineMap_mem_affineSpan_pair u b c)
    (l14b_notMem_line ha) hs

theorem l14b_mem_line {p q z : ℂ} (v : ℝ) (h : z = AffineMap.lineMap p q v) : z ∈ line[ℝ, p, q] :=
  h ▸ AffineMap.lineMap_mem_affineSpan_pair v p q

theorem l14b_circumcenter (t : Affine.Triangle ℝ ℂ) (p : ℂ)
    (h1 : dist (t.points 1) p = dist (t.points 0) p)
    (h2 : dist (t.points 2) p = dist (t.points 0) p) : t.circumcenter = p := by
  refine (t.eq_circumcenter_of_dist_eq (r := dist (t.points 0) p) ?_ ?_).symm
  · rw [t.span_eq_top Complex.finrank_real_complex]; exact AffineSubspace.mem_top _ _ _
  · intro i; fin_cases i
    · rfl
    · exact h1
    · exact h2

/-- Witness for `l14_lester`. -/
theorem l14w_lester :
    ∃ t : Affine.Triangle ℝ ℂ,
      t.points = ![⟨2, 0⟩, ⟨-3/2, 3 * Real.sqrt 3 / 2⟩, ⟨-2, -2 * Real.sqrt 3⟩] ∧
      dist (t.points 0) (t.points 1) ≠ dist (t.points 1) (t.points 2) ∧
      dist (t.points 1) (t.points 2) ≠ dist (t.points 2) (t.points 0) ∧
      dist (t.points 2) (t.points 0) ≠ dist (t.points 0) (t.points 1) ∧
      (dist (⟨-7, 0⟩ : ℂ) (t.points 1) = dist (t.points 1) (t.points 2) ∧
        dist (⟨-7, 0⟩ : ℂ) (t.points 2) = dist (t.points 1) (t.points 2) ∧
        line[ℝ, t.points 1, t.points 2].SOppSide ⟨-7, 0⟩ (t.points 0)) ∧
      (dist (⟨3, -3 * Real.sqrt 3⟩ : ℂ) (t.points 2) = dist (t.points 2) (t.points 0) ∧
        dist (⟨3, -3 * Real.sqrt 3⟩ : ℂ) (t.points 0) = dist (t.points 2) (t.points 0) ∧
        line[ℝ, t.points 2, t.points 0].SOppSide ⟨3, -3 * Real.sqrt 3⟩ (t.points 1)) ∧
      (dist (⟨5/2, 5 * Real.sqrt 3 / 2⟩ : ℂ) (t.points 0) = dist (t.points 0) (t.points 1) ∧
        dist (⟨5/2, 5 * Real.sqrt 3 / 2⟩ : ℂ) (t.points 1) = dist (t.points 0) (t.points 1) ∧
        line[ℝ, t.points 0, t.points 1].SOppSide ⟨5/2, 5 * Real.sqrt 3 / 2⟩ (t.points 2)) ∧
      (dist (⟨7/2, -Real.sqrt 3 / 2⟩ : ℂ) (t.points 1) = dist (t.points 1) (t.points 2) ∧
        dist (⟨7/2, -Real.sqrt 3 / 2⟩ : ℂ) (t.points 2) = dist (t.points 1) (t.points 2) ∧
        line[ℝ, t.points 1, t.points 2].SSameSide ⟨7/2, -Real.sqrt 3 / 2⟩ (t.points 0)) ∧
      (dist (⟨-3, Real.sqrt 3⟩ : ℂ) (t.points 2) = dist (t.points 2) (t.points 0) ∧
        dist (⟨-3, Real.sqrt 3⟩ : ℂ) (t.points 0) = dist (t.points 2) (t.points 0) ∧
        line[ℝ, t.points 2, t.points 0].SSameSide ⟨-3, Real.sqrt 3⟩ (t.points 1)) ∧
      (dist (⟨-2, -Real.sqrt 3⟩ : ℂ) (t.points 0) = dist (t.points 0) (t.points 1) ∧
        dist (⟨-2, -Real.sqrt 3⟩ : ℂ) (t.points 1) = dist (t.points 0) (t.points 1) ∧
        line[ℝ, t.points 0, t.points 1].SSameSide ⟨-2, -Real.sqrt 3⟩ (t.points 2)) ∧
      ((0 : ℂ) ∈ line[ℝ, t.points 0, ⟨-7, 0⟩] ∧ (0 : ℂ) ∈ line[ℝ, t.points 1, ⟨3, -3 * Real.sqrt 3⟩] ∧
        (0 : ℂ) ∈ line[ℝ, t.points 2, ⟨5/2, 5 * Real.sqrt 3 / 2⟩]) ∧
      ((⟨-2, 4 * Real.sqrt 3 / 3⟩ : ℂ) ∈ line[ℝ, t.points 0, ⟨7/2, -Real.sqrt 3 / 2⟩] ∧
        (⟨-2, 4 * Real.sqrt 3 / 3⟩ : ℂ) ∈ line[ℝ, t.points 1, ⟨-3, Real.sqrt 3⟩] ∧
        (⟨-2, 4 * Real.sqrt 3 / 3⟩ : ℂ) ∈ line[ℝ, t.points 2, ⟨-2, -Real.sqrt 3⟩]) ∧
      t.circumcenter = ⟨-14/13, -11 * Real.sqrt 3 / 39⟩ ∧
      t.ninePointCircle.center = ⟨-11/52, -17 * Real.sqrt 3 / 156⟩ ∧
      t.ninePointCircle.center ≠ t.circumcenter ∧ t.ninePointCircle.center ≠ 0 ∧
      t.ninePointCircle.center ≠ ⟨-2, 4 * Real.sqrt 3 / 3⟩ ∧ t.circumcenter ≠ 0 ∧
      t.circumcenter ≠ ⟨-2, 4 * Real.sqrt 3 / 3⟩ ∧ (0 : ℂ) ≠ ⟨-2, 4 * Real.sqrt 3 / 3⟩ := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have nT : ¬Collinear ℝ ({⟨2, 0⟩, ⟨-3/2, 3 * Real.sqrt 3 / 2⟩, ⟨-2, -2 * Real.sqrt 3⟩} :
      Set ℂ) := l14b_not_collinear (by simp; linarith [h3])
  let t : Affine.Triangle ℝ ℂ :=
    ⟨![⟨2, 0⟩, ⟨-3/2, 3 * Real.sqrt 3 / 2⟩, ⟨-2, -2 * Real.sqrt 3⟩],
      affineIndependent_iff_not_collinear_set.2 nT⟩
  have p0 : t.points 0 = ⟨2, 0⟩ := rfl
  have p1 : t.points 1 = ⟨-3/2, 3 * Real.sqrt 3 / 2⟩ := rfl
  have p2 : t.points 2 = ⟨-2, -2 * Real.sqrt 3⟩ := rfl
  have b12 : t.points 1 ≠ t.points 2 := by
    rw [p1, p2]; intro h; have := congrArg Complex.re h; norm_num at this
  have b20 : t.points 2 ≠ t.points 0 := by
    rw [p2, p0]; intro h; have := congrArg Complex.re h; norm_num at this
  have b01 : t.points 0 ≠ t.points 1 := by
    rw [p0, p1]; intro h; have := congrArg Complex.re h; norm_num at this
  have hO : t.circumcenter = ⟨-14/13, -11 * Real.sqrt 3 / 39⟩ :=
    l14b_circumcenter t _ (l14b_dist_eq (by simp [t]; linarith [h3]))
      (l14b_dist_eq (by simp [t]; linarith [h3]))
  have hN : t.ninePointCircle.center = ⟨-11/52, -17 * Real.sqrt 3 / 156⟩ := by
    rw [← bridge_ninePointCenter, ninePointCenter, LesterProof.midpoint_OH, hO, p0, p1, p2]
    apply Complex.ext <;> simp <;> ring
  refine ⟨t, rfl, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, hO, hN, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [p0, p1, p2, hO, hN]
  -- scalene
  · exact l14b_dist_ne (by simp; linarith [h3])
  · exact l14b_dist_ne (by simp; linarith [h3])
  · exact l14b_dist_ne (by simp; linarith [h3])
  -- outer apexes
  · exact l14b_dist_eq (by simp; linarith [h3])
  · exact l14b_dist_eq (by simp; linarith [h3])
  · refine l14b_oppSide (3/7) (-37/26) (by norm_num)
      (by simp; linarith [h3]) ?_
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    apply Complex.ext <;> simp <;> first | ring | linarith [h3]
  · exact l14b_dist_eq (by simp; linarith [h3])
  · exact l14b_dist_eq (by simp; linarith [h3])
  · refine l14b_oppSide (2/3) (-14/13) (by norm_num)
      (by simp; linarith [h3]) ?_
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    apply Complex.ext <;> simp <;> first | ring | linarith [h3]
  · exact l14b_dist_eq (by simp; linarith [h3])
  · exact l14b_dist_eq (by simp; linarith [h3])
  · refine l14b_oppSide (2/5) (-19/26) (by norm_num)
      (by simp; linarith [h3]) ?_
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    apply Complex.ext <;> simp <;> first | ring | linarith [h3]
  -- inner apexes
  · exact l14b_dist_eq (by simp; linarith [h3])
  · exact l14b_dist_eq (by simp; linarith [h3])
  · refine l14b_sameSide (1/11) (37/26) (by norm_num)
      (by simp; linarith [h3]) ?_
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    apply Complex.ext <;> simp <;> first | ring | linarith [h3]
  · exact l14b_dist_eq (by simp; linarith [h3])
  · exact l14b_dist_eq (by simp; linarith [h3])
  · refine l14b_sameSide 5 (14/13) (by norm_num)
      (by simp; linarith [h3]) ?_
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    apply Complex.ext <;> simp <;> first | ring | linarith [h3]
  · exact l14b_dist_eq (by simp; linarith [h3])
  · exact l14b_dist_eq (by simp; linarith [h3])
  · refine l14b_sameSide (8/7) (19/26) (by norm_num)
      (by simp; linarith [h3]) ?_
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    apply Complex.ext <;> simp <;> first | ring | linarith [h3]
  -- Fermat points
  · refine l14b_mem_line (2/9) ?_
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    apply Complex.ext <;> simp <;> first | ring | linarith [h3]
  · refine l14b_mem_line (1/3) ?_
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    apply Complex.ext <;> simp <;> first | ring | linarith [h3]
  · refine l14b_mem_line (4/9) ?_
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    apply Complex.ext <;> simp <;> first | ring | linarith [h3]
  · refine l14b_mem_line (-8/3) ?_
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    apply Complex.ext <;> simp <;> first | ring | linarith [h3]
  · refine l14b_mem_line (1/3) ?_
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    apply Complex.ext <;> simp <;> first | ring | linarith [h3]
  · refine l14b_mem_line (10/3) ?_
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    apply Complex.ext <;> simp <;> first | ring | linarith [h3]
  -- distinctness (real parts)
  all_goals intro h; have := congrArg Complex.re h; norm_num at this

end Lester
