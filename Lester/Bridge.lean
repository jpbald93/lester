import Lester.Basic

/-!
# Bridge lemmas: local definitions ↔ Mathlib notions

One lemma per definition of `Lester.Basic`.
-/

open Complex EuclideanGeometry

attribute [local instance] Complex.finrank_real_complex_fact

namespace Lester

/-- `ω` is `exp (π/3 · i)`. -/
theorem bridge_ω : ω = Complex.exp (↑(Real.pi / 3) * I) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  apply Complex.ext <;> simp [ω]

/-- `Ccw` is positivity of Mathlib's area form for the standard orientation of `ℂ`. -/
theorem bridge_Ccw (A B C : ℂ) :
    Ccw A B C ↔ 0 < Complex.orientation.areaForm (B - A) (C - A) := by
  rw [Complex.areaForm]; rfl

theorem norm_ω : ‖ω‖ = 1 := by
  rw [bridge_ω, Complex.norm_exp_ofReal_mul_I]

theorem norm_conj_ω : ‖(starRingEnd ℂ) ω‖ = 1 := by
  rw [Complex.norm_conj, norm_ω]

theorem norm_ω_sub_one : ‖ω - 1‖ = 1 := by
  have h : ω - 1 = ⟨-(1 / 2), Real.sqrt 3 / 2⟩ := by apply Complex.ext <;> simp [ω]; norm_num
  rw [h, Complex.norm_def, Complex.normSq_mk]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [show -(1 / 2 : ℝ) * -(1 / 2) + Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = 1 by nlinarith]
  simp

theorem norm_conj_ω_sub_one : ‖(starRingEnd ℂ) ω - 1‖ = 1 := by
  rw [← norm_ω_sub_one, ← Complex.norm_conj, map_sub, map_one]
  simp

/-- `apexOut A B C` is the apex of an equilateral triangle on `BC`. -/
theorem bridge_apexOut (A B C : ℂ) :
    dist (apexOut A B C) B = dist B C ∧ dist (apexOut A B C) C = dist B C := by
  unfold apexOut
  split_ifs
  · refine ⟨?_, ?_⟩
    · rw [dist_eq_norm, add_sub_cancel_left, norm_mul, norm_conj_ω, mul_one, dist_comm,
        dist_eq_norm]
    · rw [dist_eq_norm, show B + (C - B) * (starRingEnd ℂ) ω - C =
          (C - B) * ((starRingEnd ℂ) ω - 1) by ring, norm_mul, norm_conj_ω_sub_one, mul_one,
        dist_comm, dist_eq_norm]
  · refine ⟨?_, ?_⟩
    · rw [dist_eq_norm, add_sub_cancel_left, norm_mul, norm_ω, mul_one, dist_comm, dist_eq_norm]
    · rw [dist_eq_norm, show B + (C - B) * ω - C = (C - B) * (ω - 1) by ring, norm_mul,
        norm_ω_sub_one, mul_one, dist_comm, dist_eq_norm]

/-- `apexIn A B C` is the apex of an equilateral triangle on `BC`. -/
theorem bridge_apexIn (A B C : ℂ) :
    dist (apexIn A B C) B = dist B C ∧ dist (apexIn A B C) C = dist B C := by
  unfold apexIn
  split_ifs
  · refine ⟨?_, ?_⟩
    · rw [dist_eq_norm, add_sub_cancel_left, norm_mul, norm_ω, mul_one, dist_comm, dist_eq_norm]
    · rw [dist_eq_norm, show B + (C - B) * ω - C = (C - B) * (ω - 1) by ring, norm_mul,
        norm_ω_sub_one, mul_one, dist_comm, dist_eq_norm]
  · refine ⟨?_, ?_⟩
    · rw [dist_eq_norm, add_sub_cancel_left, norm_mul, norm_conj_ω, mul_one, dist_comm,
        dist_eq_norm]
    · rw [dist_eq_norm, show B + (C - B) * (starRingEnd ℂ) ω - C =
          (C - B) * ((starRingEnd ℂ) ω - 1) by ring, norm_mul, norm_conj_ω_sub_one, mul_one,
        dist_comm, dist_eq_norm]

/-- The first Fermat point is collinear with each vertex and the opposite outer apex. -/
theorem bridge_IsFermatOuter {A B C F : ℂ} (h : IsFermatOuter A B C F) :
    Collinear ℝ {F, A, apexOut A B C} ∧ Collinear ℝ {F, B, apexOut B C A} ∧
      Collinear ℝ {F, C, apexOut C A B} :=
  ⟨collinear_insert_of_mem_affineSpan_pair h.1, collinear_insert_of_mem_affineSpan_pair h.2.1,
    collinear_insert_of_mem_affineSpan_pair h.2.2⟩

/-- The second Fermat point is collinear with each vertex and the opposite inner apex. -/
theorem bridge_IsFermatInner {A B C F : ℂ} (h : IsFermatInner A B C F) :
    Collinear ℝ {F, A, apexIn A B C} ∧ Collinear ℝ {F, B, apexIn B C A} ∧
      Collinear ℝ {F, C, apexIn C A B} :=
  ⟨collinear_insert_of_mem_affineSpan_pair h.1, collinear_insert_of_mem_affineSpan_pair h.2.1,
    collinear_insert_of_mem_affineSpan_pair h.2.2⟩

/-- Our nine-point centre is the centre of Mathlib's nine-point circle. -/
theorem bridge_ninePointCenter (t : Affine.Triangle ℝ ℂ) :
    ninePointCenter t = t.ninePointCircle.center := by
  rw [ninePointCenter, Affine.Simplex.ninePointCircle_center,
    Affine.Triangle.orthocenter_eq_smul_vsub_vadd_circumcenter, midpoint_eq_smul_add]
  simp only [vsub_eq_sub, vadd_eq_add]
  simp only [invOf_eq_inv]
  push_cast
  module

end Lester
