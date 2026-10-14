import Mathlib

/-!
# Lester's theorem — proof

Self-contained (imports only Mathlib) so that `Lester/Basic.lean` can import it without an
import cycle. The definitions `ω`, `Ccw`, `apexOut`, `apexIn` are verbatim copies of those of
`Lester.Basic`, hence definitionally equal to them; `Lester.lester` is closed by
`LesterProof.lester_core`.

Strategy: normalise `A = 0`, `B = 1`, `C = w = u + v i` via `ζ z = (z - A) / (B - A)`. In these
coordinates all four points satisfy the explicit circle equation `lcE u v x y = 0`, whose leading
coefficient `lcA u v = -24 v² (2u - 1) (u² - 2u + v²) (u² + v² - 1)` is nonzero for a scalene
non-degenerate triangle. Each Fermat point is handled uniformly with `K = ±√3` (`K ^ 2 = 3`).
-/

open Complex EuclideanGeometry

namespace LesterProof

noncomputable section

/-- Copy of `Lester.ω`. -/
def ω : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩

/-- Copy of `Lester.Ccw`. -/
def Ccw (A B C : ℂ) : Prop := 0 < ((starRingEnd ℂ) (B - A) * (C - A)).im

open Classical in
/-- Copy of `Lester.apexOut`. -/
def apexOut (A B C : ℂ) : ℂ :=
  if Ccw A B C then B + (C - B) * (starRingEnd ℂ) ω else B + (C - B) * ω

open Classical in
/-- Copy of `Lester.apexIn`. -/
def apexIn (A B C : ℂ) : ℂ :=
  if Ccw A B C then B + (C - B) * ω else B + (C - B) * (starRingEnd ℂ) ω

/-! ## The circle in normalised coordinates -/

def lcA (u v : ℝ) : ℝ := -48*u^5*v^2 + 120*u^4*v^2 - 96*u^3*v^4 + 144*u^2*v^4 - 120*u^2*v^2 - 48*u*v^6 + 48*u*v^2 + 24*v^6 - 24*v^4
def lcB1 (u v : ℝ) : ℝ := 18*u^8 - 72*u^7 + 48*u^6*v^2 + 126*u^6 - 96*u^5*v^2 - 126*u^5 + 36*u^4*v^4 - 30*u^4*v^2 + 72*u^4 + 24*u^3*v^4 + 60*u^3*v^2 - 18*u^3 - 102*u^2*v^4 + 36*u^2*v^2 + 48*u*v^6 - 6*u*v^4 - 18*u*v^2 - 6*v^8 - 10*v^6 + 12*v^4
def lcB2 (u v : ℝ) : ℝ := 24*u^7*v - 84*u^6*v + 72*u^5*v^3 + 96*u^5*v - 180*u^4*v^3 - 30*u^4*v + 72*u^3*v^5 + 48*u^3*v^3 - 12*u^3*v - 108*u^2*v^5 + 108*u^2*v^3 + 6*u^2*v + 24*u*v^7 + 16*u*v^5 - 60*u*v^3 - 12*v^7 + 10*v^5 + 6*v^3
def lcC (u v : ℝ) : ℝ := -9*u^8 + 18*u^7 - 24*u^6*v^2 + 54*u^5*v^2 - 18*u^5 - 18*u^4*v^4 + 9*u^4 + 22*u^3*v^4 - 36*u^3*v^2 + 6*u^2*v^2 - 14*u*v^6 + 14*u*v^4 + 3*v^8 - 3*v^4

/-- The Lester circle through `0`, `1`, `u + v i`-triangle's four centres. -/
def lcE (u v x y : ℝ) : ℝ := lcA u v * (x ^ 2 + y ^ 2) + lcB1 u v * x + lcB2 u v * y + lcC u v

theorem lcA_eq (u v : ℝ) :
    lcA u v = -24 * v ^ 2 * (2 * u - 1) * (u ^ 2 - 2 * u + v ^ 2) * (u ^ 2 + v ^ 2 - 1) := by
  unfold lcA; ring

/-- The circumcentre `(1/2, y)` with `2 v y = u² + v² - u` is on the circle. -/
theorem lcE_O {u v y : ℝ} (hv : v ≠ 0) (hy : 2 * v * y = u ^ 2 + v ^ 2 - u) :
    lcE u v (1 / 2) y = 0 := by
  have h : 4 * v ^ 2 * lcE u v (1 / 2) y = 0 := by
    unfold lcE lcA lcB1 lcB2 lcC
    linear_combination (-96*y*u^5*v^3 + 240*y*u^4*v^3 - 192*y*u^3*v^5 + 288*y*u^2*v^5 - 240*y*u^2*v^3 - 96*y*u*v^7 + 96*y*u*v^3 + 48*y*v^7 - 48*y*v^5 + 72*u^5*v^2 - 180*u^4*v^2 - 48*u^3*v^4 + 144*u^3*v^2 + 72*u^2*v^4 - 36*u^2*v^2 + 8*u*v^6 - 48*u*v^4 - 4*v^6 + 12*v^4) * hy
  exact (mul_eq_zero.1 h).resolve_left (by positivity)

/-- The nine-point centre `((1 + u - 1/2)/2, (v - y)/2)` is on the circle. -/
theorem lcE_N {u v yO : ℝ} (hv : v ≠ 0) (hy : 2 * v * yO = u ^ 2 + v ^ 2 - u) :
    lcE u v ((1 + u - 1 / 2) / 2) ((v - yO) / 2) = 0 := by
  have h : 4 * v ^ 2 * lcE u v ((1 + u - 1 / 2) / 2) ((v - yO) / 2) = 0 := by
    unfold lcE lcA lcB1 lcB2 lcC
    linear_combination (-24*yO*u^5*v^3 + 60*yO*u^4*v^3 - 48*yO*u^3*v^5 + 72*yO*u^2*v^5 - 60*yO*u^2*v^3 - 24*yO*u*v^7 + 24*yO*u*v^3 + 12*yO*v^7 - 12*yO*v^5 - 36*u^7*v^2 + 126*u^6*v^2 - 60*u^5*v^4 - 126*u^5*v^2 + 150*u^4*v^4 - 12*u^3*v^6 - 84*u^3*v^4 + 54*u^3*v^2 + 18*u^2*v^6 - 24*u^2*v^4 - 18*u^2*v^2 + 12*u*v^8 - 22*u*v^6 + 30*u*v^4 - 6*v^8 + 8*v^6 - 6*v^4) * hy
  exact (mul_eq_zero.1 h).resolve_left (by positivity)

/-- A Fermat point (either one, `K = ±√3`) is on the circle. -/
theorem lcE_F {u v K x y r s : ℝ} (hK : K ^ 2 = 3) (hu : 2 * u - 1 ≠ 0)
    (hx1 : x = r * (1 + (u - 1) / 2 - v * K / 2)) (hy1 : y = r * ((u - 1) * K / 2 + v / 2))
    (hx2 : x = 1 + s * (u - (u / 2 - v * K / 2) - 1)) (hy2 : y = s * (v - (u * K / 2 + v / 2))) :
    lcE u v x y = 0 := by
  have hrD : r * ((1 + (u - 1) / 2 - v * K / 2) * (v - (u * K / 2 + v / 2))
      - ((u - 1) * K / 2 + v / 2) * (u - (u / 2 - v * K / 2) - 1)) = v - (u * K / 2 + v / 2) := by
    linear_combination (v - (u * K / 2 + v / 2)) * (hx1.symm.trans hx2)
      - (u - (u / 2 - v * K / 2) - 1) * (hy1.symm.trans hy2)
  have hD : (1 + (u - 1) / 2 - v * K / 2) * (v - (u * K / 2 + v / 2))
      - ((u - 1) * K / 2 + v / 2) * (u - (u / 2 - v * K / 2) - 1) ≠ 0 := by
    intro h0
    have h1 : K * (u ^ 2 - u + v ^ 2 + 1) = 3 * v := by linear_combination (-2) * h0 + (v / 2) * hK
    have h2 : 3 * (u ^ 2 - u + v ^ 2 + 1) ^ 2 = 9 * v ^ 2 := by
      linear_combination (-(u ^ 2 - u + v ^ 2 + 1) ^ 2) * hK + (K * (u ^ 2 - u + v ^ 2 + 1) + 3 * v) * h1
    have hu2 : 0 < (u - 1 / 2) ^ 2 := by
      have : u - 1 / 2 ≠ 0 := fun h => hu (by linear_combination 2 * h)
      positivity
    nlinarith [sq_nonneg (v ^ 2 - 3 / 4), mul_pos hu2 (by positivity : (0:ℝ) < v ^ 2 + 3 / 4),
      sq_nonneg ((u - 1 / 2) ^ 2)]
  subst hx1 hy1
  have h : (((1 + (u - 1) / 2 - v * K / 2) * (v - (u * K / 2 + v / 2))
      - ((u - 1) * K / 2 + v / 2) * (u - (u / 2 - v * K / 2) - 1))) ^ 2 *
      lcE u v (r * (1 + (u - 1) / 2 - v * K / 2)) (r * ((u - 1) * K / 2 + v / 2)) = 0 := by
    unfold lcE lcA lcB1 lcB2 lcC
    linear_combination
      ((-48*u^5*v^2 + 120*u^4*v^2 - 96*u^3*v^4 + 144*u^2*v^4 - 120*u^2*v^2 - 48*u*v^6 + 48*u*v^2 + 24*v^6 - 24*v^4) * ((1 + (u - 1) / 2 - v * K / 2) ^ 2 + ((u - 1) * K / 2 + v / 2) ^ 2)
        * (r * ((1 + (u - 1) / 2 - v * K / 2) * (v - (u * K / 2 + v / 2))
          - ((u - 1) * K / 2 + v / 2) * (u - (u / 2 - v * K / 2) - 1)) + (v - (u * K / 2 + v / 2)))
        + ((18*u^8 - 72*u^7 + 48*u^6*v^2 + 126*u^6 - 96*u^5*v^2 - 126*u^5 + 36*u^4*v^4 - 30*u^4*v^2 + 72*u^4 + 24*u^3*v^4 + 60*u^3*v^2 - 18*u^3 - 102*u^2*v^4 + 36*u^2*v^2 + 48*u*v^6 - 6*u*v^4 - 18*u*v^2 - 6*v^8 - 10*v^6 + 12*v^4) * (1 + (u - 1) / 2 - v * K / 2) + (24*u^7*v - 84*u^6*v + 72*u^5*v^3 + 96*u^5*v - 180*u^4*v^3 - 30*u^4*v + 72*u^3*v^5 + 48*u^3*v^3 - 12*u^3*v - 108*u^2*v^5 + 108*u^2*v^3 + 6*u^2*v + 24*u*v^7 + 16*u*v^5 - 60*u*v^3 - 12*v^7 + 10*v^5 + 6*v^3) * ((u - 1) * K / 2 + v / 2))
          * ((1 + (u - 1) / 2 - v * K / 2) * (v - (u * K / 2 + v / 2))
            - ((u - 1) * K / 2 + v / 2) * (u - (u / 2 - v * K / 2) - 1))) * hrD
      + (-27*K^2*u^9*v^2/8 + 243*K^2*u^8*v^2/16 - 21*K^2*u^7*v^4/2 - 81*K^2*u^7*v^2/4 + 147*K^2*u^6*v^4/4 - 45*K^2*u^5*v^6/4 - 147*K^2*u^5*v^4/4 + 81*K^2*u^5*v^2/4 + 225*K^2*u^4*v^6/8 - 243*K^2*u^4*v^2/16 - 9*K^2*u^3*v^8/2 - 75*K^2*u^3*v^6/4 + 33*K^2*u^3*v^4/2 + 27*K^2*u^3*v^2/8 + 27*K^2*u^2*v^8/4 - 51*K^2*u^2*v^4/8 - 3*K^2*u*v^10/8 - 9*K^2*u*v^8/4 + 9*K^2*u*v^6/4 + 3*K^2*u*v^4/8 + 3*K^2*v^10/16 - 3*K^2*v^6/16 + 3*K*u^11*v/4 - 33*K*u^10*v/8 + 15*K*u^9*v^3/4 + 69*K*u^9*v/8 - 135*K*u^8*v^3/8 - 63*K*u^8*v/8 + 15*K*u^7*v^5/2 + 57*K*u^7*v^3/2 - 105*K*u^6*v^5/4 - 21*K*u^6*v^3 + 63*K*u^6*v/8 + 15*K*u^5*v^7/2 + 127*K*u^5*v^5/4 - 69*K*u^5*v/8 - 75*K*u^4*v^7/4 - 55*K*u^4*v^5/4 + 105*K*u^4*v^3/8 + 33*K*u^4*v/8 + 15*K*u^3*v^9/4 + 25*K*u^3*v^7/2 - 45*K*u^3*v^3/4 - 3*K*u^3*v/4 - 45*K*u^2*v^9/8 + 5*K*u^2*v^5/8 + 9*K*u^2*v^3/2 + 3*K*u*v^11/4 + 5*K*u*v^9/8 - 5*K*u*v^5/8 - 3*K*u*v^3/4 - 3*K*v^11/8 + 5*K*v^9/8 - 5*K*v^7/8 + 3*K*v^5/8 - 9*u^9*v^2/8 + 81*u^8*v^2/16 - 7*u^7*v^4/2 - 27*u^7*v^2/4 + 49*u^6*v^4/4 - 15*u^5*v^6/4 - 49*u^5*v^4/4 + 27*u^5*v^2/4 + 75*u^4*v^6/8 - 81*u^4*v^2/16 - 3*u^3*v^8/2 - 25*u^3*v^6/4 + 11*u^3*v^4/2 + 9*u^3*v^2/8 + 9*u^2*v^8/4 - 17*u^2*v^4/8 - u*v^10/8 - 3*u*v^8/4 + 3*u*v^6/4 + u*v^4/8 + v^10/16 - v^6/16) * hK
  exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero 2 hD)

/-! ## Glue: from the triangle to normalised coordinates -/

theorem ccw_rot (A B C : ℂ) : Ccw B C A ↔ Ccw A B C := by
  unfold Ccw
  have : ((starRingEnd ℂ) (C - B) * (A - B)).im = ((starRingEnd ℂ) (B - A) * (C - A)).im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
    ring
  rw [this]

theorem sq_sqrt3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem neg_sq_sqrt3 : (-Real.sqrt 3) ^ 2 = 3 := by rw [neg_sq, sq_sqrt3]

theorem conj_ω : (starRingEnd ℂ) ω = ⟨1 / 2, -Real.sqrt 3 / 2⟩ := by
  apply Complex.ext <;> simp [ω, neg_div]

theorem ω_eq : ω = ⟨1 / 2, Real.sqrt 3 / 2⟩ := rfl

theorem apexOut_eq (A B C : ℂ) : ∃ K : ℝ, K ^ 2 = 3 ∧
    apexOut A B C = B + (C - B) * ⟨1 / 2, K / 2⟩ ∧ apexOut B C A = C + (A - C) * ⟨1 / 2, K / 2⟩ := by
  unfold apexOut
  rw [show Ccw B C A ↔ Ccw A B C from ccw_rot A B C]
  split_ifs
  · exact ⟨-Real.sqrt 3, neg_sq_sqrt3, by rw [conj_ω, neg_div], by rw [conj_ω, neg_div]⟩
  · exact ⟨Real.sqrt 3, sq_sqrt3, rfl, rfl⟩

theorem apexIn_eq (A B C : ℂ) : ∃ K : ℝ, K ^ 2 = 3 ∧
    apexIn A B C = B + (C - B) * ⟨1 / 2, K / 2⟩ ∧ apexIn B C A = C + (A - C) * ⟨1 / 2, K / 2⟩ := by
  unfold apexIn
  rw [show Ccw B C A ↔ Ccw A B C from ccw_rot A B C]
  split_ifs
  · exact ⟨Real.sqrt 3, sq_sqrt3, rfl, rfl⟩
  · exact ⟨-Real.sqrt 3, neg_sq_sqrt3, by rw [conj_ω, neg_div], by rw [conj_ω, neg_div]⟩

/-- A Fermat-type point, in normalised coordinates, lies on the circle. -/
theorem fermat_on (A B C F : ℂ) (hAB : B - A ≠ 0) (K : ℝ) (hK : K ^ 2 = 3)
    (hu : 2 * ((C - A) / (B - A)).re - 1 ≠ 0)
    (h1 : F ∈ line[ℝ, A, B + (C - B) * ⟨1 / 2, K / 2⟩])
    (h2 : F ∈ line[ℝ, B, C + (A - C) * ⟨1 / 2, K / 2⟩]) :
    lcE ((C - A) / (B - A)).re ((C - A) / (B - A)).im ((F - A) / (B - A)).re
      ((F - A) / (B - A)).im = 0 := by
  obtain ⟨r, hr⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 h1
  obtain ⟨s, hs⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 h2
  have e1 : (F - A) / (B - A) = r * (1 + ((C - A) / (B - A) - 1) * ⟨1 / 2, K / 2⟩) := by
    rw [← hr, AffineMap.lineMap_apply_module, Complex.real_smul, Complex.real_smul]
    push_cast
    field_simp
    ring
  have e2 : (F - A) / (B - A) = 1 + s * ((C - A) / (B - A) * (1 - ⟨1 / 2, K / 2⟩) - 1) := by
    rw [← hs, AffineMap.lineMap_apply_module, Complex.real_smul, Complex.real_smul]
    push_cast
    field_simp
    ring
  apply lcE_F hK hu (r := r) (s := s)
  · rw [e1]; simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]; ring
  · rw [e1]; simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]; ring
  · rw [e2]; simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]; ring
  · rw [e2]; simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]; ring

theorem dist_ζ (A B z₁ z₂ : ℂ) (hAB : B - A ≠ 0) :
    dist z₁ z₂ = ‖B - A‖ * ‖(z₁ - A) / (B - A) - (z₂ - A) / (B - A)‖ := by
  rw [dist_eq_norm, ← norm_mul]
  congr 1
  field_simp
  ring

theorem norm_sq' (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

theorem norm_eq_of {x y : ℂ} (h : x.re ^ 2 + x.im ^ 2 = y.re ^ 2 + y.im ^ 2) : ‖x‖ = ‖y‖ := by
  rw [← norm_sq', ← norm_sq'] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem cospherical_of_eq (A B : ℂ) (hAB : B - A ≠ 0) (a b1 b2 c : ℝ) (ha : a ≠ 0) (S : Set ℂ)
    (h : ∀ z ∈ S, a * (((z - A) / (B - A)).re ^ 2 + ((z - A) / (B - A)).im ^ 2)
      + b1 * ((z - A) / (B - A)).re + b2 * ((z - A) / (B - A)).im + c = 0) :
    Cospherical S := by
  refine ⟨A + (B - A) * ⟨-b1 / (2 * a), -b2 / (2 * a)⟩,
    ‖B - A‖ * Real.sqrt ((b1 ^ 2 + b2 ^ 2) / (4 * a ^ 2) - c / a), fun z hz => ?_⟩
  have hz := h z hz
  have e : z - (A + (B - A) * ⟨-b1 / (2 * a), -b2 / (2 * a)⟩)
      = (B - A) * ((z - A) / (B - A) - ⟨-b1 / (2 * a), -b2 / (2 * a)⟩) := by
    field_simp
    ring
  rw [dist_eq_norm, e, norm_mul]
  congr 1
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp only [Complex.sub_re, Complex.sub_im]
  set x := ((z - A) / (B - A)).re
  set y := ((z - A) / (B - A)).im
  have key : (x - -b1 / (2 * a)) * (x - -b1 / (2 * a)) + (y - -b2 / (2 * a)) * (y - -b2 / (2 * a))
      - ((b1 ^ 2 + b2 ^ 2) / (4 * a ^ 2) - c / a)
      = (a * (x ^ 2 + y ^ 2) + b1 * x + b2 * y + c) / a := by
    field_simp
    ring
  rw [hz, zero_div] at key
  linarith

theorem centroid_eq (t : Affine.Triangle ℝ ℂ) :
    (Finset.univ : Finset (Fin 3)).centroid ℝ t.points
      = (t.points 0 + t.points 1 + t.points 2) / 3 := by
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination]
  · simp [Fin.sum_univ_three, Finset.centroidWeights_apply, Complex.real_smul]
    ring
  · rw [Finset.sum_centroidWeights_eq_one_of_card_ne_zero]; simp

theorem midpoint_OH (t : Affine.Triangle ℝ ℂ) :
    midpoint ℝ t.circumcenter t.orthocenter
      = (t.points 0 + t.points 1 + t.points 2 - t.circumcenter) / 2 := by
  rw [Affine.Triangle.orthocenter_eq_smul_vsub_vadd_circumcenter, centroid_eq,
    midpoint_eq_smul_add]
  simp only [vsub_eq_sub, vadd_eq_add, invOf_eq_inv, Complex.real_smul]
  push_cast
  ring

theorem lester_core (t : Affine.Triangle ℝ ℂ)
    (h01 : dist (t.points 0) (t.points 1) ≠ dist (t.points 1) (t.points 2))
    (h12 : dist (t.points 1) (t.points 2) ≠ dist (t.points 2) (t.points 0))
    (h20 : dist (t.points 2) (t.points 0) ≠ dist (t.points 0) (t.points 1))
    (F₁ F₂ : ℂ)
    (h₁ : F₁ ∈ line[ℝ, t.points 0, apexOut (t.points 0) (t.points 1) (t.points 2)] ∧
      F₁ ∈ line[ℝ, t.points 1, apexOut (t.points 1) (t.points 2) (t.points 0)] ∧
      F₁ ∈ line[ℝ, t.points 2, apexOut (t.points 2) (t.points 0) (t.points 1)])
    (h₂ : F₂ ∈ line[ℝ, t.points 0, apexIn (t.points 0) (t.points 1) (t.points 2)] ∧
      F₂ ∈ line[ℝ, t.points 1, apexIn (t.points 1) (t.points 2) (t.points 0)] ∧
      F₂ ∈ line[ℝ, t.points 2, apexIn (t.points 2) (t.points 0) (t.points 1)]) :
    Concyclic ({midpoint ℝ t.circumcenter t.orthocenter, t.circumcenter, F₁, F₂} : Set ℂ) := by
  set A := t.points 0 with hA
  set B := t.points 1 with hB
  set C := t.points 2 with hC
  set O := t.circumcenter with hO
  have hinj := t.independent.injective
  have hAB : B - A ≠ 0 := sub_ne_zero.2 fun h => absurd (hinj h) (by decide)
  set w := (C - A) / (B - A) with hw
  set u := w.re with hu_def
  set v := w.im with hv_def
  have hζA : (A - A) / (B - A) = 0 := by simp
  have hζB : (B - A) / (B - A) = 1 := div_self hAB
  have hnA : 0 < ‖B - A‖ := norm_pos_iff.2 hAB
  -- non-degeneracy: `v ≠ 0`
  have hv : v ≠ 0 := by
    intro hv0
    have hcol : Collinear ℝ ({C, A, B} : Set ℂ) := by
      apply collinear_insert_of_mem_affineSpan_pair
      refine (mem_affineSpan_pair_iff_exists_lineMap_eq).2 ⟨u, ?_⟩
      rw [AffineMap.lineMap_apply_module, Complex.real_smul, Complex.real_smul]
      push_cast
      have hw' : (u : ℂ) = w := Complex.ext (by simp [u]) (by simp [v, hv0])
      rw [hw', hw]
      field_simp
      ring
    have hind : AffineIndependent ℝ ![A, B, C] := by
      convert t.independent using 1
      ext i; fin_cases i <;> rfl
    rw [affineIndependent_iff_not_collinear_set] at hind
    apply hind
    convert hcol using 1
    ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  -- scalene ⇒ the three factors of the leading coefficient are nonzero
  have hu : 2 * u - 1 ≠ 0 := by
    intro h; apply h12
    rw [dist_ζ A B _ _ hAB, dist_ζ A B _ _ hAB, hζB, hζA, ← hw]
    congr 1; apply norm_eq_of
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.zero_re, Complex.zero_im]
    linear_combination (-1 : ℝ) * h
  have hBC : u ^ 2 - 2 * u + v ^ 2 ≠ 0 := by
    intro h; apply h01
    rw [dist_ζ A B _ _ hAB, dist_ζ A B _ _ hAB, hζB, hζA, ← hw]
    congr 1; apply norm_eq_of
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.zero_re, Complex.zero_im]
    linear_combination (-1 : ℝ) * h
  have hCA : u ^ 2 + v ^ 2 - 1 ≠ 0 := by
    intro h; apply h20
    rw [dist_ζ A B _ _ hAB, dist_ζ A B _ _ hAB, hζB, hζA, ← hw]
    congr 1; apply norm_eq_of
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.zero_re, Complex.zero_im]
    linear_combination h
  have ha : lcA u v ≠ 0 := by
    rw [lcA_eq]
    have : (2 : ℝ) * u - 1 ≠ 0 := hu
    have : v ^ 2 ≠ 0 := pow_ne_zero 2 hv
    simp_all
  -- circumcentre in normalised coordinates
  set o := (O - A) / (B - A) with ho
  have hdO : ∀ i, dist (t.points i) O = t.circumradius := t.dist_circumcenter_eq_circumradius
  have hOAB : ‖(A - A) / (B - A) - o‖ = ‖(B - A) / (B - A) - o‖ := by
    have := (hdO 0).trans (hdO 1).symm
    rw [dist_ζ A B _ _ hAB, dist_ζ A B _ _ hAB] at this
    exact mul_left_cancel₀ hnA.ne' this
  have hOAC : ‖(A - A) / (B - A) - o‖ = ‖(C - A) / (B - A) - o‖ := by
    have := (hdO 0).trans (hdO 2).symm
    rw [dist_ζ A B _ _ hAB, dist_ζ A B _ _ hAB] at this
    exact mul_left_cancel₀ hnA.ne' this
  rw [hζA, hζB] at hOAB
  rw [hζA, ← hw] at hOAC
  have e1 := congrArg (· ^ 2) hOAB
  have e2 := congrArg (· ^ 2) hOAC
  simp only [norm_sq', Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.zero_re, Complex.zero_im] at e1 e2
  have hore : o.re = 1 / 2 := by linear_combination e1 / 2
  have hoim : 2 * v * o.im = u ^ 2 + v ^ 2 - u := by
    rw [hore] at e2; linear_combination e2
  -- the circle
  refine ⟨?_, coplanar_of_finrank_eq_two _ Complex.finrank_real_complex⟩
  apply cospherical_of_eq A B hAB (lcA u v) (lcB1 u v) (lcB2 u v) (lcC u v) ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro z (rfl | rfl | rfl | rfl)
  · have eN : (midpoint ℝ O t.orthocenter - A) / (B - A) = (1 + w - o) / 2 := by
      rw [midpoint_OH, ← hA, ← hB, ← hC, ← hO, hw, ho]
      field_simp
      ring
    show lcE u v _ _ = 0
    rw [eN]
    have := lcE_N (u := u) (v := v) hv hoim
    convert this using 2
    · rw [Complex.div_ofNat_re, Complex.sub_re, Complex.add_re, Complex.one_re, hore]
    · rw [Complex.div_ofNat_im, Complex.sub_im, Complex.add_im, Complex.one_im, zero_add]
  · show lcE u v _ _ = 0
    rw [← ho, hore]
    exact lcE_O hv hoim
  · obtain ⟨K, hK, e1, e2⟩ := apexOut_eq A B C
    rw [e1] at h₁; rw [e2] at h₁
    exact fermat_on A B C _ hAB K hK hu h₁.1 h₁.2.1
  · obtain ⟨K, hK, e1, e2⟩ := apexIn_eq A B C
    rw [e1] at h₂; rw [e2] at h₂
    exact fermat_on A B C _ hAB K hK hu h₂.1 h₂.2.1

end

end LesterProof
