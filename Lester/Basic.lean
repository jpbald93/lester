import Mathlib
import Lester.Proof

/-!
# Lester's circle — statement

For a scalene triangle, the nine-point centre, the circumcentre and the
two Fermat (isogonic) points are concyclic.

We work in `ℂ` viewed as the Euclidean plane. The circumcentre and orthocentre are
Mathlib's (`Affine.Simplex.circumcenter`, `Affine.Triangle.orthocenter`). The
Fermat points are characterised as the common point of the three lines joining
each vertex to the apex of the equilateral triangle erected on the opposite side
(outward for the first Fermat point X₁₃, inward for the second X₁₄).
-/

open Complex EuclideanGeometry

namespace Lester

noncomputable section

/-- `ω = e^{iπ/3}`, written in Cartesian form. -/
def ω : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩

/-- `(A, B, C)` is positively (counter-clockwise) oriented. -/
def Ccw (A B C : ℂ) : Prop := 0 < ((starRingEnd ℂ) (B - A) * (C - A)).im

open Classical in
/-- Apex of the equilateral triangle erected **outwards** (away from `A`) on side `BC`. -/
def apexOut (A B C : ℂ) : ℂ :=
  if Ccw A B C then B + (C - B) * (starRingEnd ℂ) ω else B + (C - B) * ω

open Classical in
/-- Apex of the equilateral triangle erected **inwards** (towards `A`) on side `BC`. -/
def apexIn (A B C : ℂ) : ℂ :=
  if Ccw A B C then B + (C - B) * ω else B + (C - B) * (starRingEnd ℂ) ω

/-- `F` is the first Fermat point (X₁₃) of `ABC`. -/
def IsFermatOuter (A B C F : ℂ) : Prop :=
  F ∈ line[ℝ, A, apexOut A B C] ∧ F ∈ line[ℝ, B, apexOut B C A] ∧
    F ∈ line[ℝ, C, apexOut C A B]

/-- `F` is the second Fermat point (X₁₄) of `ABC`. -/
def IsFermatInner (A B C F : ℂ) : Prop :=
  F ∈ line[ℝ, A, apexIn A B C] ∧ F ∈ line[ℝ, B, apexIn B C A] ∧
    F ∈ line[ℝ, C, apexIn C A B]

/-- Nine-point centre: midpoint of circumcentre and orthocentre. -/
def ninePointCenter (t : Affine.Triangle ℝ ℂ) : ℂ :=
  midpoint ℝ t.circumcenter t.orthocenter

/-- **Lester's circle theorem.** The triangle is assumed *scalene*. In a typical isosceles
triangle the four points are distinct and collinear on the symmetry axis, hence not concyclic,
so "non-equilateral" alone would make the statement false (some isosceles cases are trivial). -/
theorem lester (t : Affine.Triangle ℝ ℂ)
    (h01 : dist (t.points 0) (t.points 1) ≠ dist (t.points 1) (t.points 2))
    (h12 : dist (t.points 1) (t.points 2) ≠ dist (t.points 2) (t.points 0))
    (h20 : dist (t.points 2) (t.points 0) ≠ dist (t.points 0) (t.points 1))
    (F₁ F₂ : ℂ)
    (h₁ : IsFermatOuter (t.points 0) (t.points 1) (t.points 2) F₁)
    (h₂ : IsFermatInner (t.points 0) (t.points 1) (t.points 2) F₂) :
    Concyclic ({ninePointCenter t, t.circumcenter, F₁, F₂} : Set ℂ) := by
  exact LesterProof.lester_core t h01 h12 h20 F₁ F₂ h₁ h₂

end

end Lester
