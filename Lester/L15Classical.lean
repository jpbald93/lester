import Lester.Bridge
import Lester.Proof

/-!
# Layer 15: classical-statement comparison

Layer 15. These definitions and statements were written independently, from textbook statements,
by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves
(or proves part of) one of them from this development.
-/


/-!
# Paper D — classical statements D1–D7 (blind formalisation)

All statements live in the Euclidean plane `Pt := EuclideanSpace ℝ (Fin 2)`.
Constructed objects (second intersection points, Clifford points, Fermat points,
Thébault circles, auxiliary circumcentres, bisector feet) are passed in as data
together with their DEFINING property; well-definedness facts that are needed only
to make such data exist are stated separately as `_obligation` theorems.
-/

open EuclideanGeometry

noncomputable section

namespace Lester.Classical

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-! ## D1 — Clifford's circle theorems -/

/-- OWN DEFINITION. General position hypothesis of D1 for `n` circles `c i` through a
common point `M`: genuine circles (positive radius), pairwise distinct, `P i j` is a
second common point of `c i` and `c j` different from `M`, and for any three circles the
three second points are not collinear. (Since distinct circles meet in at most two points,
`P i j` is uniquely determined by these conditions.) -/
structure CliffordGP (n : ℕ) (c : Fin n → Sphere Pt) (M : Pt) (P : Fin n → Fin n → Pt) :
    Prop where
  radius_pos : ∀ i, 0 < (c i).radius
  through_M : ∀ i, M ∈ c i
  distinct : Function.Injective c
  second_mem : ∀ i j, i ≠ j → P i j ∈ c i ∧ P i j ∈ c j
  second_ne : ∀ i j, i ≠ j → P i j ≠ M
  noncollinear : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ Collinear ℝ {P i j, P i k, P j k}

/-- OWN DEFINITION. `X` lies on every circle `Γ_ijk` (through the non-collinear points
`P i j, P i k, P j k`) for `i, j, k` pairwise distinct in `S`. For `S` with four elements
this says that `X` is a common point of the four circles of D1(a) (a "Clifford point").
Because `P i j, P i k, P j k` are non-collinear, `Cospherical {P i j, P i k, P j k, X}`
means exactly that `X` lies on their (unique) circumcircle. -/
def OnAllGamma {n : ℕ} (P : Fin n → Fin n → Pt) (S : Finset (Fin n)) (X : Pt) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S, i ≠ j → i ≠ k → j ≠ k →
    Cospherical ({P i j, P i k, P j k, X} : Set Pt)

/-- D1(a), Clifford n = 4: the four circles `Γ_123, Γ_124, Γ_134, Γ_234` have a common
point. -/
def classical_D1_a (c : Fin 4 → Sphere Pt) (M : Pt) (P : Fin 4 → Fin 4 → Pt)
    (h : CliffordGP 4 c M P) : Prop := 
    ∃ X : Pt, OnAllGamma P Finset.univ X


/-- D1(b), Clifford n = 5: the five Clifford points `X l` (of the four circles obtained by
omitting circle `l`) lie on one circle. -/
def classical_D1_b (c : Fin 5 → Sphere Pt) (M : Pt) (P : Fin 5 → Fin 5 → Pt)
    (h : CliffordGP 5 c M P) (X : Fin 5 → Pt)
    (hX : ∀ l, OnAllGamma P (Finset.univ.erase l) (X l))
    -- EXTRA HYPOTHESIS: "general position" — the Clifford point of each four circles is
    -- well defined (the four Γ-circles have exactly one common point); otherwise "the
    -- point given by part (a)" is not determined.
    (hXu : ∀ l Y, OnAllGamma P (Finset.univ.erase l) Y → Y = X l)
    -- EXTRA HYPOTHESIS: the five points are not collinear ("one circle", not a line).
    -- AMBIGUOUS: drop `hnc` and conclude `Cospherical (range X) ∨ Collinear ℝ (range X)`
    -- ("circle or line", the inversive form).
    (hnc : ¬ Collinear ℝ (Set.range X)) : Prop := 
    Cospherical (Set.range X)


/-- D1(c), Clifford n = 6: for each `m`, the five Clifford points `X m l` (`l ≠ m`) of the
five circles other than `m` lie on a circle `C m` (part (b)); these six circles have a
common point. `X m l` is the Clifford point of the four circles other than `m, l`. -/
def classical_D1_c (c : Fin 6 → Sphere Pt) (M : Pt) (P : Fin 6 → Fin 6 → Pt)
    (h : CliffordGP 6 c M P) (X : Fin 6 → Fin 6 → Pt)
    (hX : ∀ m l, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) (X m l))
    -- EXTRA HYPOTHESIS: general position — each Clifford point is well defined.
    (hXu : ∀ m l Y, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) Y → Y = X m l)
    (C : Fin 6 → Sphere Pt)
    (hC : ∀ m l, m ≠ l → X m l ∈ C m)
    -- EXTRA HYPOTHESIS: general position — the five points on `C m` are not collinear, so
    -- `C m` is the unique circle through them (this is the hypothesis under which part (b)
    -- produces a circle).
    (hCnc : ∀ m, ¬ Collinear ℝ {p : Pt | ∃ l, l ≠ m ∧ p = X m l}) : Prop := 
    ∃ Y : Pt, ∀ m, Y ∈ C m


/-- OWN DEFINITION. Data of Clifford's chain for `n` circles `c i` through `M`, levels
indexed by subsets `S` of the circles: `circ S` (for `|S|` odd) is the circle and `pt S`
(for `|S|` even) the point attached to `S`.
* level 1: `circ {i} = c i`;
* level 2: `pt {i,j}` is the second intersection of `c i, c j` (≠ `M`);
* odd level `|S| = 2k+1 ≥ 3`: `circ S` passes through the `|S|` points `pt (S \ {i})`,
  which are not collinear (general position), so `circ S` is uniquely determined;
* even level `|S| = 2k ≥ 4`: `pt S` lies on the `|S|` circles `circ (S \ {i})` and is their
  unique common point (general position).
All levels strictly below `n` are part of the data/hypotheses (they are the lower
instances of the chain); the theorems below assert the top level `n`. -/
structure CliffordChain (n : ℕ) (c : Fin n → Sphere Pt) (M : Pt)
    (pt : Finset (Fin n) → Pt) (circ : Finset (Fin n) → Sphere Pt) : Prop where
  radius_pos : ∀ i, 0 < (c i).radius
  through_M : ∀ i, M ∈ c i
  distinct : Function.Injective c
  level_one : ∀ i, circ {i} = c i
  level_two : ∀ S : Finset (Fin n), S.card = 2 →
    pt S ≠ M ∧ ∀ i ∈ S, pt S ∈ circ (S.erase i)
  odd_mem : ∀ S : Finset (Fin n), Odd S.card → 3 ≤ S.card → S.card < n →
    ∀ i ∈ S, pt (S.erase i) ∈ circ S
  odd_gp : ∀ S : Finset (Fin n), Odd S.card → 3 ≤ S.card → S.card < n →
    ¬ Collinear ℝ ((fun i => pt (S.erase i)) '' (S : Set (Fin n)))
  even_mem : ∀ S : Finset (Fin n), Even S.card → 4 ≤ S.card → S.card < n →
    ∀ i ∈ S, pt S ∈ circ (S.erase i)
  even_gp : ∀ S : Finset (Fin n), Even S.card → 4 ≤ S.card → S.card < n →
    ∀ Y : Pt, (∀ i ∈ S, Y ∈ circ (S.erase i)) → Y = pt S

/-- D1(d), Clifford's chain, even step (all even `n ≥ 4`): the `n` circles of level
`n - 1` pass through one common point.
(The case `n = 2` is the general-position hypothesis `level_two` itself.) -/
def classical_D1_d_even (n : ℕ) (hn : 4 ≤ n) (he : Even n)
    (c : Fin n → Sphere Pt) (M : Pt)
    (pt : Finset (Fin n) → Pt) (circ : Finset (Fin n) → Sphere Pt)
    (h : CliffordChain n c M pt circ) : Prop := 
    ∃ Y : Pt, ∀ i, Y ∈ circ (Finset.univ.erase i)


/-- D1(d), Clifford's chain, odd step (all odd `n ≥ 3`): the `n` points of level `n - 1`
lie on one circle. -/
def classical_D1_d_odd (n : ℕ) (hn : 3 ≤ n) (ho : Odd n)
    (c : Fin n → Sphere Pt) (M : Pt)
    (pt : Finset (Fin n) → Pt) (circ : Finset (Fin n) → Sphere Pt)
    (h : CliffordChain n c M pt circ)
    -- EXTRA HYPOTHESIS: the top-level points are not collinear ("one circle"). For `n = 3`
    -- this is exactly the non-collinearity hypothesis of (a).
    -- AMBIGUOUS: drop it and conclude `Cospherical … ∨ Collinear ℝ …` (circle or line).
    (hnc : ¬ Collinear ℝ (Set.range fun i => pt (Finset.univ.erase i))) : Prop := 
    Cospherical (Set.range fun i => pt (Finset.univ.erase i))


/-! ## D2 — Miquel's pentagram (five circles) theorem -/

/-- D2. Five lines `ℓ 0, …, ℓ 4` in general position (no two parallel, no three
concurrent), labelled in the cyclic order of the sides of the inner pentagon: its vertices
are `V i = ℓ i ∩ ℓ (i+1)`, the star points are `T i = ℓ (i-1) ∩ ℓ (i+1)`, and the outer
triangle `i` (bounded by `ℓ (i-1), ℓ i, ℓ (i+1)`) has vertices `V (i-1), V i, T i` and
circumcircle `ω i`.
AMBIGUOUS: the labelling is only required to be cyclic as above; we do not additionally
require the inner pentagon to be convex / the figure to be a "star" (alternative: add a
hypothesis that the `V i` form a convex pentagon with the `T i` outside it).
Consecutive circles `ω i, ω (i+1)` meet in the inner vertex `V i` and in
a second point `Q i`. Then the five points `Q i` lie on one circle. -/
def classical_D2 (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k)
    (V T : Fin 5 → Pt)
    (hV : ∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1))
    (hT : ∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1))
    (ω : Fin 5 → Sphere Pt)
    (hω : ∀ i, V (i - 1) ∈ ω i ∧ V i ∈ ω i ∧ T i ∈ ω i)
    (Q : Fin 5 → Pt)
    -- The classical statement presupposes a second point; AMBIGUOUS: if `ω i, ω (i+1)` are
    -- tangent at `V i` one could take `Q i = V i` (here such configurations are excluded by
    -- the requirement `Q i ≠ V i`).
    (hQ : ∀ i, Q i ∈ ω i ∧ Q i ∈ ω (i + 1) ∧ Q i ≠ V i)
    -- EXTRA HYPOTHESIS: the five points are not collinear ("one circle", not a line).
    -- AMBIGUOUS: drop `hnc` and conclude `Cospherical ∨ Collinear` (circle or line).
    (hnc : ¬ Collinear ℝ (Set.range Q)) : Prop := 
    Cospherical (Set.range Q)


/-- D2 obligation (well-formedness only): for five lines in general position the
intersection points `V i`, `T i` exist and the three vertices of each outer triangle are
non-collinear, so the circumcircles `ω i` exist (and are unique). -/
def classical_D2_obligation (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k) : Prop := 
    ∃ V T : Fin 5 → Pt, (∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1)) ∧
      (∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1)) ∧
      ∀ i, ¬ Collinear ℝ ({V (i - 1), V i, T i} : Set Pt)


/-! ## D3 — Lester's theorem -/

/-- OWN DEFINITION. `X` is the apex of the equilateral triangle erected OUTWARDLY on side
`q r` of triangle `p q r` (opposite side of line `q r` from `p`). -/
def IsOuterApex (p q r X : Pt) : Prop :=
  dist q X = dist q r ∧ dist r X = dist q r ∧ (line[ℝ, q, r]).SOppSide p X

/-- OWN DEFINITION. `X` is the apex of the equilateral triangle erected INWARDLY on side
`q r` of triangle `p q r` (same side of line `q r` as `p`). -/
def IsInnerApex (p q r X : Pt) : Prop :=
  dist q X = dist q r ∧ dist r X = dist q r ∧ (line[ℝ, q, r]).SSameSide p X

/-- OWN DEFINITION. First Fermat point (first isogonic centre): common point of the lines
joining each vertex to the apex of the outward equilateral triangle on the opposite side. -/
def IsFirstFermatPoint (a b c F : Pt) : Prop :=
  ∃ A' B' C' : Pt, IsOuterApex a b c A' ∧ IsOuterApex b c a B' ∧ IsOuterApex c a b C' ∧
    F ∈ line[ℝ, a, A'] ∧ F ∈ line[ℝ, b, B'] ∧ F ∈ line[ℝ, c, C']

/-- OWN DEFINITION. Second Fermat point (second isogonic centre): same with the inward
equilateral triangles. -/
def IsSecondFermatPoint (a b c F : Pt) : Prop :=
  ∃ A' B' C' : Pt, IsInnerApex a b c A' ∧ IsInnerApex b c a B' ∧ IsInnerApex c a b C' ∧
    F ∈ line[ℝ, a, A'] ∧ F ∈ line[ℝ, b, B'] ∧ F ∈ line[ℝ, c, C']

/-- D3, Lester's theorem: in a scalene triangle the two Fermat points, the circumcentre and
the nine-point centre are concyclic. -/
def classical_D3 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b)
    (F₁ F₂ : Pt) (hF₁ : IsFirstFermatPoint a b c F₁) (hF₂ : IsSecondFermatPoint a b c F₂) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    Cospherical ({F₁, F₂, t.circumcenter, (t.ninePointCircle).center} : Set Pt)


/-- D3 obligation (well-formedness only): both Fermat points exist (the second one needs
the triangle not to be equilateral; scalene suffices). -/
def classical_D3_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b) : Prop := 
    (∃ F, IsFirstFermatPoint a b c F) ∧ (∃ F, IsSecondFermatPoint a b c F)


/-! ## D4 — Sawayama–Thébault theorem -/

/-- OWN DEFINITION. The circle `ω` (positive radius) is tangent to the line `p q`. -/
def TangentToLine (ω : Sphere Pt) (p q : Pt) : Prop :=
  0 < ω.radius ∧ Metric.infDist ω.center (line[ℝ, p, q] : Set Pt) = ω.radius

/-- OWN DEFINITION. The circle `ω` (positive radius) is internally tangent to the circle `Ω`
(lies inside `Ω` and touches it). -/
def InternallyTangent (ω Ω : Sphere Pt) : Prop :=
  0 < ω.radius ∧ ω.radius < Ω.radius ∧ dist ω.center Ω.center = Ω.radius - ω.radius

/-- D4, Sawayama–Thébault: `D` on side `BC`; `ω₁, ω₂` are tangent to lines `AD`, `BC`,
internally tangent to the circumcircle, one on each side of `AD`. Then their centres and
the incentre are collinear. -/
def classical_D4 (a b c d : Pt) (h : AffineIndependent ℝ ![a, b, c])
    -- AMBIGUOUS: "on side BC" taken as strictly between `B` and `C` (`Wbtw` would allow
    -- `D = B` or `D = C`, where one of the two circles degenerates).
    (hd : Sbtw ℝ b d c)
    (ω₁ ω₂ : Sphere Pt) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    TangentToLine ω₁ a d → TangentToLine ω₁ b c → InternallyTangent ω₁ t.circumsphere →
    TangentToLine ω₂ a d → TangentToLine ω₂ b c → InternallyTangent ω₂ t.circumsphere →
    (line[ℝ, a, d]).SOppSide ω₁.center ω₂.center →
    -- EXTRA HYPOTHESIS / AMBIGUOUS: the two circles lie on the same side of `BC` as `A`
    -- (inside the angles `ADB` and `ADC`). Without it, each side of `AD` also carries a
    -- circle in the circular segment cut off by `BC`, for which the statement is not the
    -- classical one.
    (line[ℝ, b, c]).SSameSide ω₁.center a → (line[ℝ, b, c]).SSameSide ω₂.center a →
    Collinear ℝ ({ω₁.center, ω₂.center, t.incenter} : Set Pt)


/-- D4 obligation (well-formedness only): the two Thébault circles exist. -/
def classical_D4_obligation (a b c d : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hd : Sbtw ℝ b d c) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    ∃ ω₁ ω₂ : Sphere Pt,
      TangentToLine ω₁ a d ∧ TangentToLine ω₁ b c ∧ InternallyTangent ω₁ t.circumsphere ∧
      TangentToLine ω₂ a d ∧ TangentToLine ω₂ b c ∧ InternallyTangent ω₂ t.circumsphere ∧
      (line[ℝ, a, d]).SOppSide ω₁.center ω₂.center ∧
      (line[ℝ, b, c]).SSameSide ω₁.center a ∧ (line[ℝ, b, c]).SSameSide ω₂.center a


/-! ## D5 — Kosnita's theorem -/

/-- OWN DEFINITION. `o` is equidistant from `p, q, r`, i.e. (for `p, q, r` not collinear) the
circumcentre of triangle `p q r`. -/
def IsCircumcenterOf (o p q r : Pt) : Prop :=
  dist o p = dist o q ∧ dist o p = dist o r

/-- D5, Kosnita: with `O` the circumcentre and `O_a, O_b, O_c` the circumcentres of `OBC`,
`OCA`, `OAB`, the lines `AO_a, BO_b, CO_c` are concurrent.
(If `O` lies on a side — right triangle — the corresponding `O_x` does not exist and the
statement is vacuous; see the obligation.) -/
def classical_D5 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) (Oa Ob Oc : Pt) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    IsCircumcenterOf Oa t.circumcenter b c → IsCircumcenterOf Ob t.circumcenter c a →
    IsCircumcenterOf Oc t.circumcenter a b →
    -- EXTRA HYPOTHESIS: the three lines are defined (`A ≠ O_a` etc.; `A = O_a` happens e.g.
    -- for an isosceles triangle with apex angle 120° at `A`).
    a ≠ Oa → b ≠ Ob → c ≠ Oc →
    -- AMBIGUOUS: concurrency "at infinity" allowed — the Kosnita point (isogonal conjugate
    -- of the nine-point centre) is at infinity when the nine-point centre lies on the
    -- circumcircle; then the three lines are parallel. Strict alternative: add the
    -- hypothesis that the lines are not all parallel and keep only the first disjunct.
    (∃ X : Pt, X ∈ line[ℝ, a, Oa] ∧ X ∈ line[ℝ, b, Ob] ∧ X ∈ line[ℝ, c, Oc]) ∨
      ((line[ℝ, a, Oa]).Parallel (line[ℝ, b, Ob]) ∧
        (line[ℝ, b, Ob]).Parallel (line[ℝ, c, Oc]))


/-- D5 obligation (well-formedness only): if the circumcentre is not on line `BC`, the
circumcentre of `OBC` exists. -/
def classical_D5_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    ¬ Collinear ℝ ({t.circumcenter, b, c} : Set Pt) →
      ∃ Oa, IsCircumcenterOf Oa t.circumcenter b c


/-! ## D6 — Blundon's fundamental inequality -/

/-- D6, Blundon, lower bound. -/
def classical_D6_lower (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    let R := t.circumradius
    let r := t.inradius
    let s := (dist a b + dist b c + dist c a) / 2
    2 * R ^ 2 + 10 * R * r - r ^ 2 - 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r) ≤ s ^ 2


/-- D6, Blundon, upper bound. -/
def classical_D6_upper (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    let R := t.circumradius
    let r := t.inradius
    let s := (dist a b + dist b c + dist c a) / 2
    s ^ 2 ≤ 2 * R ^ 2 + 10 * R * r - r ^ 2 + 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r)


/-- D6 obligation (well-formedness only): the radicand is non-negative (Euler `R ≥ 2r`),
so `Real.sqrt` is the genuine square root rather than its junk value `0`. -/
def classical_D6_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    0 ≤ t.circumradius ^ 2 - 2 * t.circumradius * t.inradius


/-! ## D7 — Steiner–Lehmus theorem -/

/-- OWN DEFINITION. `e` is the foot of the internal bisector from vertex `v` of the angle
`p v q`: `e` lies on segment `p q` and bisects the angle at `v`. -/
def IsBisectorFoot (v p q e : Pt) : Prop :=
  Wbtw ℝ p e q ∧ ∠ p v e = ∠ e v q

/-- D7, Steiner–Lehmus: if the internal bisectors from `B` and `C` (vertex to opposite side)
have equal length, then `AB = AC`. -/
def classical_D7 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) (e f : Pt)
    (he : IsBisectorFoot b a c e) (hf : IsBisectorFoot c a b f)
    (hlen : dist b e = dist c f) : Prop := 
    dist a b = dist a c


/-- D7 obligation (well-formedness only): the bisector foot exists. -/
def classical_D7_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    ∃ e, IsBisectorFoot b a c e


end Lester.Classical

namespace Lester.Classical

noncomputable def planeIso : ℂ ≃ₗᵢ[ℝ] Pt := Complex.orthonormalBasisOneI.repr
noncomputable def complexIso : Pt ≃ₗᵢ[ℝ] ℂ := planeIso.symm

 theorem cov_cospherical_transport {s : Set Pt} :
    Cospherical (complexIso '' s) ↔ Cospherical s := by
  constructor
  · rintro ⟨o, r, hr⟩
    refine ⟨complexIso.symm o, r, fun p hp => ?_⟩
    have hh := hr (complexIso p) ⟨p, hp, rfl⟩
    rw [← complexIso.apply_symm_apply o, complexIso.dist_map] at hh
    exact hh
  · rintro ⟨o, r, hr⟩
    refine ⟨complexIso o, r, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    rw [complexIso.dist_map]
    exact hr p hp

 theorem cov_collinear_transport {s : Set Pt} :
    Collinear ℝ (complexIso '' s) ↔ Collinear ℝ s := by
  rw [collinear_iff_exists_forall_eq_smul_vadd, collinear_iff_exists_forall_eq_smul_vadd]
  constructor
  · rintro ⟨o, v, h⟩
    refine ⟨complexIso.symm o, complexIso.symm v, fun p hp => ?_⟩
    obtain ⟨r, hr⟩ := h (complexIso p) ⟨p, hp, rfl⟩
    refine ⟨r, ?_⟩
    have hh := congrArg complexIso.symm hr
    simpa only [vadd_eq_add, map_add, map_smul, LinearIsometryEquiv.symm_apply_apply] using hh
  · rintro ⟨o, v, h⟩
    refine ⟨complexIso o, complexIso v, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨r, rfl⟩ := h p hp
    exact ⟨r, by simp [vadd_eq_add]⟩

noncomputable def planeAffine : Pt →ᵃⁱ[ℝ] ℂ := complexIso.toLinearIsometry.toAffineIsometry

theorem cov_D3_part (a b c : Pt) (h : AffineIndependent ℝ ![a,b,c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b)
    (F₁ F₂ : Pt) (hF₁ : IsFirstFermatPoint a b c F₁) (hF₂ : IsSecondFermatPoint a b c F₂)
    (ho : Lester.IsFermatOuter (complexIso a) (complexIso b) (complexIso c) (complexIso F₁))
    (hi : Lester.IsFermatInner (complexIso a) (complexIso b) (complexIso c) (complexIso F₂)) :
    let t : Affine.Triangle ℝ Pt := ⟨![a,b,c],h⟩
    Cospherical ({F₁,F₂,t.circumcenter,t.ninePointCircle.center} : Set Pt) := by
  let t : Affine.Triangle ℝ Pt := ⟨![a,b,c],h⟩
  let u := t.map planeAffine.toAffineMap planeAffine.injective
  have e0 : u.points 0 = complexIso a := rfl
  have e1 : u.points 1 = complexIso b := rfl
  have e2 : u.points 2 = complexIso c := rfl
  have hc1 : u.circumcenter = complexIso t.circumcenter := t.circumcenter_map planeAffine
  have hc2 : u.ninePointCircle.center = complexIso t.ninePointCircle.center :=
    congrArg Sphere.center (t.ninePointCircle_map planeAffine)
  have hh := Lester.lester u
    (by simpa only [e0,e1,e2,complexIso.dist_map] using hab)
    (by simpa only [e0,e1,e2,complexIso.dist_map] using hbc)
    (by simpa only [e0,e1,e2,complexIso.dist_map] using hca)
    (complexIso F₁) (complexIso F₂) ho hi
  apply cov_cospherical_transport.1
  have hcos := hh.1
  rw [Lester.bridge_ninePointCenter, hc1, hc2] at hcos
  convert hcos using 1
  ext p
  simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto



/-! ## L15 gap 1: the writer's Fermat definitions coincide with Lester's -/

/-- Signed area (copied from the Thébault repository, renamed). -/
def gcross (U V X : Pt) : ℝ := (V 0 - U 0) * (X 1 - U 1) - (V 1 - U 1) * (X 0 - U 0)

theorem gap_lineMap_coord (U V : Pt) (s : ℝ) (i : Fin 2) :
    (AffineMap.lineMap U V s : Pt) i = U i + s * (V i - U i) := by
  rw [AffineMap.lineMap_apply_module']
  simp; ring

theorem gap_pt_ext (X Y : Pt) (h0 : X 0 = Y 0) (h1 : X 1 = Y 1) : X = Y := by
  ext i; fin_cases i <;> simp [h0, h1]

theorem gap_cross_of_mem (U V X : Pt) (hX : X ∈ line[ℝ, U, V]) : gcross U V X = 0 := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hX
  obtain ⟨s, rfl⟩ := hX
  unfold gcross; rw [gap_lineMap_coord, gap_lineMap_coord]; ring

theorem gap_mem_of_cross (U V X : Pt) (h : U ≠ V) (hc : gcross U V X = 0) :
    X ∈ line[ℝ, U, V] := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  have hne : (V 0 - U 0) ≠ 0 ∨ (V 1 - U 1) ≠ 0 := by
    by_contra hh; push Not at hh
    exact h (gap_pt_ext _ _ (by linarith [hh.1]) (by linarith [hh.2])).symm
  have hd : 0 < (V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2 := by
    rcases hne with hh | hh
    · have := sq_pos_of_ne_zero hh; positivity
    · have := sq_pos_of_ne_zero hh; positivity
  set d := (V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2
  set s := ((X 0 - U 0) * (V 0 - U 0) + (X 1 - U 1) * (V 1 - U 1)) / d
  refine ⟨s, ?_⟩
  unfold gcross at hc
  have k0 : s * (V 0 - U 0) = X 0 - U 0 := by
    simp only [s]; rw [div_mul_eq_mul_div, div_eq_iff hd.ne']
    linear_combination (V 1 - U 1) * hc
  have k1 : s * (V 1 - U 1) = X 1 - U 1 := by
    simp only [s]; rw [div_mul_eq_mul_div, div_eq_iff hd.ne']
    linear_combination -(V 0 - U 0) * hc
  apply gap_pt_ext <;> rw [gap_lineMap_coord] <;> linarith

theorem gap_opp_cross_neg (U V X Y : Pt) (huv : U ≠ V)
    (h : (line[ℝ,U,V]).SOppSide X Y) : gcross U V X * gcross U V Y < 0 := by
  obtain ⟨Z,hz,ht⟩ := h.exists_sbtw
  obtain ⟨⟨t,⟨ht0,ht1⟩,he⟩,hZX,hZY⟩ := ht
  have ht0' : t ≠ 0 := by intro hh; rw [hh,AffineMap.lineMap_apply_zero] at he; exact hZX he.symm
  have ht1' : t ≠ 1 := by intro hh; rw [hh,AffineMap.lineMap_apply_one] at he; exact hZY he.symm
  have hec := gap_cross_of_mem U V Z hz
  have hlin : (1-t) * gcross U V X + t * gcross U V Y = 0 := by
    rw [← he] at hec
    dsimp [gcross] at *
    rw [gap_lineMap_coord,gap_lineMap_coord] at hec
    linear_combination hec
  have hx : gcross U V X ≠ 0 := fun hh => h.left_notMem (gap_mem_of_cross U V X huv hh)
  have heq : t * (gcross U V X * gcross U V Y) = -(1-t) * (gcross U V X)^2 := by
    linear_combination (gcross U V X) * hlin
  have htl : t < 1 := lt_of_le_of_ne ht1 ht1'
  have hn : t * (gcross U V X * gcross U V Y) < 0 := by
    rw [heq]
    exact mul_neg_of_neg_of_pos (by linarith) (sq_pos_of_ne_zero hx)
  exact neg_of_mul_neg_right hn ht0

theorem gap_same_cross_pos (U V X Y : Pt) (hUV : U ≠ V)
    (h : (line[ℝ, U, V]).SSameSide X Y) : 0 < gcross U V X * gcross U V Y := by
  have hU : U ∈ line[ℝ, U, V] := left_mem_affineSpan_pair ℝ U V
  rw [AffineSubspace.sSameSide_iff_exists_left hU] at h
  obtain ⟨hX, hY, Z, hZ, hr⟩ := h
  have hXc : gcross U V X ≠ 0 := fun hc => hX (gap_mem_of_cross U V X hUV hc)
  have hYc : gcross U V Y ≠ 0 := fun hc => hY (gap_mem_of_cross U V Y hUV hc)
  have hx : X -ᵥ U ≠ 0 := by
    intro h0; rw [vsub_eq_zero_iff_eq] at h0; exact hX (h0 ▸ hU)
  have hy : Y -ᵥ Z ≠ 0 := by
    intro h0; rw [vsub_eq_zero_iff_eq] at h0; exact hY (h0 ▸ hZ)
  obtain ⟨r₁, r₂, h1, h2, he⟩ := hr.exists_pos hx hy
  have e0 := congrArg (fun v : Pt => v 0) he
  have e1 := congrArg (fun v : Pt => v 1) he
  simp only [PiLp.smul_apply, vsub_eq_sub, PiLp.sub_apply, smul_eq_mul] at e0 e1
  have hz := gap_cross_of_mem U V Z hZ
  have key : r₁ * gcross U V X = r₂ * gcross U V Y := by
    unfold gcross at *
    linear_combination (V 0 - U 0) * e1 - (V 1 - U 1) * e0 - r₂ * hz
  have hpos : 0 < (r₁ * gcross U V X) * (r₂ * gcross U V Y) := by
    rw [key]; exact mul_self_pos.2 (mul_ne_zero h2.ne' hYc)
  have : (r₁ * gcross U V X) * (r₂ * gcross U V Y) =
      (r₁ * r₂) * (gcross U V X * gcross U V Y) := by ring
  rw [this] at hpos
  exact pos_of_mul_pos_right hpos (by positivity)

theorem gap_iso_re (x : Pt) : (complexIso x).re = x 0 := by
  simp [complexIso, planeIso]

theorem gap_iso_im (x : Pt) : (complexIso x).im = x 1 := by
  simp [complexIso, planeIso]

/-- Lester's orientation predicate is the sign of the signed area of the writer's points. -/
theorem gap_ccw_iff (a b c : Pt) :
    Lester.Ccw (complexIso a) (complexIso b) (complexIso c) ↔ 0 < gcross b c a := by
  unfold Lester.Ccw gcross
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
    gap_iso_re, gap_iso_im]
  constructor <;> intro hh <;> linarith

theorem gap_apex_alg (u0 u1 y0 y1 : ℝ) (hD : 0 < u0 ^ 2 + u1 ^ 2)
    (hdot : u0 * y0 + u1 * y1 = (u0 ^ 2 + u1 ^ 2) / 2)
    (hyy : y0 ^ 2 + y1 ^ 2 = u0 ^ 2 + u1 ^ 2) :
    (0 < u0 * y1 - u1 * y0 →
      y0 = u0 / 2 - u1 * (Real.sqrt 3 / 2) ∧ y1 = u1 / 2 + u0 * (Real.sqrt 3 / 2)) ∧
    (u0 * y1 - u1 * y0 < 0 →
      y0 = u0 / 2 - u1 * (-(Real.sqrt 3 / 2)) ∧ y1 = u1 / 2 + u0 * (-(Real.sqrt 3 / 2))) := by
  have h3 : (u0 * y1 - u1 * y0) ^ 2 = 3 / 4 * (u0 ^ 2 + u1 ^ 2) ^ 2 := by
    have : (u0 * y1 - u1 * y0) ^ 2 + (u0 * y0 + u1 * y1) ^ 2 =
      (u0 ^ 2 + u1 ^ 2) * (y0 ^ 2 + y1 ^ 2) := by ring
    rw [hdot, hyy] at this; linarith
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s3p : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hpm : (u0 * y1 - u1 * y0 - Real.sqrt 3 / 2 * (u0 ^ 2 + u1 ^ 2)) *
      (u0 * y1 - u1 * y0 + Real.sqrt 3 / 2 * (u0 ^ 2 + u1 ^ 2)) = 0 := by
    linear_combination h3 - (u0 ^ 2 + u1 ^ 2) ^ 2 / 4 * s3
  have hq : 0 < Real.sqrt 3 / 2 * (u0 ^ 2 + u1 ^ 2) := by positivity
  have solve : ∀ k : ℝ, u0 * y1 - u1 * y0 = k * (u0 ^ 2 + u1 ^ 2) →
      y0 = u0 / 2 - u1 * k ∧ y1 = u1 / 2 + u0 * k := by
    intro k hk
    constructor
    · apply mul_left_cancel₀ hD.ne'
      linear_combination u0 * hdot - u1 * hk
    · apply mul_left_cancel₀ hD.ne'
      linear_combination u1 * hdot + u0 * hk
  refine ⟨fun hpos => solve _ ?_, fun hneg => solve _ ?_⟩
  · rcases mul_eq_zero.1 hpm with hh | hh
    · linarith
    · linarith
  · rcases mul_eq_zero.1 hpm with hh | hh
    · linarith
    · linarith

/-- Complex characterisation of the two equilateral apices on `BC`. -/
theorem gap_apex_char (b c x : Pt) (hbc : b ≠ c) (h1 : dist b x = dist b c)
    (h2 : dist c x = dist b c) :
    (0 < gcross b c x → complexIso x = complexIso b + (complexIso c - complexIso b) * Lester.ω) ∧
    (gcross b c x < 0 → complexIso x =
      complexIso b + (complexIso c - complexIso b) * (starRingEnd ℂ) Lester.ω) := by
  have hd : ∀ p q : Pt, dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
    intro p q
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two,
      Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
  have q1 := hd b x; have q2 := hd c x; have q3 := hd b c
  rw [h1] at q1; rw [h2] at q2
  have hD : 0 < (c 0 - b 0) ^ 2 + (c 1 - b 1) ^ 2 := by
    have := pow_pos (dist_pos.2 hbc) 2; linarith
  have hdot : (c 0 - b 0) * (x 0 - b 0) + (c 1 - b 1) * (x 1 - b 1) =
      ((c 0 - b 0) ^ 2 + (c 1 - b 1) ^ 2) / 2 := by
    linear_combination (q2 - q1) / 2
  have hyy : (x 0 - b 0) ^ 2 + (x 1 - b 1) ^ 2 = (c 0 - b 0) ^ 2 + (c 1 - b 1) ^ 2 := by
    linear_combination q3 - q1
  obtain ⟨hA, hB⟩ := gap_apex_alg _ _ _ _ hD hdot hyy
  have hcr : gcross b c x = (c 0 - b 0) * (x 1 - b 1) - (c 1 - b 1) * (x 0 - b 0) := rfl
  refine ⟨fun hpos => ?_, fun hneg => ?_⟩
  · rw [hcr] at hpos
    obtain ⟨e0, e1⟩ := hA hpos
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im, gap_iso_re,
        gap_iso_im, Lester.ω]
      linear_combination e0
    · simp only [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im, gap_iso_re,
        gap_iso_im, Lester.ω]
      linear_combination e1
  · rw [hcr] at hneg
    obtain ⟨e0, e1⟩ := hB hneg
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im, gap_iso_re,
        gap_iso_im, Lester.ω, Complex.conj_re, Complex.conj_im]
      linear_combination e0
    · simp only [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im, gap_iso_re,
        gap_iso_im, Lester.ω, Complex.conj_re, Complex.conj_im]
      linear_combination e1

theorem gap_ne_of_apex (q r X : Pt) (h1 : dist q X = dist q r)
    (hs : X ∉ line[ℝ, q, r]) : q ≠ r := by
  rintro rfl
  rw [dist_self, dist_eq_zero] at h1
  exact hs (h1 ▸ left_mem_affineSpan_pair ℝ q q)

/-- The writer's outward apex is Lester's `apexOut`. -/
theorem gap_outer_apex (p q r X : Pt) (h : IsOuterApex p q r X) :
    complexIso X = Lester.apexOut (complexIso p) (complexIso q) (complexIso r) := by
  obtain ⟨h1, h2, hs⟩ := h
  have hqr := gap_ne_of_apex q r X h1 hs.right_notMem
  have hn := gap_opp_cross_neg q r p X hqr hs
  have hp0 : gcross q r p ≠ 0 := fun hh => hs.left_notMem (gap_mem_of_cross q r p hqr hh)
  obtain ⟨hA, hB⟩ := gap_apex_char q r X hqr h1 h2
  unfold Lester.apexOut
  split_ifs with hc
  · rw [gap_ccw_iff] at hc
    exact hB (by nlinarith)
  · rw [gap_ccw_iff] at hc
    have : gcross q r p < 0 := lt_of_le_of_ne (not_lt.1 hc) hp0
    exact hA (by nlinarith)

/-- The writer's inward apex is Lester's `apexIn`. -/
theorem gap_inner_apex (p q r X : Pt) (h : IsInnerApex p q r X) :
    complexIso X = Lester.apexIn (complexIso p) (complexIso q) (complexIso r) := by
  obtain ⟨h1, h2, hs⟩ := h
  have hqr := gap_ne_of_apex q r X h1 hs.2.2
  have hn := gap_same_cross_pos q r p X hqr hs
  have hp0 : gcross q r p ≠ 0 := fun hh => hs.2.1 (gap_mem_of_cross q r p hqr hh)
  obtain ⟨hA, hB⟩ := gap_apex_char q r X hqr h1 h2
  unfold Lester.apexIn
  split_ifs with hc
  · rw [gap_ccw_iff] at hc
    exact hA (by nlinarith)
  · rw [gap_ccw_iff] at hc
    have : gcross q r p < 0 := lt_of_le_of_ne (not_lt.1 hc) hp0
    exact hB (by nlinarith)

theorem gap_mem_line_map (p q x : Pt) (h : x ∈ line[ℝ, p, q]) :
    complexIso x ∈ line[ℝ, complexIso p, complexIso q] := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at h ⊢
  obtain ⟨s, rfl⟩ := h
  refine ⟨s, ?_⟩
  simp only [AffineMap.lineMap_apply_module, map_add, map_smul]

theorem gap_fermat_outer (a b c F : Pt) (h : IsFirstFermatPoint a b c F) :
    Lester.IsFermatOuter (complexIso a) (complexIso b) (complexIso c) (complexIso F) := by
  obtain ⟨A', B', C', hA, hB, hC, h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← gap_outer_apex _ _ _ _ hA]; exact gap_mem_line_map _ _ _ h1
  · rw [← gap_outer_apex _ _ _ _ hB]; exact gap_mem_line_map _ _ _ h2
  · rw [← gap_outer_apex _ _ _ _ hC]; exact gap_mem_line_map _ _ _ h3

theorem gap_fermat_inner (a b c F : Pt) (h : IsSecondFermatPoint a b c F) :
    Lester.IsFermatInner (complexIso a) (complexIso b) (complexIso c) (complexIso F) := by
  obtain ⟨A', B', C', hA, hB, hC, h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← gap_inner_apex _ _ _ _ hA]; exact gap_mem_line_map _ _ _ h1
  · rw [← gap_inner_apex _ _ _ _ hB]; exact gap_mem_line_map _ _ _ h2
  · rw [← gap_inner_apex _ _ _ _ hC]; exact gap_mem_line_map _ _ _ h3

/-- **D3, exact writer statement.** -/
theorem cov_D3 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b)
    (F₁ F₂ : Pt) (hF₁ : IsFirstFermatPoint a b c F₁) (hF₂ : IsSecondFermatPoint a b c F₂) :
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    Cospherical ({F₁, F₂, t.circumcenter, (t.ninePointCircle).center} : Set Pt) :=
  cov_D3_part a b c h hab hbc hca F₁ F₂ hF₁ hF₂ (gap_fermat_outer a b c F₁ hF₁)
    (gap_fermat_inner a b c F₂ hF₂)

theorem cov_D3_exact (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b)
    (F₁ F₂ : Pt) (hF₁ : IsFirstFermatPoint a b c F₁) (hF₂ : IsSecondFermatPoint a b c F₂) :
    classical_D3 a b c h hab hbc hca F₁ F₂ hF₁ hF₂ :=
  cov_D3 a b c h hab hbc hca F₁ F₂ hF₁ hF₂


/-! ## L15 gap 4 (D3 part): existence of both Fermat points -/

def mk2 (x y : ℝ) : Pt := !₂[x, y]

@[simp] theorem gap_mk2_0 (x y : ℝ) : mk2 x y 0 = x := by simp [mk2]
@[simp] theorem gap_mk2_1 (x y : ℝ) : mk2 x y 1 = y := by simp [mk2]

theorem gap_dist_sq (X Y : Pt) : dist X Y ^ 2 = (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two,
    Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

/-- Apex of the equilateral triangle on `q r` obtained by rotating `r - q` by `±60°`
(`K = ±√3`). -/
noncomputable def apx (q r : Pt) (K : ℝ) : Pt :=
  mk2 (q 0 + (r 0 - q 0) / 2 - K / 2 * (r 1 - q 1)) (q 1 + (r 1 - q 1) / 2 + K / 2 * (r 0 - q 0))

theorem gap_apx_dist (q r : Pt) (K : ℝ) (hK : K ^ 2 = 3) :
    dist q (apx q r K) = dist q r ∧ dist r (apx q r K) = dist q r := by
  have e : ∀ x y : Pt, dist x y ^ 2 = dist q r ^ 2 → dist x y = dist q r := fun x y h =>
    (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 h
  constructor <;> apply e <;> rw [gap_dist_sq, gap_dist_sq] <;> simp only [apx, gap_mk2_0, gap_mk2_1] <;>
    linear_combination ((r 0 - q 0) ^ 2 / 4 + (r 1 - q 1) ^ 2 / 4) * hK

theorem gap_apx_cross (q r : Pt) (K : ℝ) :
    gcross q r (apx q r K) = K / 2 * ((r 0 - q 0) ^ 2 + (r 1 - q 1) ^ 2) := by
  simp only [gcross, apx, gap_mk2_0, gap_mk2_1]; ring

theorem gap_opp_of_cross_neg (U V X Y : Pt) (huv : U ≠ V)
    (hp : gcross U V X * gcross U V Y < 0) : (line[ℝ,U,V]).SOppSide X Y := by
  have hx : gcross U V X ≠ 0 := by intro hh; rw [hh,zero_mul] at hp; linarith
  have hy : gcross U V Y ≠ 0 := by intro hh; rw [hh,mul_zero] at hp; linarith
  let r := gcross U V Y / gcross U V X
  let Z := Y - r • (X - U)
  have hr : r < 0 := by
    dsimp [r]
    exact div_neg_iff.2 (by rcases mul_neg_iff.1 hp with h|h <;> tauto)
  have hz : Z ∈ line[ℝ,U,V] := by
    apply gap_mem_of_cross _ _ _ huv
    have he : r * gcross U V X = gcross U V Y := div_mul_cancel₀ _ hx
    dsimp [Z]
    simp only [gcross,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul] at *
    linear_combination -he
  apply AffineSubspace.sOppSide_of_vsub_eq_smul
    (p₁ := U) (p₂ := Z) (m := X-U) (c₁ := (1:ℝ)) (c₂ := r)
    (left_mem_affineSpan_pair ℝ U V) hz
  · simp
  · simp [Z,vsub_eq_sub]
  · linarith
  · intro hh; exact hx (gap_cross_of_mem U V X hh)
  · intro hh; exact hy (gap_cross_of_mem U V Y hh)

theorem gap_same_of_cross_pos (U V X Y : Pt) (huv : U ≠ V)
    (hp : 0 < gcross U V X * gcross U V Y) : (line[ℝ,U,V]).SSameSide X Y := by
  have hx : gcross U V X ≠ 0 := by intro hh; rw [hh,zero_mul] at hp; linarith
  have hy : gcross U V Y ≠ 0 := by intro hh; rw [hh,mul_zero] at hp; linarith
  let r := gcross U V Y / gcross U V X
  let Z := Y - r • (X - U)
  have hr : 0 < r := by
    dsimp [r]
    exact (div_pos_iff).2 (by rcases mul_pos_iff.1 hp with h|h <;> tauto)
  have hz : Z ∈ line[ℝ,U,V] := by
    apply gap_mem_of_cross _ _ _ huv
    have he : r * gcross U V X = gcross U V Y := div_mul_cancel₀ _ hx
    dsimp [Z]
    simp only [gcross,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul] at *
    linear_combination -he
  apply AffineSubspace.sSameSide_of_vsub_eq_smul
    (p₁ := U) (p₂ := Z) (m := X-U) (c₁ := (1:ℝ)) (c₂ := r)
    (left_mem_affineSpan_pair ℝ U V) hz
  · simp
  · simp [Z,vsub_eq_sub]
  · simpa using hr.le
  · intro hh; exact hx (gap_cross_of_mem U V X hh)
  · intro hh; exact hy (gap_cross_of_mem U V Y hh)

theorem gap_ne_sq (q r : Pt) (h : q ≠ r) : 0 < (r 0 - q 0) ^ 2 + (r 1 - q 1) ^ 2 := by
  have := pow_pos (dist_pos.2 h) 2
  rw [gap_dist_sq] at this
  nlinarith [this]

/-- The apex `apx q r K` is outward (resp. inward) iff `K` and the orientation have opposite
(resp. equal) signs. -/
theorem gap_apx_outer (p q r : Pt) (K : ℝ) (hK : K ^ 2 = 3) (hqr : q ≠ r)
    (hs : K * gcross q r p < 0) : IsOuterApex p q r (apx q r K) := by
  obtain ⟨h1, h2⟩ := gap_apx_dist q r K hK
  refine ⟨h1, h2, gap_opp_of_cross_neg q r p _ hqr ?_⟩
  rw [gap_apx_cross]
  have := gap_ne_sq q r hqr
  nlinarith

theorem gap_apx_inner (p q r : Pt) (K : ℝ) (hK : K ^ 2 = 3) (hqr : q ≠ r)
    (hs : 0 < K * gcross q r p) : IsInnerApex p q r (apx q r K) := by
  obtain ⟨h1, h2⟩ := gap_apx_dist q r K hK
  refine ⟨h1, h2, gap_same_of_cross_pos q r p _ hqr ?_⟩
  rw [gap_apx_cross]
  have := gap_ne_sq q r hqr
  nlinarith

/-- The three lines vertex–apex (same rotation `K` on every side) are concurrent, provided the
non-degeneracy `K·S ≠ 3g`. -/
theorem gap_concurrent (a b c : Pt) (K : ℝ) (hK : K ^ 2 = 3)
    (hE : K * (((a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 + ((b 0 - c 0) ^ 2 + (b 1 - c 1) ^ 2) +
      ((c 0 - a 0) ^ 2 + (c 1 - a 1) ^ 2)) / 2) - 3 * gcross b c a ≠ 0) :
    ∃ F, F ∈ line[ℝ, a, apx b c K] ∧ F ∈ line[ℝ, b, apx c a K] ∧ F ∈ line[ℝ, c, apx a b K] := by
  have hD : (apx c a K 0 - b 0) * (apx b c K 1 - a 1) - (apx c a K 1 - b 1) * (apx b c K 0 - a 0) ≠ 0 := by
    intro h0; apply hE
    simp only [apx, gap_mk2_0, gap_mk2_1] at h0
    unfold gcross
    linear_combination 2 * h0 - (-(a 0 * b 1 - a 0 * c 1 - a 1 * b 0 + a 1 * c 0 + b 0 * c 1 - b 1 * c 0) / 2) * hK
  have hD' : (apx a b K 0 - c 0) * (apx c a K 1 - b 1) - (apx a b K 1 - c 1) * (apx c a K 0 - b 0) ≠ 0 := by
    intro h0; apply hE
    simp only [apx, gap_mk2_0, gap_mk2_1] at h0
    unfold gcross
    linear_combination 2 * h0 - (-(a 0 * b 1 - a 0 * c 1 - a 1 * b 0 + a 1 * c 0 + b 0 * c 1 - b 1 * c 0) / 2) * hK
  have hbB : b ≠ apx c a K := by
    intro he; apply hD; rw [← he]; ring
  have hcC : c ≠ apx a b K := by
    intro he; apply hD'; rw [← he]; ring
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t * ((apx c a K 0 - b 0) * (apx b c K 1 - a 1) - (apx c a K 1 - b 1) * (apx b c K 0 - a 0)) =
      (apx c a K 0 - b 0) * (b 1 - a 1) - (apx c a K 1 - b 1) * (b 0 - a 0) :=
    ⟨_, div_mul_cancel₀ _ hD⟩
  refine ⟨AffineMap.lineMap a (apx b c K) t, AffineMap.lineMap_mem_affineSpan_pair _ _ _, ?_, ?_⟩
  · apply gap_mem_of_cross _ _ _ hbB
    unfold gcross
    rw [gap_lineMap_coord, gap_lineMap_coord]
    linear_combination ht
  · apply gap_mem_of_cross _ _ _ hcC
    unfold gcross
    rw [gap_lineMap_coord, gap_lineMap_coord]
    apply mul_left_cancel₀ hD
    simp only [apx, gap_mk2_0, gap_mk2_1] at ht ⊢
    linear_combination (((a 0 + (b 0 - a 0) / 2 - K / 2 * (b 1 - a 1)) - c 0) * ((b 1 + (c 1 - b 1) / 2 + K / 2 * (c 0 - b 0)) - a 1) - ((a 1 + (b 1 - a 1) / 2 + K / 2 * (b 0 - a 0)) - c 1) * ((b 0 + (c 0 - b 0) / 2 - K / 2 * (c 1 - b 1)) - a 0)) * ht

/-- A non-equilateral (here: `dist a b ≠ dist b c`) triangle has `K·S ≠ 3g` for `K = ±√3`. -/
theorem gap_nondeg_alg (p q r g K : ℝ) (hK : K ^ 2 = 3)
    (hg : (p - q) ^ 2 + (q - r) ^ 2 + (r - p) ^ 2 = 2 * (((p + q + r) / 2) ^ 2 - 3 * g ^ 2))
    (h0 : K * ((p + q + r) / 2) - 3 * g = 0) : p = q := by
  have h1 : K * ((p + q + r) / 2) = 3 * g := by linarith
  have h2 : 3 * ((p + q + r) / 2) ^ 2 = 9 * g ^ 2 := by
    have e : (K * ((p + q + r) / 2)) ^ 2 = (3 * g) ^ 2 := by rw [h1]
    nlinarith [e]
  have h3 : (p - q) ^ 2 + (q - r) ^ 2 + (r - p) ^ 2 = 0 := by rw [hg]; linarith
  nlinarith [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (r - p)]

/-- A triangle with `dist a b ≠ dist b c` has `K·S ≠ 3g` for `K = ±√3`. -/
theorem gap_nondeg (a b c : Pt) (K : ℝ) (hK : K ^ 2 = 3) (hab : dist a b ≠ dist b c) :
    K * (((a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 + ((b 0 - c 0) ^ 2 + (b 1 - c 1) ^ 2) +
      ((c 0 - a 0) ^ 2 + (c 1 - a 1) ^ 2)) / 2) - 3 * gcross b c a ≠ 0 := by
  intro h0
  apply hab
  apply (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1
  rw [gap_dist_sq, gap_dist_sq]
  refine gap_nondeg_alg _ _ ((c 0 - a 0) ^ 2 + (c 1 - a 1) ^ 2) (gcross b c a) K hK ?_ h0
  unfold gcross; ring

/-- **D3 obligation, exact writer statement.** -/
theorem cov_D3_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b) :
    (∃ F, IsFirstFermatPoint a b c F) ∧ (∃ F, IsSecondFermatPoint a b c F) := by
  have hnc := affineIndependent_iff_not_collinear_set.1 h
  have hab' : a ≠ b := fun e => hnc (by rw [e]; simp [collinear_pair])
  have hbc' : b ≠ c := fun e => hnc (by rw [e]; simp [collinear_pair])
  have hca' : c ≠ a := fun e => hnc (by rw [e]; simp [collinear_pair, Set.insert_comm])
  set g := gcross b c a with hgdef
  have hg : g ≠ 0 := by
    intro h0
    exact hnc (collinear_insert_of_mem_affineSpan_pair (gap_mem_of_cross b c a hbc' h0))
  have g2 : gcross c a b = g := by simp only [hgdef, gcross]; ring
  have g3 : gcross a b c = g := by simp only [hgdef, gcross]; ring
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s3' : (-Real.sqrt 3) ^ 2 = 3 := by rw [neg_sq, s3]
  have s3p : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsgn : ∃ K : ℝ, K ^ 2 = 3 ∧ K * g < 0 := by
    rcases lt_or_gt_of_ne hg with hn | hp
    · exact ⟨Real.sqrt 3, s3, mul_neg_of_pos_of_neg s3p hn⟩
    · exact ⟨-Real.sqrt 3, s3', by nlinarith⟩
  obtain ⟨K, hK, hKg⟩ := hsgn
  have hK' : (-K) ^ 2 = 3 := by rw [neg_sq, hK]
  have hKg' : 0 < -K * g := by linarith
  constructor
  · obtain ⟨F, h1, h2, h3⟩ := gap_concurrent a b c K hK (gap_nondeg a b c K hK hab)
    exact ⟨F, apx b c K, apx c a K, apx a b K,
      gap_apx_outer a b c K hK hbc' hKg, gap_apx_outer b c a K hK hca' (by rw [g2]; exact hKg),
      gap_apx_outer c a b K hK hab' (by rw [g3]; exact hKg), h1, h2, h3⟩
  · obtain ⟨F, h1, h2, h3⟩ := gap_concurrent a b c (-K) hK' (gap_nondeg a b c (-K) hK' hab)
    exact ⟨F, apx b c (-K), apx c a (-K), apx a b (-K),
      gap_apx_inner a b c (-K) hK' hbc' hKg', gap_apx_inner b c a (-K) hK' hca' (by rw [g2]; exact hKg'),
      gap_apx_inner c a b (-K) hK' hab' (by rw [g3]; exact hKg'), h1, h2, h3⟩

theorem cov_D3_obligation_exact (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b) :
    classical_D3_obligation a b c h hab hbc hca :=
  cov_D3_obligation a b c h hab hbc hca

end Lester.Classical
