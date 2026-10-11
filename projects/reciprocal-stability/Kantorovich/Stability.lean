import Kantorovich

/-!
# Sharp quadratic stability for the two-point weighted product

This file proves the exact best global coefficient for squared Euclidean
distance to the two endpoint maximizers. Mathematical priority is separate
from formal correctness and has not yet been established.
-/

namespace TwoPointKantorovich

noncomputable section

def product (p q x y : ℝ) : ℝ := (p * x + q * y) * (p / x + q / y)

def optimum (p q m M : ℝ) : ℝ := (p + q) ^ 2 + p * q * (M - m) ^ 2 / (m * M)

def distanceSq (m M x y : ℝ) : ℝ :=
  min ((x - m) ^ 2 + (y - M) ^ 2) ((x - M) ^ 2 + (y - m) ^ 2)

theorem distanceSq_nonneg (m M x y : ℝ) : 0 ≤ distanceSq m M x y := by
  exact le_min (add_nonneg (sq_nonneg _) (sq_nonneg _))
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem distanceSq_symm (m M x y : ℝ) : distanceSq m M x y = distanceSq m M y x := by
  unfold distanceSq
  rw [show (y - m) ^ 2 + (x - M) ^ 2 = (x - M) ^ 2 + (y - m) ^ 2 by ring,
      show (y - M) ^ 2 + (x - m) ^ 2 = (x - m) ^ 2 + (y - M) ^ 2 by ring,
      min_comm]

theorem distanceSq_of_le (m M x y : ℝ) (hmM : m ≤ M) (hxy : x ≤ y) :
    distanceSq m M x y = (x - m) ^ 2 + (y - M) ^ 2 := by
  apply min_eq_left
  nlinarith [mul_nonneg (sub_nonneg.mpr hmM) (sub_nonneg.mpr hxy)]

/-- A nonnegative polynomial certificate for the sorted scalar inequality. -/
theorem sorted_certificate (m M x y : ℝ) :
    x * y * ((M - m) ^ 2 - (x - m) ^ 2 - (M - y) ^ 2) - m * M * (y - x) ^ 2 =
      (x - m) * (y - x) ^ 2 * y +
      2 * x * y * (x - m) * (y - x) +
      (M - y) * (y - x) * (2 * x ^ 2 + (2 * x - m) * (y - x)) +
      2 * x * y * (x - m) * (M - y) := by ring

theorem sorted_scalar_bound (m M x y : ℝ)
    (hm : 0 < m) (hx : m ≤ x) (hxy : x ≤ y) (hy : y ≤ M) :
    (x - m) ^ 2 + (M - y) ^ 2 ≤
      (M - m) ^ 2 - m * M * (y - x) ^ 2 / (x * y) := by
  have hx0 : 0 < x := lt_of_lt_of_le hm hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hxa : 0 ≤ x - m := sub_nonneg.mpr hx
  have hyt : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hMb : 0 ≤ M - y := sub_nonneg.mpr hy
  have hxm : 0 ≤ 2 * x - m := by linarith
  have hcertificate := sorted_certificate m M x y
  have hnonneg : 0 ≤
      (x - m) * (y - x) ^ 2 * y +
      2 * x * y * (x - m) * (y - x) +
      (M - y) * (y - x) * (2 * x ^ 2 + (2 * x - m) * (y - x)) +
      2 * x * y * (x - m) * (M - y) := by positivity
  have hpoly : 0 ≤
      x * y * ((M - m) ^ 2 - (x - m) ^ 2 - (M - y) ^ 2) - m * M * (y - x) ^ 2 := by
    linarith
  have hmul : m * M * (y - x) ^ 2 ≤
      ((M - m) ^ 2 - ((x - m) ^ 2 + (M - y) ^ 2)) * (x * y) := by
    nlinarith
  have hdiv := (div_le_iff₀ (mul_pos hx0 hy0)).mpr hmul
  linarith

/-- The sorted scalar bound, expressed using distance to either maximizer. -/
theorem scalar_stability (m M x y : ℝ)
    (hm : 0 < m) (hmM : m ≤ M)
    (hx : m ≤ x ∧ x ≤ M) (hy : m ≤ y ∧ y ≤ M) :
    distanceSq m M x y ≤ (M - m) ^ 2 - m * M * (x - y) ^ 2 / (x * y) := by
  rcases le_total x y with hxy | hyx
  · rw [distanceSq_of_le m M x y hmM hxy]
    have h := sorted_scalar_bound m M x y hm hx.1 hxy hy.2
    rw [show (y - x) ^ 2 = (x - y) ^ 2 by ring,
      show (M - y) ^ 2 = (y - M) ^ 2 by ring] at h
    exact h
  · rw [distanceSq_symm, distanceSq_of_le m M y x hmM hyx]
    have h := sorted_scalar_bound m M y x hm hy.1 hyx hx.2
    simpa [show (M - x) ^ 2 = (x - M) ^ 2 by ring, mul_comm] using h

theorem deficit_identity (p q m M x y : ℝ)
    (hm : 0 < m) (hM : 0 < M) (hx : 0 < x) (hy : 0 < y) :
    optimum p q m M - product p q x y =
      p * q / (m * M) * ((M - m) ^ 2 - m * M * (x - y) ^ 2 / (x * y)) := by
  unfold optimum product
  field_simp [ne_of_gt hm, ne_of_gt hM, ne_of_gt hx, ne_of_gt hy]
  ring

/-- Sharp quadratic stability, valid for all nonnegative fixed weights. -/
theorem sharp_stability (p q m M x y : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hm : 0 < m) (hmM : m ≤ M)
    (hx : m ≤ x ∧ x ≤ M) (hy : m ≤ y ∧ y ≤ M) :
    p * q / (m * M) * distanceSq m M x y ≤ optimum p q m M - product p q x y := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  rw [deficit_identity p q m M x y hm hM
    (lt_of_lt_of_le hm hx.1) (lt_of_lt_of_le hm hy.1)]
  exact mul_le_mul_of_nonneg_left (scalar_stability m M x y hm hmM hx hy)
    (div_nonneg (mul_nonneg hp hq) (le_of_lt (mul_pos hm hM)))

theorem opposite_endpoints_attain (p q m M : ℝ) (hm : 0 < m) (hM : 0 < M) :
    product p q m M = optimum p q m M := by
  unfold product optimum
  field_simp [ne_of_gt hm, ne_of_gt hM]
  ring

/-- The coefficient cannot be increased: the equal lower-endpoint pair
is an equality witness with strictly positive squared distance. -/
theorem coefficient_optimal (p q m M C : ℝ) (hm : 0 < m) (hmM : m < M)
    (hC : ∀ x y : ℝ, (m ≤ x ∧ x ≤ M) → (m ≤ y ∧ y ≤ M) →
      C * distanceSq m M x y ≤ optimum p q m M - product p q x y) :
    C ≤ p * q / (m * M) := by
  have hM : 0 < M := lt_trans hm hmM
  have h := hC m m ⟨le_rfl, le_of_lt hmM⟩ ⟨le_rfl, le_of_lt hmM⟩
  have hd : distanceSq m M m m = (M - m) ^ 2 := by
    unfold distanceSq
    ring_nf
    simp
  rw [hd, deficit_identity p q m M m m hm hM hm hm] at h
  norm_num at h
  by_contra hnot
  have hstrict := mul_lt_mul_of_pos_right (lt_of_not_ge hnot)
    (sq_pos_of_pos (sub_pos.mpr hmM))
  exact (not_lt_of_ge h) hstrict

theorem optimal_coefficient_iff (p q m M C : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hm : 0 < m) (hmM : m < M) :
    (∀ x y : ℝ, (m ≤ x ∧ x ≤ M) → (m ≤ y ∧ y ≤ M) →
      C * distanceSq m M x y ≤ optimum p q m M - product p q x y) ↔
    C ≤ p * q / (m * M) := by
  constructor
  · exact coefficient_optimal p q m M C hm hmM
  · intro hC x y hx hy
    exact (mul_le_mul_of_nonneg_right hC (distanceSq_nonneg m M x y)).trans
      (sharp_stability p q m M x y hp hq hm (le_of_lt hmM) hx hy)

/-- Zero squared distance means precisely one of the two endpoint pairs. -/
theorem distanceSq_eq_zero_iff (m M x y : ℝ) :
    distanceSq m M x y = 0 ↔ (x = m ∧ y = M) ∨ (x = M ∧ y = m) := by
  unfold distanceSq
  constructor
  · intro hz
    by_cases hle : (x - m) ^ 2 + (y - M) ^ 2 ≤ (x - M) ^ 2 + (y - m) ^ 2
    · rw [min_eq_left hle] at hz
      have h1 : (x - m) ^ 2 = 0 := by nlinarith [sq_nonneg (y - M)]
      have h2 : (y - M) ^ 2 = 0 := by nlinarith [sq_nonneg (x - m)]
      exact Or.inl ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp h1), sub_eq_zero.mp (sq_eq_zero_iff.mp h2)⟩
    · rw [min_eq_right (le_of_not_ge hle)] at hz
      have h1 : (x - M) ^ 2 = 0 := by nlinarith [sq_nonneg (y - m)]
      have h2 : (y - m) ^ 2 = 0 := by nlinarith [sq_nonneg (x - M)]
      exact Or.inr ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp h1), sub_eq_zero.mp (sq_eq_zero_iff.mp h2)⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp <;> positivity

/-- For positive weights the maximizing inputs are exactly the opposite
endpoint pairs. No unproved extremizer assertion is used in the metric. -/
theorem product_eq_optimum_iff (p q m M x y : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hm : 0 < m) (hmM : m ≤ M)
    (hx : m ≤ x ∧ x ≤ M) (hy : m ≤ y ∧ y ≤ M) :
    product p q x y = optimum p q m M ↔
      (x = m ∧ y = M) ∨ (x = M ∧ y = m) := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  constructor
  · intro heq
    have h := sharp_stability p q m M x y (le_of_lt hp) (le_of_lt hq) hm hmM hx hy
    rw [heq, sub_self] at h
    have hc : 0 < p * q / (m * M) := div_pos (mul_pos hp hq) (mul_pos hm hM)
    have hd : distanceSq m M x y = 0 := by
      by_contra hnot
      have hdpos := lt_of_le_of_ne (distanceSq_nonneg m M x y) (Ne.symm hnot)
      have hpos := mul_pos hc hdpos
      linarith
    exact (distanceSq_eq_zero_iff m M x y).mp hd
  · rintro (⟨hxm, hyM⟩ | ⟨hxM, hym⟩)
    · rw [hxm, hyM]
      exact opposite_endpoints_attain p q m M hm hM
    · rw [hxM, hym]
      unfold product optimum
      field_simp [ne_of_gt hm, ne_of_gt hM]
      ring

/-- A near-optimal objective supplies an explicit distance certificate. -/
theorem near_optimal_distance (p q m M x y ε : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hm : 0 < m) (hmM : m ≤ M)
    (hx : m ≤ x ∧ x ≤ M) (hy : m ≤ y ∧ y ≤ M)
    (hε : optimum p q m M - product p q x y ≤ ε) :
    distanceSq m M x y ≤ m * M * ε / (p * q) := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have h := (sharp_stability p q m M x y (le_of_lt hp) (le_of_lt hq) hm hmM hx hy).trans hε
  have hscaled := mul_le_mul_of_nonneg_left h (le_of_lt (mul_pos hm hM))
  have hid : m * M * (p * q / (m * M) * distanceSq m M x y) =
      p * q * distanceSq m M x y := by
    field_simp [ne_of_gt hm, ne_of_gt hM]
  rw [hid] at hscaled
  apply (le_div_iff₀ (mul_pos hp hq)).mpr
  nlinarith

#print axioms sorted_scalar_bound
#print axioms scalar_stability
#print axioms sharp_stability
#print axioms coefficient_optimal
#print axioms optimal_coefficient_iff
#print axioms distanceSq_eq_zero_iff
#print axioms product_eq_optimum_iff
#print axioms near_optimal_distance

end

end TwoPointKantorovich
