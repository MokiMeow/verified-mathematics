import Kantorovich.ThreeCertificates

namespace ThreePointKantorovich

open ThreePointKantorovich

noncomputable section

def product (x y z : ℝ) : ℝ := (x + y + z) * (1 / x + 1 / y + 1 / z)

def optimum (m M : ℝ) : ℝ := 9 + 2 * (M - m) ^ 2 / (m * M)

/-- The six squared distances to the endpoint triples with one or two
upper endpoints. The all-equal endpoint triples are excluded. -/
def distanceSq (m M x y z : ℝ) : ℝ :=
  min
    (min ((x - m) ^ 2 + (y - m) ^ 2 + (z - M) ^ 2)
      (min ((x - m) ^ 2 + (y - M) ^ 2 + (z - m) ^ 2)
        ((x - M) ^ 2 + (y - m) ^ 2 + (z - m) ^ 2)))
    (min ((x - m) ^ 2 + (y - M) ^ 2 + (z - M) ^ 2)
      (min ((x - M) ^ 2 + (y - m) ^ 2 + (z - M) ^ 2)
        ((x - M) ^ 2 + (y - M) ^ 2 + (z - m) ^ 2)))

theorem distanceSq_nonneg (m M x y z : ℝ) : 0 ≤ distanceSq m M x y z := by
  unfold distanceSq
  positivity

theorem distanceSq_swap_xy (m M x y z : ℝ) : distanceSq m M x y z = distanceSq m M y x z := by
  unfold distanceSq
  ac_rfl

theorem distanceSq_swap_yz (m M x y z : ℝ) : distanceSq m M x y z = distanceSq m M x z y := by
  unfold distanceSq
  ac_rfl

theorem product_swap_xy (x y z : ℝ) : product x y z = product y x z := by
  unfold product
  ring

theorem product_swap_yz (x y z : ℝ) : product x y z = product x z y := by
  unfold product
  ring

/-- Three nonnegative cones cover the ordered lower-half region. -/
theorem lower_cone_cover (m M x y z : ℝ) (P : ℝ → ℝ → ℝ → ℝ → Prop)
    (hx : m ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ M) (hmid : 2 * y ≤ m + M)
    (h0 : ∀ a t r b : ℝ, 0 ≤ a → 0 ≤ t → 0 ≤ r → 0 ≤ b →
      P (m + 2 * a + 2 * t + r + b) (m + a) (m + a + t) (m + 2 * a + 2 * t + r))
    (h1 : ∀ a v t r : ℝ, 0 ≤ a → 0 ≤ v → 0 ≤ t → 0 ≤ r →
      P (m + 2 * a + 2 * v + 2 * t + r) (m + a) (m + a + v + t) (m + 2 * a + 2 * v + t))
    (h2 : ∀ u a t r : ℝ, 0 ≤ u → 0 ≤ a → 0 ≤ t → 0 ≤ r →
      P (m + 2 * u + 2 * a + 2 * t + r) (m + u + a) (m + u + a + t) (m + 2 * u + a + t)) :
    P M x y z := by
  by_cases hlarge : 2 * y ≤ z + m
  · have h := h0 (x - m) (y - x) (z - 2 * y + m) (M - z)
      (by linarith) (by linarith) (by linarith) (by linarith)
    convert h using 1 <;> ring
  · by_cases hmedium : x - m ≤ z - y
    · have h := h1 (x - m) (z - y - (x - m)) (2 * y - z - m) (M + m - 2 * y)
        (by linarith) (by linarith) (by linarith) (by linarith)
      convert h using 1 <;> ring
    · have h := h2 (z - y) (x - m - (z - y)) (y - x) (M + m - 2 * y)
        (by linarith) (by linarith) (by linarith) (by linarith)
      convert h using 1 <;> ring

theorem lower_numerator_nonneg (m M x y z : ℝ) (hm : 0 < m)
    (hx : m ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ M) (hmid : 2 * y ≤ m + M) :
    0 ≤ ThreePointKantorovich.lowerNumerator m M x y z := by
  apply lower_cone_cover m M x y z (fun M x y z => 0 ≤ ThreePointKantorovich.lowerNumerator m M x y z)
    hx hxy hyz hz hmid
  · intro a t r b ha ht hr hb
    simpa only [add_assoc, add_left_comm, add_comm] using
      ThreePointKantorovich.lower_cone_0 m a t r b (le_of_lt hm) ha ht hr hb
  · intro a v t r ha hv ht hr
    simpa only [add_assoc, add_left_comm, add_comm] using
      ThreePointKantorovich.lower_cone_1 m a v t r (le_of_lt hm) ha hv ht hr
  · intro u a t r hu ha ht hr
    simpa only [add_assoc, add_left_comm, add_comm] using
      ThreePointKantorovich.lower_cone_2 m u a t r (le_of_lt hm) hu ha ht hr

theorem reflected_upper_numerator_nonneg (m M x y z : ℝ) (hm : 0 < m)
    (hx : m ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ M) (hmid : 2 * y ≤ m + M) :
    0 ≤ ThreePointKantorovich.reflectedUpperNumerator m M x y z := by
  apply lower_cone_cover m M x y z (fun M x y z => 0 ≤ ThreePointKantorovich.reflectedUpperNumerator m M x y z)
    hx hxy hyz hz hmid
  · intro a t r b ha ht hr hb
    simpa only [add_assoc, add_left_comm, add_comm] using
      ThreePointKantorovich.reflectedUpper_cone_0 m a t r b (le_of_lt hm) ha ht hr hb
  · intro a v t r ha hv ht hr
    simpa only [add_assoc, add_left_comm, add_comm] using
      ThreePointKantorovich.reflectedUpper_cone_1 m a v t r (le_of_lt hm) ha hv ht hr
  · intro u a t r hu ha ht hr
    simpa only [add_assoc, add_left_comm, add_comm] using
      ThreePointKantorovich.reflectedUpper_cone_2 m u a t r (le_of_lt hm) hu ha ht hr

theorem upper_numerator_nonneg (m M x y z : ℝ) (hm : 0 < m)
    (hx : m ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ M) (hmid : m + M ≤ 2 * y) :
    0 ≤ ThreePointKantorovich.upperNumerator m M x y z := by
  have h := reflected_upper_numerator_nonneg m M (m + M - z) (m + M - y) (m + M - x) hm
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  unfold ThreePointKantorovich.reflectedUpperNumerator at h
  rw [show m + M - (m + M - x) = x by ring,
      show m + M - (m + M - y) = y by ring,
      show m + M - (m + M - z) = z by ring] at h
  exact h

theorem lower_gap_identity (m M x y z : ℝ)
    (hm : 0 < m) (hM : 0 < M) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    optimum m M - product x y z -
      2 / (m * M) * ((x - m) ^ 2 + (y - m) ^ 2 + (M - z) ^ 2) =
    ThreePointKantorovich.lowerNumerator m M x y z / (m * M * x * y * z) := by
  unfold optimum product ThreePointKantorovich.lowerNumerator
  field_simp [ne_of_gt hm, ne_of_gt hM, ne_of_gt hx, ne_of_gt hy, ne_of_gt hz]
  ring

theorem upper_gap_identity (m M x y z : ℝ)
    (hm : 0 < m) (hM : 0 < M) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    optimum m M - product x y z -
      2 / (m * M) * ((x - m) ^ 2 + (y - M) ^ 2 + (M - z) ^ 2) =
    ThreePointKantorovich.upperNumerator m M x y z / (m * M * x * y * z) := by
  unfold optimum product ThreePointKantorovich.upperNumerator
  field_simp [ne_of_gt hm, ne_of_gt hM, ne_of_gt hx, ne_of_gt hy, ne_of_gt hz]
  ring

theorem sorted_stability (m M x y z : ℝ) (hm : 0 < m)
    (hx : m ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ M) :
    2 / (m * M) * distanceSq m M x y z ≤ optimum m M - product x y z := by
  have hx0 : 0 < x := lt_of_lt_of_le hm hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hz0 : 0 < z := lt_of_lt_of_le hy0 hyz
  have hM : 0 < M := lt_of_lt_of_le hz0 hz
  have hc : 0 ≤ 2 / (m * M) := by positivity
  by_cases hmid : 2 * y ≤ m + M
  · have hnum := lower_numerator_nonneg m M x y z hm hx hxy hyz hz hmid
    have hgap := div_nonneg hnum (show 0 ≤ m * M * x * y * z by positivity)
    rw [← lower_gap_identity m M x y z hm hM hx0 hy0 hz0] at hgap
    have hd : distanceSq m M x y z ≤ (x - m) ^ 2 + (y - m) ^ 2 + (M - z) ^ 2 := by
      unfold distanceSq
      exact (min_le_left _ _).trans (by simp [show (z - M) ^ 2 = (M - z) ^ 2 by ring])
    have hscaled := mul_le_mul_of_nonneg_left hd hc
    linarith
  · have hnum := upper_numerator_nonneg m M x y z hm hx hxy hyz hz (le_of_not_ge hmid)
    have hgap := div_nonneg hnum (show 0 ≤ m * M * x * y * z by positivity)
    rw [← upper_gap_identity m M x y z hm hM hx0 hy0 hz0] at hgap
    have hd : distanceSq m M x y z ≤ (x - m) ^ 2 + (y - M) ^ 2 + (M - z) ^ 2 := by
      unfold distanceSq
      exact (min_le_right _ _).trans (by simp [show (z - M) ^ 2 = (M - z) ^ 2 by ring])
    have hscaled := mul_le_mul_of_nonneg_left hd hc
    linarith

/-- Sharp three-point stability for arbitrary, unsorted positive inputs. -/
theorem sharp_stability (m M x y z : ℝ) (hm : 0 < m)
    (hx : m ≤ x ∧ x ≤ M) (hy : m ≤ y ∧ y ≤ M) (hz : m ≤ z ∧ z ≤ M) :
    2 / (m * M) * distanceSq m M x y z ≤ optimum m M - product x y z := by
  by_cases hxy : x ≤ y
  · by_cases hyz : y ≤ z
    · exact sorted_stability m M x y z hm hx.1 hxy hyz hz.2
    · by_cases hxz : x ≤ z
      · have h := sorted_stability m M x z y hm hx.1 hxz (le_of_not_ge hyz) hy.2
        convert h using 1 <;> simp only [distanceSq, product] <;> ac_rfl
      · have h := sorted_stability m M z x y hm hz.1 (le_of_not_ge hxz) hxy hy.2
        convert h using 1 <;> simp only [distanceSq, product] <;> ac_rfl
  · by_cases hxz : x ≤ z
    · have h := sorted_stability m M y x z hm hy.1 (le_of_not_ge hxy) hxz hz.2
      convert h using 1 <;> simp only [distanceSq, product] <;> ac_rfl
    · by_cases hyz : y ≤ z
      · have h := sorted_stability m M y z x hm hy.1 hyz (le_of_not_ge hxz) hx.2
        convert h using 1 <;> simp only [distanceSq, product] <;> ac_rfl
      · have h := sorted_stability m M z y x hm hz.1 (le_of_not_ge hyz) (le_of_not_ge hxy) hx.2
        convert h using 1 <;> simp only [distanceSq, product] <;> ac_rfl

theorem distanceSq_lower_corner (m M : ℝ) : distanceSq m M m m m = (M - m) ^ 2 := by
  unfold distanceSq
  simp only [sub_self, zero_pow (show (2 : ℕ) ≠ 0 by decide), zero_add, add_zero]
  have hsq : (m - M) ^ 2 = (M - m) ^ 2 := by ring
  rw [hsq]
  simp [show (M - m) ^ 2 ≤ (M - m) ^ 2 + (M - m) ^ 2 by nlinarith [sq_nonneg (M - m)]]

theorem lower_corner_deficit (m M : ℝ) (hm : 0 < m) :
    optimum m M - product m m m = 2 / (m * M) * (M - m) ^ 2 := by
  unfold optimum product
  field_simp [ne_of_gt hm]
  ring

/-- The global coefficient is exactly twice the two-point unweighted one. -/
theorem coefficient_optimal (m M C : ℝ) (hm : 0 < m) (hmM : m < M)
    (hC : ∀ x y z : ℝ, (m ≤ x ∧ x ≤ M) → (m ≤ y ∧ y ≤ M) → (m ≤ z ∧ z ≤ M) →
      C * distanceSq m M x y z ≤ optimum m M - product x y z) :
    C ≤ 2 / (m * M) := by
  have h := hC m m m ⟨le_rfl, le_of_lt hmM⟩ ⟨le_rfl, le_of_lt hmM⟩ ⟨le_rfl, le_of_lt hmM⟩
  rw [distanceSq_lower_corner, lower_corner_deficit m M hm] at h
  by_contra hnot
  have hs := mul_lt_mul_of_pos_right (lt_of_not_ge hnot) (sq_pos_of_pos (sub_pos.mpr hmM))
  exact (not_lt_of_ge h) hs

theorem optimal_coefficient_iff (m M C : ℝ) (hm : 0 < m) (hmM : m < M) :
    (∀ x y z : ℝ, (m ≤ x ∧ x ≤ M) → (m ≤ y ∧ y ≤ M) → (m ≤ z ∧ z ≤ M) →
      C * distanceSq m M x y z ≤ optimum m M - product x y z) ↔
    C ≤ 2 / (m * M) := by
  constructor
  · exact coefficient_optimal m M C hm hmM
  · intro hC x y z hx hy hz
    exact (mul_le_mul_of_nonneg_right hC (distanceSq_nonneg m M x y z)).trans
      (sharp_stability m M x y z hm hx hy hz)

theorem endpoints_attain (m M : ℝ) (hm : 0 < m) (hM : 0 < M) :
    product m m M = optimum m M := by
  unfold product optimum
  field_simp [ne_of_gt hm, ne_of_gt hM]
  ring

#print axioms sharp_stability
#print axioms coefficient_optimal
#print axioms optimal_coefficient_iff

end

end ThreePointKantorovich
