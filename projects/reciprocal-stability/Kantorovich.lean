import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Fixed-weight Kantorovich inequality

A local formalization of established finite weighted inequalities.
All weights are nonnegative; values lie in a positive closed interval.
The total weight need not be one. Empty sets and equal interval endpoints
are included.
-/

open scoped BigOperators

namespace Kantorovich

noncomputable section

def objective {ι : Type*} (s : Finset ι) (w x : ι → ℝ) : ℝ :=
  (∑ i ∈ s, w i * x i) * (∑ i ∈ s, w i / x i)

def endpoint {ι : Type*} [DecidableEq ι] (m M : ℝ) (S : Finset ι) (i : ι) : ℝ :=
  if i ∈ S then m else M

/-- The chord gap of the one-coordinate objective, with positive denominators. -/
theorem chord_gap (m M t p A B : ℝ) (hm : 0 < m) (ht : 0 < t) (hM : 0 < M) :
    (M - t) * ((A + p * m) * (B + p / m)) +
      (t - m) * ((A + p * M) * (B + p / M)) -
      (M - m) * ((A + p * t) * (B + p / t)) =
    (M - m) * p * A * (M - t) * (t - m) / (m * M * t) := by
  field_simp [ne_of_gt hm, ne_of_gt ht, ne_of_gt hM]
  ring

/-- Some endpoint is at least as good as the current coordinate. -/
theorem coordinate_endpoint (m M t p A B : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hmt : m ≤ t) (htM : t ≤ M)
    (hp : 0 ≤ p) (hA : 0 ≤ A) :
    ∃ z : ℝ, (z = m ∨ z = M) ∧
      (A + p * t) * (B + p / t) ≤ (A + p * z) * (B + p / z) := by
  by_cases heq : m = M
  · have htm : t = m := by linarith
    exact ⟨m, Or.inl rfl, by simp [htm]⟩
  have hlt : m < M := lt_of_le_of_ne hmM heq
  have ht : 0 < t := lt_of_lt_of_le hm hmt
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hmm : 0 ≤ M - m := sub_nonneg.mpr hmM
  have htm : 0 ≤ t - m := sub_nonneg.mpr hmt
  have hMt : 0 ≤ M - t := sub_nonneg.mpr htM
  have hgap := chord_gap m M t p A B hm ht hM
  have hnonneg : 0 ≤
      (M - m) * p * A * (M - t) * (t - m) / (m * M * t) := by
    positivity
  by_cases hleft : (A + p * t) * (B + p / t) ≤
      (A + p * m) * (B + p / m)
  · exact ⟨m, Or.inl rfl, hleft⟩
  refine ⟨M, Or.inr rfl, ?_⟩
  by_contra hright
  have h1 := lt_of_not_ge hleft
  have h2 := lt_of_not_ge hright
  have h3 : 0 ≤ M - t := sub_nonneg.mpr htM
  have h4 : 0 ≤ t - m := sub_nonneg.mpr hmt
  have htne : t ≠ M := by
    intro he
    apply hright
    simp [he]
  have hMtpos : 0 < M - t := sub_pos.mpr (lt_of_le_of_ne htM htne)
  have hfirst := mul_lt_mul_of_pos_left h1 hMtpos
  have hsecond := mul_le_mul_of_nonneg_left (le_of_lt h2) h4
  have hsum := add_lt_add_of_lt_of_le hfirst hsecond
  have hcombine :
      (M - t) * ((A + p * t) * (B + p / t)) +
        (t - m) * ((A + p * t) * (B + p / t)) =
      (M - m) * ((A + p * t) * (B + p / t)) := by ring
  rw [hcombine] at hsum
  linarith

/-- Round all coordinates while retaining arbitrary nonnegative offsets. -/
theorem endpoint_rounding_with_offsets {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M) :
    ∀ (w x : ι → ℝ) (A B : ℝ),
      (∀ i ∈ s, 0 ≤ w i) → (∀ i ∈ s, m ≤ x i ∧ x i ≤ M) →
      0 ≤ A → 0 ≤ B →
      ∃ y : ι → ℝ, (∀ i ∈ s, y i = m ∨ y i = M) ∧
        (A + ∑ i ∈ s, w i * x i) * (B + ∑ i ∈ s, w i / x i) ≤
        (A + ∑ i ∈ s, w i * y i) * (B + ∑ i ∈ s, w i / y i) := by
  induction s using Finset.induction_on with
  | empty =>
    intro w x A B hw hx hA hB
    exact ⟨fun _ => m, by simp, by simp⟩
  | @insert a s ha ih =>
    intro w x A B hw hx hA hB
    have hws : ∀ i ∈ s, 0 ≤ w i := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    have hxs : ∀ i ∈ s, m ≤ x i ∧ x i ≤ M :=
      fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hwa : 0 ≤ w a := hw a (Finset.mem_insert_self a s)
    have hxa := hx a (Finset.mem_insert_self a s)
    have hsumA : 0 ≤ A + ∑ i ∈ s, w i * x i := by
      apply add_nonneg hA
      exact Finset.sum_nonneg fun i hi => mul_nonneg (hws i hi) (le_trans (le_of_lt hm) (hxs i hi).1)
    have hsumB : 0 ≤ B + ∑ i ∈ s, w i / x i := by
      apply add_nonneg hB
      exact Finset.sum_nonneg fun i hi => div_nonneg (hws i hi) (le_trans (le_of_lt hm) (hxs i hi).1)
    obtain ⟨t, ht, hstep⟩ := coordinate_endpoint m M (x a) (w a)
      (A + ∑ i ∈ s, w i * x i) (B + ∑ i ∈ s, w i / x i)
      hm hmM hxa.1 hxa.2 hwa hsumA
    have htpos : 0 < t := by rcases ht with rfl | rfl <;> linarith
    obtain ⟨y, hy, htail⟩ := ih w x (A + w a * t) (B + w a / t)
      hws hxs (add_nonneg hA (mul_nonneg hwa (le_of_lt htpos)))
      (add_nonneg hB (div_nonneg hwa (le_of_lt htpos)))
    let z := Function.update y a t
    have hz : ∀ i ∈ s, z i = y i := by
      intro i hi
      have hia : i ≠ a := by intro he; subst i; exact ha hi
      simp [z, Function.update_of_ne hia]
    refine ⟨z, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa [z] using ht
      · rw [hz i hi]
        exact hy i hi
    · have hsum1 : (∑ i ∈ s, w i * z i) = ∑ i ∈ s, w i * y i :=
        Finset.sum_congr rfl fun i hi => by rw [hz i hi]
      have hsum2 : (∑ i ∈ s, w i / z i) = ∑ i ∈ s, w i / y i :=
        Finset.sum_congr rfl fun i hi => by rw [hz i hi]
      simp only [Finset.sum_insert ha]
      have hza : z a = t := by simp [z]
      rw [hza, hsum1, hsum2]
      have hstep' :
          (A + (w a * x a + ∑ i ∈ s, w i * x i)) *
            (B + (w a / x a + ∑ i ∈ s, w i / x i)) ≤
          (A + w a * t + ∑ i ∈ s, w i * x i) *
            (B + w a / t + ∑ i ∈ s, w i / x i) := by
        convert hstep using 1
        all_goals ring
      have htail' :
          (A + w a * t + ∑ i ∈ s, w i * x i) *
            (B + w a / t + ∑ i ∈ s, w i / x i) ≤
          (A + (w a * t + ∑ i ∈ s, w i * y i)) *
            (B + (w a / t + ∑ i ∈ s, w i / y i)) := by
        convert htail using 1
        ring
      exact hstep'.trans htail'

/-- Endpoint assignments attain at least the objective of any admissible input. -/
theorem endpoint_rounding {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, m ≤ x i ∧ x i ≤ M) :
    ∃ S ⊆ s, objective s w x ≤ objective s w (endpoint m M S) := by
  classical
  obtain ⟨y, hy, hle⟩ := endpoint_rounding_with_offsets s m M hm hmM w x 0 0
    hw hx (by norm_num) (by norm_num)
  let S := s.filter fun i => y i = m
  have hS : S ⊆ s := Finset.filter_subset _ _
  have hye : ∀ i ∈ s, y i = endpoint m M S i := by
    intro i hi
    rcases hy i hi with h | h
    · simp [endpoint, S, hi, h]
    · by_cases hsame : M = m
      · simp [endpoint, S, hi, h, hsame]
      · simp [endpoint, S, hi, h, hsame]
  refine ⟨S, hS, ?_⟩
  have ha : (∑ i ∈ s, w i * y i) = ∑ i ∈ s, w i * endpoint m M S i :=
    Finset.sum_congr rfl fun i hi => by rw [hye i hi]
  have hb : (∑ i ∈ s, w i / y i) = ∑ i ∈ s, w i / endpoint m M S i :=
    Finset.sum_congr rfl fun i hi => by rw [hye i hi]
  simpa [objective, ha, hb] using hle

def mass {ι : Type*} (s : Finset ι) (w : ι → ℝ) : ℝ := ∑ i ∈ s, w i

/-- Evaluate an endpoint assignment by the two partition masses. -/
theorem endpoint_objective {ι : Type*} [DecidableEq ι]
    (s S : Finset ι) (hS : S ⊆ s) (w : ι → ℝ) (m M : ℝ) :
    objective s w (endpoint m M S) =
      (m * mass S w + M * mass (s \ S) w) *
      (mass S w / m + mass (s \ S) w / M) := by
  classical
  have hf : s.filter (fun i => i ∈ S) = S := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hfn : s.filter (fun i => i ∉ S) = s \ S := by
    ext i
    simp
  unfold objective endpoint
  simp only [mul_ite, div_ite]
  rw [Finset.sum_ite, Finset.sum_ite, hf, hfn]
  simp only [← Finset.sum_mul, ← Finset.sum_div]
  dsimp [mass]
  ring

/-- The exact partition correction to the usual constant. -/
theorem partition_identity {ι : Type*} [DecidableEq ι]
    (s S : Finset ι) (hS : S ⊆ s) (w : ι → ℝ) (m M : ℝ)
    (hm : 0 < m) (hM : 0 < M) :
    4 * m * M * objective s w (endpoint m M S) =
      (m + M) ^ 2 * (mass S w + mass (s \ S) w) ^ 2 -
      (M - m) ^ 2 * (mass S w - mass (s \ S) w) ^ 2 := by
  rw [endpoint_objective s S hS w m M]
  field_simp [ne_of_gt hm, ne_of_gt hM]
  ring

/-- One endpoint partition maximizes the objective for every admissible input.
The quantifier order makes the partition independent of the input values. -/
theorem exists_sharp_endpoint_partition {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℝ) (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∃ S ⊆ s, ∀ x : ι → ℝ, (∀ i ∈ s, m ≤ x i ∧ x i ≤ M) →
      objective s w x ≤ objective s w (endpoint m M S) := by
  classical
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image s.powerset
    (fun T => objective s w (endpoint m M T)) ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset s)⟩
  refine ⟨S, Finset.mem_powerset.mp hS, ?_⟩
  intro x hx
  obtain ⟨T, hT, hle⟩ := endpoint_rounding s w x m M hm hmM hw hx
  exact hle.trans (hmax T (Finset.mem_powerset.mpr hT))

theorem mass_partition {ι : Type*} [DecidableEq ι]
    (s S : Finset ι) (hS : S ⊆ s) (w : ι → ℝ) :
    mass S w + mass (s \ S) w = mass s w := by
  dsimp [mass]
  simpa [add_comm] using Finset.sum_sdiff (f := w) hS

def imbalanceSq {ι : Type*} [DecidableEq ι]
    (s S : Finset ι) (w : ι → ℝ) : ℝ :=
  (mass S w - mass (s \ S) w) ^ 2

/-- A minimum-imbalance partition gives the exact sharp fixed-weight bound. -/
theorem sharp_fixed_weight_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℝ) (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∃ S ⊆ s,
      (∀ T ⊆ s, imbalanceSq s S w ≤ imbalanceSq s T w) ∧
      (∀ x : ι → ℝ, (∀ i ∈ s, m ≤ x i ∧ x i ≤ M) →
        4 * m * M * objective s w x ≤
          (m + M) ^ 2 * (mass s w) ^ 2 - (M - m) ^ 2 * imbalanceSq s S w) ∧
      4 * m * M * objective s w (endpoint m M S) =
        (m + M) ^ 2 * (mass s w) ^ 2 - (M - m) ^ 2 * imbalanceSq s S w := by
  classical
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image s.powerset
    (fun T => imbalanceSq s T w) ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset s)⟩
  have hs : S ⊆ s := Finset.mem_powerset.mp hS
  have hidS := partition_identity s S hs w m M hm hM
  rw [mass_partition s S hs w] at hidS
  change 4 * m * M * objective s w (endpoint m M S) =
    (m + M) ^ 2 * (mass s w) ^ 2 - (M - m) ^ 2 * imbalanceSq s S w at hidS
  refine ⟨S, hs, ?_, ?_, hidS⟩
  · intro T hT
    exact hmin T (Finset.mem_powerset.mpr hT)
  · intro x hx
    obtain ⟨T, hT, hle⟩ := endpoint_rounding s w x m M hm hmM hw hx
    have hidT := partition_identity s T hT w m M hm hM
    rw [mass_partition s T hT w] at hidT
    change 4 * m * M * objective s w (endpoint m M T) =
      (m + M) ^ 2 * (mass s w) ^ 2 - (M - m) ^ 2 * imbalanceSq s T w at hidT
    have hscaled := mul_le_mul_of_nonneg_left hle (show 0 ≤ 4 * m * M by positivity)
    have hcorrection := mul_le_mul_of_nonneg_left
      (hmin T (Finset.mem_powerset.mpr hT)) (sq_nonneg (M - m))
    linarith

/-- The classical unnormalized weighted Kantorovich inequality. -/
theorem weighted_kantorovich {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, m ≤ x i ∧ x i ≤ M) :
    objective s w x ≤ (m + M) ^ 2 * (mass s w) ^ 2 / (4 * m * M) := by
  obtain ⟨S, hS, hmin, hbound, heq⟩ := sharp_fixed_weight_bound s w m M hm hmM hw
  have h := hbound x hx
  have hnonneg : 0 ≤ (M - m) ^ 2 * imbalanceSq s S w :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hpos : 0 < 4 * m * M := by positivity
  apply (le_div_iff₀ hpos).mpr
  nlinarith

/-- Without an exactly balanced partition the usual bound is strictly loose. -/
theorem strict_if_no_balanced_partition {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (m M : ℝ) (hm : 0 < m) (hmM : m < M)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, m ≤ x i ∧ x i ≤ M)
    (hno : ∀ S ⊆ s, mass S w ≠ mass (s \ S) w) :
    objective s w x < (m + M) ^ 2 * (mass s w) ^ 2 / (4 * m * M) := by
  obtain ⟨S, hS, hmin, hbound, heq⟩ :=
    sharp_fixed_weight_bound s w m M hm (le_of_lt hmM) hw
  have h := hbound x hx
  have hM : 0 < M := lt_trans hm hmM
  have hgap : 0 < imbalanceSq s S w := sq_pos_of_ne_zero (sub_ne_zero.mpr (hno S hS))
  have hcorrection : 0 < (M - m) ^ 2 * imbalanceSq s S w :=
    mul_pos (sq_pos_of_pos (sub_pos.mpr hmM)) hgap
  apply (lt_div_iff₀ (show 0 < 4 * m * M by positivity)).mpr
  nlinarith

#print axioms chord_gap
#print axioms coordinate_endpoint
#print axioms endpoint_rounding_with_offsets
#print axioms sharp_fixed_weight_bound
#print axioms weighted_kantorovich
#print axioms strict_if_no_balanced_partition

/-- A concrete sharp example: weights one and two, interval one to four. -/
theorem two_weight_example (x y : ℝ) (hx : 1 ≤ x ∧ x ≤ 4) (hy : 1 ≤ y ∧ y ≤ 4) :
    (x + 2 * y) * (1 / x + 2 / y) ≤ 27 / 2 := by
  have hy0 : 0 ≤ 2 * y := by linarith [hy.1]
  obtain ⟨t, ht, h1⟩ := coordinate_endpoint 1 4 x 1 (2 * y) (2 / y)
    (by norm_num) (by norm_num) hx.1 hx.2 (by norm_num) hy0
  have ht0 : 0 ≤ t := by rcases ht with rfl | rfl <;> norm_num
  obtain ⟨u, hu, h2⟩ := coordinate_endpoint 1 4 y 2 t (1 / t)
    (by norm_num) (by norm_num) hy.1 hy.2 (by norm_num) ht0
  have h1' : (x + 2 * y) * (1 / x + 2 / y) ≤
      (t + 2 * y) * (1 / t + 2 / y) := by
    convert h1 using 1 <;> ring
  have h := h1'.trans h2
  rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;> norm_num at h ⊢ <;> linarith

theorem two_weight_example_attained :
    ((1 : ℝ) + 2 * 4) * (1 / 1 + 2 / 4) = 27 / 2 := by norm_num

theorem two_weight_example_improves_classical :
    (27 / 2 : ℝ) < (1 + 4) ^ 2 * (1 + 2) ^ 2 / (4 * 1 * 4) := by norm_num

/-- The maximizing endpoint assignments satisfy the original interval constraint. -/
theorem endpoint_mem_interval {ι : Type*} [DecidableEq ι]
    (m M : ℝ) (S : Finset ι) (i : ι) (hmM : m ≤ M) :
    m ≤ endpoint m M S i ∧ endpoint m M S i ≤ M := by
  unfold endpoint
  split_ifs <;> exact ⟨by linarith, by linarith⟩

/-- For a genuine interval, the classical constant is attained exactly when
the fixed weights admit an equal-mass partition. -/
theorem classical_attainment_iff_balanced {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℝ) (m M : ℝ) (hm : 0 < m) (hmM : m < M)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∃ x : ι → ℝ, (∀ i ∈ s, m ≤ x i ∧ x i ≤ M) ∧
      objective s w x = (m + M) ^ 2 * (mass s w) ^ 2 / (4 * m * M)) ↔
    ∃ S ⊆ s, mass S w = mass (s \ S) w := by
  constructor
  · rintro ⟨x, hx, heq⟩
    by_contra hno
    have hno' : ∀ S ⊆ s, mass S w ≠ mass (s \ S) w := by
      intro S hS he
      exact hno ⟨S, hS, he⟩
    have hlt := strict_if_no_balanced_partition s w x m M hm hmM hw hx hno'
    exact (ne_of_lt hlt) heq
  · rintro ⟨S, hS, heq⟩
    refine ⟨endpoint m M S, fun i _ => endpoint_mem_interval m M S i (le_of_lt hmM), ?_⟩
    have hM : 0 < M := lt_trans hm hmM
    have hid := partition_identity s S hS w m M hm hM
    rw [mass_partition s S hS w, heq, sub_self, zero_pow (by decide), mul_zero, sub_zero] at hid
    apply (eq_div_iff (show 4 * m * M ≠ 0 by positivity)).mpr
    nlinarith

#print axioms two_weight_example
#print axioms classical_attainment_iff_balanced

end

end Kantorovich
