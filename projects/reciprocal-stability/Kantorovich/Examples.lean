import Kantorovich.ThreeStability

namespace ReciprocalStabilityExamples

theorem two_lower_corner :
    TwoPointKantorovich.distanceSq 1 4 1 1 = 9 ∧
    TwoPointKantorovich.optimum 1 1 1 4 - TwoPointKantorovich.product 1 1 1 1 = 9 / 4 := by
  norm_num [TwoPointKantorovich.distanceSq, TwoPointKantorovich.optimum, TwoPointKantorovich.product]

theorem three_lower_corner :
    ThreePointKantorovich.distanceSq 1 4 1 1 1 = 9 ∧
    ThreePointKantorovich.optimum 1 4 - ThreePointKantorovich.product 1 1 1 = 9 / 2 := by
  norm_num [ThreePointKantorovich.distanceSq, ThreePointKantorovich.optimum, ThreePointKantorovich.product]

theorem three_midpoint_equality :
    ThreePointKantorovich.distanceSq 1 4 1 (5 / 2) 4 = 9 / 4 ∧
    ThreePointKantorovich.optimum 1 4 - ThreePointKantorovich.product 1 (5 / 2) 4 = 9 / 8 := by
  norm_num [ThreePointKantorovich.distanceSq, ThreePointKantorovich.optimum, ThreePointKantorovich.product]

end ReciprocalStabilityExamples
