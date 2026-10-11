import Mathlib.Probability.Moments.Covariance

/-!
# Executable checks for `Mathlib.Probability.Moments.Covariance`

This companion file is checked against mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` (Lean 4.34.0).
-/

open MeasureTheory
open scoped ProbabilityTheory

-- Definition and the probability-measure expansion.
#check ProbabilityTheory.covariance
#check ProbabilityTheory.covariance_eq_sub

-- Zero, symmetry, constants, and elementary algebra.
#check ProbabilityTheory.covariance_zero_left
#check ProbabilityTheory.covariance_zero_right
#check ProbabilityTheory.covariance_zero_measure
#check ProbabilityTheory.covariance_comm
#check ProbabilityTheory.covariance_const_left
#check ProbabilityTheory.covariance_const_right
#check ProbabilityTheory.covariance_add_const_left
#check ProbabilityTheory.covariance_const_add_left
#check ProbabilityTheory.covariance_add_const_right
#check ProbabilityTheory.covariance_const_add_right
#check ProbabilityTheory.covariance_add_left
#check ProbabilityTheory.covariance_add_right
#check ProbabilityTheory.covariance_smul_left
#check ProbabilityTheory.covariance_smul_right
#check ProbabilityTheory.covariance_const_mul_left
#check ProbabilityTheory.covariance_const_mul_right
#check ProbabilityTheory.covariance_mul_const_left
#check ProbabilityTheory.covariance_mul_const_right
#check ProbabilityTheory.covariance_fun_div_left
#check ProbabilityTheory.covariance_fun_div_right
#check ProbabilityTheory.covariance_neg_left
#check ProbabilityTheory.covariance_fun_neg_left
#check ProbabilityTheory.covariance_neg_right
#check ProbabilityTheory.covariance_fun_neg_right
#check ProbabilityTheory.covariance_sub_left
#check ProbabilityTheory.covariance_fun_sub_left
#check ProbabilityTheory.covariance_sub_right
#check ProbabilityTheory.covariance_fun_sub_right
#check ProbabilityTheory.covariance_sub_sub
#check ProbabilityTheory.covariance_fun_sub_fun_sub
#check ProbabilityTheory.covariance_sub_const_left
#check ProbabilityTheory.covariance_const_sub_left
#check ProbabilityTheory.covariance_sub_const_right
#check ProbabilityTheory.covariance_const_sub_right

-- Finite sums.
#check ProbabilityTheory.covariance_sum_left'
#check ProbabilityTheory.covariance_sum_left
#check ProbabilityTheory.covariance_fun_sum_left'
#check ProbabilityTheory.covariance_fun_sum_left
#check ProbabilityTheory.covariance_sum_right'
#check ProbabilityTheory.covariance_sum_right
#check ProbabilityTheory.covariance_fun_sum_right'
#check ProbabilityTheory.covariance_fun_sum_right
#check ProbabilityTheory.covariance_sum_sum'
#check ProbabilityTheory.covariance_sum_sum
#check ProbabilityTheory.covariance_fun_sum_fun_sum'
#check ProbabilityTheory.covariance_fun_sum_fun_sum

-- Change of variables and independence.
#check ProbabilityTheory.covariance_map_equiv
#check ProbabilityTheory.covariance_map
#check ProbabilityTheory.covariance_map_fun
#check ProbabilityTheory.IndepFun.covariance_eq_zero
#check ProbabilityTheory.covariance_fst_snd_prod

namespace CovarianceSurvey

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} {X Y Z T : Ω → ℝ}

example [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[X, Y; μ] = μ[X * Y] - μ[X] * μ[Y] :=
  ProbabilityTheory.covariance_eq_sub hX hY

example : cov[X, Y; μ] = cov[Y, X; μ] :=
  ProbabilityTheory.covariance_comm X Y

example [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hZ : MemLp Z 2 μ) (hT : MemLp T 2 μ) :
    cov[X - Y, Z - T; μ] =
      cov[X, Z; μ] - cov[X, T; μ] - cov[Y, Z; μ] + cov[Y, T; μ] :=
  ProbabilityTheory.covariance_sub_sub hX hY hZ hT

example (h : ProbabilityTheory.IndepFun X Y μ) (hX : MemLp X 2 μ)
    (hY : MemLp Y 2 μ) : cov[X, Y; μ] = 0 :=
  h.covariance_eq_zero hX hY

end CovarianceSurvey
