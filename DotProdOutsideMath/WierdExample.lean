import Mathlib


variable {m n: Type _}[Fintype n][Fintype m]
variable {K: Type}[IsROrC K]

open Matrix BigOperators


@[simp]
theorem IsROrC.re_sum (f : α → K) : IsROrC.re (∑ i in s, f i) = ∑ i in s, IsROrC.re (f i) := by 
  apply map_sum _ _

@[simp]
theorem IsROrC.im_sum (f : α → K) : IsROrC.im (∑ i in s, f i) = ∑ i in s, IsROrC.im (f i) := by
  apply map_sum _ _

lemma dot_product_star_self_eq_zero_iff_R_or_C 
    (v : n → K) : Matrix.dotProduct (star v) v = 0 ↔  v = 0 := by 
  simp_rw [Matrix.dotProduct, Pi.star_apply, ← starRingEnd_apply, IsROrC.conj_mul]
  rw [IsROrC.ext_iff]
  simp only [IsROrC.re_sum, IsROrC.ofReal_re, map_zero, IsROrC.im_sum, IsROrC.ofReal_im, 
    Finset.sum_const_zero, and_true]
  constructor
  · intro hr
    rw [Finset.sum_eq_zero_iff_of_nonneg] at hr
    · simp only [Finset.mem_univ, map_eq_zero, forall_true_left] at hr
      funext i
      exact hr i
    · simp only [Finset.mem_univ, forall_true_left]
      intro
      apply IsROrC.normSq_nonneg
  · intro h
    rw [h]
    simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero]

theorem ker_mulVecLin_conjTranspose_mul_self_R_or_C (A : Matrix m n K) :
    LinearMap.ker (Aᴴ ⬝ A).mulVecLin = LinearMap.ker (mulVecLin A) := by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, ← mulVec_mulVec]
  constructor
  · intro h
    replace h := congr_arg (dotProduct (star x)) h
    rwa [dotProduct_zero, dotProduct_mulVec, vecMul_conjTranspose, star_star, 
      dot_product_star_self_eq_zero_iff_R_or_C] at h
  · intro h
    rw [h, mulVec_zero]

open FiniteDimensional Matrix

theorem rank_conjTranspose_mul_self_R_or_C (A : Matrix m n K) : (Aᴴ ⬝ A).rank = A.rank := by
  dsimp only [Matrix.rank]
  refine' add_left_injective (finrank K (LinearMap.ker (mulVecLin A))) _
  dsimp only
  trans finrank K { x // x ∈ LinearMap.range (mulVecLin (Aᴴ ⬝ A)) } +
    finrank K { x // x ∈ LinearMap.ker (mulVecLin (Aᴴ ⬝ A)) }
  -- simp?
  · rw [ker_mulVecLin_conjTranspose_mul_self_R_or_C]
  · simp only [LinearMap.finrank_range_add_finrank_ker]

variable {R: Type}[Field R][PartialOrder R][StarOrderedRing R]
theorem NotInMathlib_rank_conjTranspose_mul_self (A : Matrix m n R) : (Aᴴ ⬝ A).rank = A.rank := by
  dsimp only [rank]
  refine' add_left_injective (finrank R (LinearMap.ker (mulVecLin A))) _
  dsimp only
  trans finrank R { x // x ∈ LinearMap.range (mulVecLin (Aᴴ ⬝ A)) } +
    finrank R { x // x ∈ LinearMap.ker (mulVecLin (Aᴴ ⬝ A)) }
  · rw [ker_mulVecLin_conjTranspose_mul_self]
  · simp only [LinearMap.finrank_range_add_finrank_ker]