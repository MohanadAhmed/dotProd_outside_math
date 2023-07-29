-- import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.IsROrC.Basic


variable {m n: Type _}[Fintype n][Fintype m]
variable {K: Type}[IsROrC K]

open Matrix BigOperators
open FiniteDimensional Matrix

@[simp]
theorem IsROrC.re_sum (f : α → K) : IsROrC.re (∑ i in s, f i) = ∑ i in s, IsROrC.re (f i) := by 
  apply map_sum _ _

@[simp]
theorem IsROrC.im_sum (f : α → K) : IsROrC.im (∑ i in s, f i) = ∑ i in s, IsROrC.im (f i) := by
  apply map_sum _ _

lemma dot_product_star_self_eq_zero_iff_R_or_C 
    (v : n → K) : Matrix.dotProduct (star v) v = 0 ↔  v = 0 := by sorry

theorem ker_mulVecLin_conjTranspose_mul_self_R_or_C (A : Matrix m n K) :
    LinearMap.ker (Aᴴ ⬝ A).mulVecLin = LinearMap.ker (mulVecLin A) := by sorry

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