import SparseLowerTail.Numerics.MatrixInterval4

/-! Interval enclosures of actual four-dimensional solutions, reusing a common
matrix enclosure and determinant. No approximate solution is a proof premise. -/
namespace SparseLowerTail.Numerics

theorem matrixSolution4_eq_cramer {M : Matrix (Fin 4) (Fin 4) ℝ}
    {b x : Fin 4 → ℝ} (hd : M.det≠0) (hx : M.mulVec x=b) (j : Fin 4) :
    x j=(M.updateCol j b).det/M.det := by
  have hv : x=M.det⁻¹ • Matrix.cramer M b := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hd))
    rw [hx,Matrix.mulVec_smul,Matrix.mulVec_cramer,smul_smul,inv_mul_cancel₀ hd,one_smul]
  rw [hv]
  simp only [Pi.smul_apply,smul_eq_mul,Matrix.cramer_apply,div_eq_mul_inv,mul_comm]

theorem matrixSolution4_interval {M : Matrix (Fin 4) (Fin 4) ℝ}
    {b x : Fin 4 → ℝ} {box : Fin 4 → Fin 4 → DyadicInterval}
    {rhs : Fin 4 → DyadicInterval} {D N J : DyadicInterval}
    (hbox : ∀i j,(box i j).contains (M i j))
    (hrhs : ∀i,(rhs i).contains (b i))
    (hD : matrixDetInterval4 box=some D) (hzero : D.ApartZero)
    (hInv : D.inv?=some J) (hx : M.mulVec x=b) (j : Fin 4)
    (hN : matrixDetInterval4 (fun i k => if k=j then rhs i else box i k)=some N) :
    (N.mul J).contains (x j) := by
  have hd := matrixDet_ne_zero_of_interval hbox hD hzero
  rw [matrixSolution4_eq_cramer hd hx j,div_eq_mul_inv]
  apply DyadicInterval.mul_contains
  · apply matrixDetInterval4_contains (hI := hN)
    intro i k
    simp only [Matrix.updateCol_apply]
    split_ifs
    · exact hrhs i
    · exact hbox i k
  · exact DyadicInterval.inv?_contains (matrixDetInterval4_contains hbox hD) hInv

end SparseLowerTail.Numerics
