import SparseLowerTail.Numerics.RationalMatrix4

/-! Check each matrix entry once, then bound its determinant using only the
sixteen resulting intervals. This avoids replaying expensive expressions
at every occurrence in the determinant expansion. -/
namespace SparseLowerTail.Numerics

def matrixIndex4 (i j : Fin 4) : Fin 16 := ⟨4*i.val+j.val,by omega⟩

def flattenMatrix4 {α : Type*} (M : Fin 4 → Fin 4 → α) : Fin 16 → α :=
  fun k => M ⟨k.val/4,by omega⟩ ⟨k.val%4,by omega⟩

theorem flattenMatrix4_index {α : Type*} (M : Fin 4 → Fin 4 → α) (i j : Fin 4) :
    flattenMatrix4 M (matrixIndex4 i j)=M i j := by
  fin_cases i <;> fin_cases j <;> rfl

def matrixVariables4 (i j : Fin 4) : RationalExpr 16 := .var (matrixIndex4 i j)

theorem matrixVariables4_eval (M : Matrix (Fin 4) (Fin 4) ℝ) :
    RationalExpr.matrixEval matrixVariables4 (flattenMatrix4 M)=M := by
  funext i j
  exact flattenMatrix4_index M i j

def matrixDetInterval4 (box : Fin 4 → Fin 4 → DyadicInterval) : Option DyadicInterval :=
  (RationalExpr.det4 matrixVariables4).dyadicEval (flattenMatrix4 box)

theorem matrixDetInterval4_contains {M : Matrix (Fin 4) (Fin 4) ℝ}
    {box : Fin 4 → Fin 4 → DyadicInterval} {I : DyadicInterval}
    (hbox : ∀i j,(box i j).contains (M i j))
    (hI : matrixDetInterval4 box=some I) : I.contains M.det := by
  have h : ∀k,(flattenMatrix4 box k).contains (flattenMatrix4 M k) :=
    fun k => hbox _ _
  have hd := RationalExpr.dyadicEval_contains (RationalExpr.det4 matrixVariables4) h hI
  simpa only [RationalExpr.det4_eval,matrixVariables4_eval] using hd

theorem matrixDet_ne_zero_of_interval {M : Matrix (Fin 4) (Fin 4) ℝ}
    {box : Fin 4 → Fin 4 → DyadicInterval} {I : DyadicInterval}
    (hbox : ∀i j,(box i j).contains (M i j))
    (hI : matrixDetInterval4 box=some I) (hzero : I.ApartZero) : M.det≠0 :=
  DyadicInterval.ne_zero_of_contains hzero (matrixDetInterval4_contains hbox hI)

end SparseLowerTail.Numerics
