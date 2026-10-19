import SparseLowerTail.Section07.SpectralRemainder

/-! The explicit scalar error terms `eq:s7errors`.
The arguments are η=μt/2, m=edge density, ev=leading eigenvalue,
M=√(A/ev), s=m−ev, and A=m+μt. -/
noncomputable section
namespace SparseLowerTail.Section07

def rowMeanError (η ev M s A : ℝ) : ℝ :=
  η*(2*M^2-1)+3*ev*M*(M-1)+M^2*Real.sqrt (s*A)*Real.sqrt (2-2/M)

def rowCodegreeError (η m ev M s A : ℝ) : ℝ :=
  η*m/2+2*ev*M^2*η+Real.sqrt (A*s*η*m/2)+4*M^2*(m+η)*η+
    2*M^2*s*Real.sqrt (η*m/2)+5*ev^2*M*(M-1)+2*M^2*s*Real.sqrt (s*A)

def rowBaseError (m η ev M : ℝ) : ℝ :=
  |m-1/2| *(m+η)+ev*|ev-1/2| *M

def rowEulerError (μ η m ev M s A : ℝ) : ℝ :=
  μ*(rowCodegreeError η m ev M s A+rowBaseError m η ev M+rowMeanError η ev M s A/2)

end SparseLowerTail.Section07
