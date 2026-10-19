import SparseLowerTail.Numerics.ExpEndpoints

/-! Generated rational proposals; the Valid proofs are kernel checked. -/
namespace SparseLowerTail.Numerics.WideExpSmoke
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def endpoint0 : ExpEndpointCertificate :=
  ⟨(-32/1 : ℚ), 20, (3133965575612453541/1152921504606846976 : ℚ), (3133965575612453543/1152921504606846976 : ℚ), (45519047431013386932820748705743/576460752303423488 : ℚ), (45519047431013387862383937993661/576460752303423488 : ℚ)⟩
theorem endpoint0_valid : endpoint0.Valid := by decide +kernel
theorem endpoint0_bounds :
    Bounds (Real.exp (-(endpoint0.q : ℝ)))
      (endpoint0.lower : ℝ) (endpoint0.upper : ℝ) :=
  endpoint0.bounds endpoint0_valid

def endpoint1 : ExpEndpointCertificate :=
  ⟨(0/1 : ℚ), 20, (1/1 : ℚ), (1/1 : ℚ), (1/1 : ℚ), (1/1 : ℚ)⟩
theorem endpoint1_valid : endpoint1.Valid := by decide +kernel
theorem endpoint1_bounds :
    Bounds (Real.exp (-(endpoint1.q : ℝ)))
      (endpoint1.lower : ℝ) (endpoint1.upper : ℝ) :=
  endpoint1.bounds endpoint1_valid

def endpoint2 : ExpEndpointCertificate :=
  ⟨(16/1 : ℚ), 20, (26508507426831583/72057594037927936 : ℚ), (212068059414652665/576460752303423488 : ℚ), (64872111479/576460752303423488 : ℚ), (129744222959/1152921504606846976 : ℚ)⟩
theorem endpoint2_valid : endpoint2.Valid := by decide +kernel
theorem endpoint2_bounds :
    Bounds (Real.exp (-(endpoint2.q : ℝ)))
      (endpoint2.lower : ℝ) (endpoint2.upper : ℝ) :=
  endpoint2.bounds endpoint2_valid

def endpoint3 : ExpEndpointCertificate :=
  ⟨(9009/512 : ℚ), 20, (665267167777429205/1152921504606846976 : ℚ), (332633583888714603/576460752303423488 : ℚ), (6576926313/288230376151711744 : ℚ), (26307705253/1152921504606846976 : ℚ)⟩
theorem endpoint3_valid : endpoint3.Valid := by decide +kernel
theorem endpoint3_bounds :
    Bounds (Real.exp (-(endpoint3.q : ℝ)))
      (endpoint3.lower : ℝ) (endpoint3.upper : ℝ) :=
  endpoint3.bounds endpoint3_valid

def endpoint4 : ExpEndpointCertificate :=
  ⟨(4629/256 : ℚ), 20, (655233042297025821/1152921504606846976 : ℚ), (327616521148512911/576460752303423488 : ℚ), (16176082245/1152921504606846976 : ℚ), (8088041123/576460752303423488 : ℚ)⟩
theorem endpoint4_valid : endpoint4.Valid := by decide +kernel
theorem endpoint4_bounds :
    Bounds (Real.exp (-(endpoint4.q : ℝ)))
      (endpoint4.lower : ℝ) (endpoint4.upper : ℝ) :=
  endpoint4.bounds endpoint4_valid

def endpoint5 : ExpEndpointCertificate :=
  ⟨(32/1 : ℚ), 20, (26508507426831583/72057594037927936 : ℚ), (212068059414652665/576460752303423488 : ℚ), (1825/144115188075855872 : ℚ), (14601/1152921504606846976 : ℚ)⟩
theorem endpoint5_valid : endpoint5.Valid := by decide +kernel
theorem endpoint5_bounds :
    Bounds (Real.exp (-(endpoint5.q : ℝ)))
      (endpoint5.lower : ℝ) (endpoint5.upper : ℝ) :=
  endpoint5.bounds endpoint5_valid

end SparseLowerTail.Numerics.WideExpSmoke
