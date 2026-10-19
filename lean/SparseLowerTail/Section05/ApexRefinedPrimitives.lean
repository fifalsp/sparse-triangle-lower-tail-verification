import SparseLowerTail.Section04.RefinedThresholdDigits
import SparseLowerTail.Section05.ApexTangencyExpressions

/-! Refined bounds derived from the actual crossing, not assumed decimal constants. -/
noncomputable section
namespace SparseLowerTail.Section05
open Numerics Section04

def apexRefinedPrimitiveBounds : Fin 9 → RationalInterval := ![⟨(2036271405980614055645653/500000000000000000000000 : ℚ),(509067851495153536569091/125000000000000000000000 : ℚ)⟩,⟨(81643762803369005197153/500000000000000000000000 : ℚ),(10205470350421127629233/62500000000000000000000 : ℚ)⟩,⟨(17034019083235291753671/1000000000000000000000000 : ℚ),(2129252385404411855163/125000000000000000000000 : ℚ)⟩,⟨(849346944307562254223/1000000000000000000000 : ℚ),(106168368038445285141/125000000000000000000 : ℚ)⟩,⟨(9217366869665912798417/1000000000000000000000000 : ℚ),(1843473373933183010703/200000000000000000000000 : ℚ)⟩,⟨(461560688742150414785753/500000000000000000000000 : ℚ),(461560688742150470810233/500000000000000000000000 : ℚ)⟩,⟨(282156954144062429294093/25000000000000000000000 : ℚ),(5643139082881249193887473/500000000000000000000000 : ℚ)⟩,⟨(86638096339079754597667/200000000000000000000000 : ℚ),(108297620423849696996163/250000000000000000000000 : ℚ)⟩,⟨(14461867245552130416101/31250000000000000000000 : ℚ),(231389875928834105895051/500000000000000000000000 : ℚ)⟩]

theorem apexRefinedPrimitiveBounds_contains (i : Fin 9) :
    (apexRefinedPrimitiveBounds i).contains (apexPrimitiveValues i) := by
  have hz : transitionParameter∈Set.Icc Refined.digitZLower Refined.digitZUpper :=
    ⟨Refined.transitionParameter_digits.1.le,Refined.transitionParameter_digits.2.le⟩
  have hp := Refined.tight_branch_ranges hz
  have hA : Bounds criticalA (17034019083235291753671/1000000000000000000000000 : ℝ) (2129252385404411855163/125000000000000000000000 : ℝ) := hp.1
  have hB : Bounds criticalB (849346944307562254223/1000000000000000000000 : ℝ) (106168368038445285141/125000000000000000000 : ℝ) := hp.2.1
  have hL := Refined.digit_log_range hz
  have hE := Refined.digit_exponent_range hz
  have hqa : -Real.log criticalA=branchLog transitionParameter+
      2*transitionParameter*branchLog transitionParameter/(1-transitionParameter)^2 := by
    rw [criticalA,branchA,Real.log_mul (ne_of_gt transitionParameter_mem_Ioo.1)
      (ne_of_gt (branchB_pos _)),log_branchB,branchLog_eq_neg_log]
    ring
  have hqb : -Real.log criticalB=2*transitionParameter*branchLog transitionParameter/(1-transitionParameter)^2 := by
    rw [criticalB,log_branchB]
    ring
  have h1 : Bounds ((branchLog transitionParameter)+(2*transitionParameter*branchLog transitionParameter/(1-transitionParameter)^2)) (2036271405980614055645653/500000000000000000000000 : ℝ) (509067851495153536569091/125000000000000000000000 : ℝ) := by
    exact (hL.add hE).weaken (by norm_num) (by norm_num)
  have hQA : Bounds (-Real.log criticalA) (2036271405980614055645653/500000000000000000000000 : ℝ) (509067851495153536569091/125000000000000000000000 : ℝ) := by
    rw [hqa]
    exact h1
  have hQB : Bounds (-Real.log criticalB) (81643762803369005197153/500000000000000000000000 : ℝ) (10205470350421127629233/62500000000000000000000 : ℝ) := by
    rw [hqb]
    exact hE
  have h2 : Bounds ((-Real.log criticalA)+(1 : ℝ)) (2536271405980614055645653/500000000000000000000000 : ℝ) (634067851495153536569091/125000000000000000000000 : ℝ) := by
    exact (hQA.add (Bounds.refl (1 : ℝ))).weaken (by norm_num) (by norm_num)
  have h3 : Bounds (criticalA*((-Real.log criticalA)+(1 : ℝ))) (86405791059475567797649/1000000000000000000000000 : ℝ) (86405791059475586547411/1000000000000000000000000 : ℝ) := by
    exact (hA.mul_nonneg h2 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h4 : Bounds ((1 : ℝ)-(criticalA*((-Real.log criticalA)+(1 : ℝ)))) (913594208940524413452589/1000000000000000000000000 : ℝ) (913594208940524432202351/1000000000000000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub h3).weaken (by norm_num) (by norm_num)
  have h5 : Bounds ((-Real.log criticalB)+(1 : ℝ)) (581643762803369005197153/500000000000000000000000 : ℝ) (72705470350421127629233/62500000000000000000000 : ℝ) := by
    exact (hQB.add (Bounds.refl (1 : ℝ))).weaken (by norm_num) (by norm_num)
  have h6 : Bounds (criticalB*((-Real.log criticalB)+(1 : ℝ))) (247008676306297002155537/250000000000000000000000 : ℝ) (247008676306297016705531/250000000000000000000000 : ℝ) := by
    exact (hB.mul_nonneg h5 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h7 : Bounds ((1 : ℝ)-(criticalB*((-Real.log criticalB)+(1 : ℝ)))) (2991323693702983294469/250000000000000000000000 : ℝ) (2991323693702997844463/250000000000000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub h6).weaken (by norm_num) (by norm_num)
  have h8 : Bounds (criticalA*criticalA) (290157806128024089333/1000000000000000000000000 : ℝ) (290157806128024194523/1000000000000000000000000 : ℝ) := by
    exact (hA.mul_nonneg hA (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h9 : Bounds ((criticalA*criticalA)*criticalA) (4942553606734448417/1000000000000000000000000 : ℝ) (2471276803367225553/500000000000000000000000 : ℝ) := by
    exact (h8.mul_nonneg hA (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h10 : Bounds ((3 : ℝ)*criticalA) (51102057249705875261013/1000000000000000000000000 : ℝ) (6387757156213235565489/125000000000000000000000 : ℝ) := by
    exact ((Bounds.refl (3 : ℝ)).mul_nonneg hA (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h11 : Bounds (criticalB*criticalB) (360695115902296628761353/500000000000000000000000 : ℝ) (360695115902296651613033/500000000000000000000000 : ℝ) := by
    exact (hB.mul_nonneg hB (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h12 : Bounds (((3 : ℝ)*criticalA)*(criticalB*criticalB)) (9216131231264229186313/250000000000000000000000 : ℝ) (36864524925056925762953/1000000000000000000000000 : ℝ) := by
    exact (h10.mul_nonneg h11 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h13 : Bounds (((criticalA*criticalA)*criticalA)+(((3 : ℝ)*criticalA)*(criticalB*criticalB))) (36869467478663651193669/1000000000000000000000000 : ℝ) (36869467478663660214059/1000000000000000000000000 : ℝ) := by
    exact (h9.add h12).weaken (by norm_num) (by norm_num)
  have h14 : Bounds ((((criticalA*criticalA)*criticalA)+(((3 : ℝ)*criticalA)*(criticalB*criticalB)))/(4 : ℝ)) (9217366869665912798417/1000000000000000000000000 : ℝ) (1843473373933183010703/200000000000000000000000 : ℝ) := by
    exact (h13.div_pos (Bounds.refl (4 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h15 : Bounds (criticalB-criticalA) (13004889456630108740339/15625000000000000000000 : ℝ) (832312925224326989374329/1000000000000000000000000 : ℝ) := by
    exact (hB.sub hA).weaken (by norm_num) (by norm_num)
  have h16 : Bounds (((1 : ℝ)-(criticalA*((-Real.log criticalA)+(1 : ℝ))))-((1 : ℝ)-(criticalB*((-Real.log criticalB)+(1 : ℝ))))) (901628914165712422074737/1000000000000000000000000 : ℝ) (36065156566628499960979/40000000000000000000000 : ℝ) := by
    exact (h4.sub h7).weaken (by norm_num) (by norm_num)
  have h17 : Bounds ((criticalB-criticalA)/(((1 : ℝ)-(criticalA*((-Real.log criticalA)+(1 : ℝ))))-((1 : ℝ)-(criticalB*((-Real.log criticalB)+(1 : ℝ)))))) (461560688742150414785753/500000000000000000000000 : ℝ) (461560688742150470810233/500000000000000000000000 : ℝ) := by
    exact (h15.div_pos h16 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h18 : Bounds (criticalA+criticalB) (866380963390797545976671/1000000000000000000000000 : ℝ) (108297620423849696996163/125000000000000000000000 : ℝ) := by
    exact (hA.add hB).weaken (by norm_num) (by norm_num)
  have h19 : Bounds ((criticalA+criticalB)/(2 : ℝ)) (86638096339079754597667/200000000000000000000000 : ℝ) (108297620423849696996163/250000000000000000000000 : ℝ) := by
    exact (h18.div_pos (Bounds.refl (2 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h20 : Bounds (((1 : ℝ)-(criticalA*((-Real.log criticalA)+(1 : ℝ))))+((1 : ℝ)-(criticalB*((-Real.log criticalB)+(1 : ℝ))))) (185111900743067269326093/200000000000000000000000 : ℝ) (925559503715336423580203/1000000000000000000000000 : ℝ) := by
    exact (h4.add h7).weaken (by norm_num) (by norm_num)
  have h21 : Bounds ((((1 : ℝ)-(criticalA*((-Real.log criticalA)+(1 : ℝ))))+((1 : ℝ)-(criticalB*((-Real.log criticalB)+(1 : ℝ)))))/(2 : ℝ)) (14461867245552130416101/31250000000000000000000 : ℝ) (231389875928834105895051/500000000000000000000000 : ℝ) := by
    exact (h20.div_pos (Bounds.refl (2 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have ht : Bounds criticalTriangle (9217366869665912798417/1000000000000000000000000 : ℝ) (1843473373933183010703/200000000000000000000000 : ℝ) := by
    convert h14 using 1
    change criticalTriangle=((((criticalA*criticalA)*criticalA)+(((3 : ℝ)*criticalA)*(criticalB*criticalB)))/(4 : ℝ))
    rw [show criticalTriangle=balancedTriangle criticalA criticalB from critical_pair_triangle.symm]
    unfold balancedTriangle
    ring
  have ho : Bounds criticalOmega (461560688742150414785753/500000000000000000000000 : ℝ) (461560688742150470810233/500000000000000000000000 : ℝ) := by
    convert h17 using 1
    unfold criticalOmega entropy
    ring
  have hm : Bounds criticalMean (86638096339079754597667/200000000000000000000000 : ℝ) (108297620423849696996163/250000000000000000000000 : ℝ) := by
    convert h19 using 1
  have hf : Bounds criticalCost (14461867245552130416101/31250000000000000000000 : ℝ) (231389875928834105895051/500000000000000000000000 : ℝ) := by
    convert h21 using 1
    rw [show criticalCost=balancedCost criticalA criticalB from critical_pair_cost.symm]
    unfold balancedCost entropy
    ring
  have hmu : Bounds (relaxationMultiplier criticalPoint) (282156954144062429294093/25000000000000000000000 : ℝ) (5643139082881249193887473/500000000000000000000000 : ℝ) := by
    rw [criticalMultiplier_eq_branchMu]
    exact hp.2.2
  fin_cases i
  · norm_num [apexRefinedPrimitiveBounds,RationalInterval.contains,apexPrimitiveValues] at ⊢
    exact hQA
  · norm_num [apexRefinedPrimitiveBounds,RationalInterval.contains,apexPrimitiveValues] at ⊢
    exact hQB
  · norm_num [apexRefinedPrimitiveBounds,RationalInterval.contains,apexPrimitiveValues] at ⊢
    exact hA
  · norm_num [apexRefinedPrimitiveBounds,RationalInterval.contains,apexPrimitiveValues] at ⊢
    exact hB
  · norm_num [apexRefinedPrimitiveBounds,RationalInterval.contains,apexPrimitiveValues] at ⊢
    exact ht
  · norm_num [apexRefinedPrimitiveBounds,RationalInterval.contains,apexPrimitiveValues] at ⊢
    exact ho
  · norm_num [apexRefinedPrimitiveBounds,RationalInterval.contains,apexPrimitiveValues] at ⊢
    exact hmu
  · norm_num [apexRefinedPrimitiveBounds,RationalInterval.contains,apexPrimitiveValues] at ⊢
    exact hm
  · norm_num [apexRefinedPrimitiveBounds,RationalInterval.contains,apexPrimitiveValues] at ⊢
    exact hf

def apexRefinedPrimitiveIntervals (i : Fin 9) : DyadicInterval :=
  DyadicInterval.ofRational (apexRefinedPrimitiveBounds i)

theorem apexRefinedPrimitiveIntervals_contains (i : Fin 9) :
    (apexRefinedPrimitiveIntervals i).contains (apexPrimitiveValues i) :=
  DyadicInterval.ofRational_contains (apexRefinedPrimitiveBounds_contains i)

end SparseLowerTail.Section05
