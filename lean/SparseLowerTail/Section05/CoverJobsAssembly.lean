import SparseLowerTail.Section05.ApexCoverAssembly
import SparseLowerTail.Section05.CoverJobIntervals

/-! Exact integration of all 36 nonapex jobs and six apex fans.
The numerical job results remain explicit internal obligations. -/
noncomputable section
namespace SparseLowerTail.Section05
open Section02 Section04 CoverGeometry
namespace CoverGeometry
theorem cellVertex_eq_fanApex_or_job (i : Fin 12) (v : ℝ×ℝ)
    (hv : v∈cellVertices i) :
    (∃ k : Fin 6,i=k.castAdd 6 ∧ v=criticalPoint) ∨ ∃ j : Fin 36,nonapexCell j=i ∧ nonapexVertex j=v := by
  fin_cases i
  · change v∈cellVertices 0 at hv
    rw [cellVertices0_eq] at hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact Or.inl ⟨0,rfl,rfl⟩
    · exact Or.inr ⟨0,rfl,nonapexVertex0_eq⟩
    · exact Or.inr ⟨1,rfl,nonapexVertex1_eq⟩
  · change v∈cellVertices 1 at hv
    rw [cellVertices1_eq] at hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact Or.inl ⟨1,rfl,rfl⟩
    · exact Or.inr ⟨2,rfl,nonapexVertex2_eq⟩
    · exact Or.inr ⟨3,rfl,nonapexVertex3_eq⟩
  · change v∈cellVertices 2 at hv
    rw [cellVertices2_eq] at hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact Or.inl ⟨2,rfl,rfl⟩
    · exact Or.inr ⟨4,rfl,nonapexVertex4_eq⟩
    · exact Or.inr ⟨5,rfl,nonapexVertex5_eq⟩
  · change v∈cellVertices 3 at hv
    rw [cellVertices3_eq] at hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact Or.inl ⟨3,rfl,rfl⟩
    · exact Or.inr ⟨6,rfl,nonapexVertex6_eq⟩
    · exact Or.inr ⟨7,rfl,nonapexVertex7_eq⟩
  · change v∈cellVertices 4 at hv
    rw [cellVertices4_eq] at hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact Or.inl ⟨4,rfl,rfl⟩
    · exact Or.inr ⟨8,rfl,nonapexVertex8_eq⟩
    · exact Or.inr ⟨9,rfl,nonapexVertex9_eq⟩
  · change v∈cellVertices 5 at hv
    rw [cellVertices5_eq] at hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact Or.inl ⟨5,rfl,rfl⟩
    · exact Or.inr ⟨10,rfl,nonapexVertex10_eq⟩
    · exact Or.inr ⟨11,rfl,nonapexVertex11_eq⟩
  · change v∈cellVertices 6 at hv
    rw [cellVertices6_eq] at hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨12,rfl,nonapexVertex12_eq⟩
    · exact Or.inr ⟨13,rfl,nonapexVertex13_eq⟩
    · exact Or.inr ⟨14,rfl,nonapexVertex14_eq⟩
    · exact Or.inr ⟨15,rfl,nonapexVertex15_eq⟩
  · change v∈cellVertices 7 at hv
    rw [cellVertices7_eq] at hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨16,rfl,nonapexVertex16_eq⟩
    · exact Or.inr ⟨17,rfl,nonapexVertex17_eq⟩
    · exact Or.inr ⟨18,rfl,nonapexVertex18_eq⟩
    · exact Or.inr ⟨19,rfl,nonapexVertex19_eq⟩
  · change v∈cellVertices 8 at hv
    rw [cellVertices8_eq] at hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨20,rfl,nonapexVertex20_eq⟩
    · exact Or.inr ⟨21,rfl,nonapexVertex21_eq⟩
    · exact Or.inr ⟨22,rfl,nonapexVertex22_eq⟩
    · exact Or.inr ⟨23,rfl,nonapexVertex23_eq⟩
  · change v∈cellVertices 9 at hv
    rw [cellVertices9_eq] at hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨24,rfl,nonapexVertex24_eq⟩
    · exact Or.inr ⟨25,rfl,nonapexVertex25_eq⟩
    · exact Or.inr ⟨26,rfl,nonapexVertex26_eq⟩
    · exact Or.inr ⟨27,rfl,nonapexVertex27_eq⟩
  · change v∈cellVertices 10 at hv
    rw [cellVertices10_eq] at hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨28,rfl,nonapexVertex28_eq⟩
    · exact Or.inr ⟨29,rfl,nonapexVertex29_eq⟩
    · exact Or.inr ⟨30,rfl,nonapexVertex30_eq⟩
    · exact Or.inr ⟨31,rfl,nonapexVertex31_eq⟩
  · change v∈cellVertices 11 at hv
    rw [cellVertices11_eq] at hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨32,rfl,nonapexVertex32_eq⟩
    · exact Or.inr ⟨33,rfl,nonapexVertex33_eq⟩
    · exact Or.inr ⟨34,rfl,nonapexVertex34_eq⟩
    · exact Or.inr ⟨35,rfl,nonapexVertex35_eq⟩

end CoverGeometry

/-- The wide endpoint range covers every support cutoff in the actual table. -/
theorem all_cell_cutoffs_in_wide_range (i : Fin 12) : 0≤cellQ i ∧ cellQ i≤32 := by
  fin_cases i <;> norm_num [cellQ]

/-- Every nonapex job on its entire sorted logarithmic domain. -/
def NonapexJobResults : Prop := ∀j : Fin 36,
  ∀q∈orderedLogDomain (cellQ (nonapexCell j)),
    0<logCertificate (coverCellTheta (nonapexCell j))
      (cellLambda (nonapexCell j)) (nonapexVertex j) q

/-- Every apex fan, including its zero pattern, on the entire sorted domain. -/
def ApexJobResults : Prop := ∀i : Fin 6,
  ∀q∈orderedLogDomain (cellQ (i.castAdd 6)),ApexLeafConclusion i q

theorem verifiedCover_of_ordered_jobs (hn : NonapexJobResults) (ha : ApexJobResults) :
    VerifiedCertificateCover (certificateCell coverCellTheta) := by
  apply verifiedCover_of_positivity
  · intro i v hv hne u hu
    rcases cellVertex_eq_apex_or_job i v hv with he | ⟨j,hj,hv⟩
    · exact (hne he).elim
    · have hp := coverCertificate_pos_of_orderedLog
        (coverCellTheta (nonapexCell j)) (cellLambda (nonapexCell j))
        (nonapexVertex j) (cellQ (nonapexCell j)) (hn j) u
        (by simpa only [hj] using hu)
      simpa only [hj,hv] using hp
  · intro i hv u hu
    rcases cellVertex_eq_fanApex_or_job i criticalPoint hv with ⟨k,hi,_⟩ | ⟨j,hj,hv⟩
    · rw [hi,coverCellTheta_fan]
      exact (apex_nonneg_patterns_of_ordered k _ (ha k) u
        (by simpa only [hi] using hu)).1
    · have hp := coverCertificate_pos_of_orderedLog
        (coverCellTheta (nonapexCell j)) (cellLambda (nonapexCell j))
        (nonapexVertex j) (cellQ (nonapexCell j)) (hn j) u
        (by simpa only [hj] using hu)
      simpa only [hj,hv] using hp.le

/-- Complete critical classification from the 42 full-domain numerical jobs.
The four classical inputs are explicit; neither job family is assumed classical. -/
theorem criticalClassification_of_ordered_jobs
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hcount : ClassicalTriangleCounting) (hSampling : UniformSampling)
    (hn : NonapexJobResults) (ha : ApexJobResults) : CriticalClassification :=
  criticalClassification_of_verifiedCover hdyadic hcompact hcount hSampling
    (verifiedCover_of_ordered_jobs hn ha) (criticalApexCertificate_of_ordered 0 (ha 0))

end SparseLowerTail.Section05
