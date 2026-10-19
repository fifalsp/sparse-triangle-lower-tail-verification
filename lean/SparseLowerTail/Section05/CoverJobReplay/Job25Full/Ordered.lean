import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00001
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00002
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00003
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00004
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00005
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00006
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00007
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00008
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00009
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00010
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00011
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00012
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00013
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00014
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00015
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00016
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00017
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00018
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00019
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00020
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00021
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00022
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00023
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00024
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00025
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00026
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00027
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00028
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00029
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00030
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00031
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00032
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00033
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00034
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00035
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00036
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00037
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00038
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00039
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00040
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00041
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Coverage00042

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def initialBox : LogBox := ⟨![(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(1607/256 : ℚ),(1607/256 : ℚ)]⟩
def chunkTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (some Coverage00000.initialBox)) (.leaf (some Coverage00032.initialBox))) (.branch (.leaf (some Coverage00016.initialBox)) (.leaf (none)))) (.branch (.branch (.leaf (some Coverage00008.initialBox)) (.leaf (some Coverage00040.initialBox))) (.branch (.leaf (some Coverage00024.initialBox)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some Coverage00004.initialBox)) (.leaf (some Coverage00036.initialBox))) (.branch (.leaf (some Coverage00020.initialBox)) (.leaf (none)))) (.branch (.branch (.leaf (some Coverage00012.initialBox)) (.leaf (none))) (.branch (.leaf (some Coverage00028.initialBox)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some Coverage00002.initialBox)) (.leaf (some Coverage00034.initialBox))) (.branch (.leaf (some Coverage00018.initialBox)) (.leaf (none)))) (.branch (.branch (.leaf (some Coverage00010.initialBox)) (.leaf (some Coverage00042.initialBox))) (.branch (.leaf (some Coverage00026.initialBox)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some Coverage00006.initialBox)) (.leaf (some Coverage00038.initialBox))) (.branch (.leaf (some Coverage00022.initialBox)) (.leaf (none)))) (.branch (.branch (.leaf (some Coverage00014.initialBox)) (.leaf (none))) (.branch (.leaf (some Coverage00030.initialBox)) (.leaf (none))))))) (.branch (.branch (.branch (.branch (.branch (.leaf (some Coverage00001.initialBox)) (.leaf (some Coverage00033.initialBox))) (.branch (.leaf (some Coverage00017.initialBox)) (.leaf (none)))) (.branch (.branch (.leaf (some Coverage00009.initialBox)) (.leaf (some Coverage00041.initialBox))) (.branch (.leaf (some Coverage00025.initialBox)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some Coverage00005.initialBox)) (.leaf (some Coverage00037.initialBox))) (.branch (.leaf (some Coverage00021.initialBox)) (.leaf (none)))) (.branch (.branch (.leaf (some Coverage00013.initialBox)) (.leaf (none))) (.branch (.leaf (some Coverage00029.initialBox)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some Coverage00003.initialBox)) (.leaf (some Coverage00035.initialBox))) (.branch (.leaf (some Coverage00019.initialBox)) (.leaf (none)))) (.branch (.branch (.leaf (some Coverage00011.initialBox)) (.leaf (none))) (.branch (.leaf (some Coverage00027.initialBox)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some Coverage00007.initialBox)) (.leaf (some Coverage00039.initialBox))) (.branch (.leaf (some Coverage00023.initialBox)) (.leaf (none)))) (.branch (.branch (.leaf (some Coverage00015.initialBox)) (.leaf (none))) (.branch (.leaf (some Coverage00031.initialBox)) (.leaf (none))))))))
def subdivision : CoverReplayTree := (.split 0 (.split 0 (.split 0 (.leaf 0) (.split 1 (.split 0 (.leaf 1) (.leaf 2)) (.split 2 (.split 0 (.leaf 3) (.leaf 4)) (.leaf 5)))) (.split 1 (.split 0 (.split 1 (.split 0 (.leaf 6) (.leaf 7)) (.split 2 (.split 0 (.leaf 8) (.leaf 9)) (.leaf 10))) (.split 1 (.split 0 (.leaf 11) (.leaf 12)) (.leaf 13))) (.split 2 (.split 0 (.leaf 14) (.leaf 15)) (.leaf 16)))) (.split 1 (.split 0 (.split 1 (.split 0 (.split 1 (.leaf 17) (.leaf 18)) (.split 1 (.leaf 19) (.leaf 20))) (.split 2 (.split 0 (.leaf 21) (.leaf 22)) (.leaf 23))) (.split 1 (.split 0 (.leaf 24) (.leaf 25)) (.split 2 (.split 0 (.leaf 26) (.leaf 27)) (.leaf 28)))) (.split 2 (.split 0 (.split 2 (.split 0 (.leaf 29) (.leaf 30)) (.split 0 (.leaf 31) (.leaf 32))) (.split 1 (.split 2 (.split 0 (.leaf 33) (.leaf 34)) (.split 0 (.leaf 35) (.leaf 36))) (.split 2 (.split 0 (.leaf 37) (.leaf 38)) (.leaf 39)))) (.split 0 (.leaf 40) (.split 1 (.leaf 41) (.leaf 42))))))
theorem valid : subdivision.Valid chunkTable.get initialBox := by decide +kernel
theorem chunk_proofs (Q : ℝ) : chunkTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨⟨(fun _ hq hord => Coverage00000.covered _ hq hord),(fun _ hq hord => Coverage00032.covered _ hq hord)⟩,⟨(fun _ hq hord => Coverage00016.covered _ hq hord),True.intro⟩⟩,⟨⟨(fun _ hq hord => Coverage00008.covered _ hq hord),(fun _ hq hord => Coverage00040.covered _ hq hord)⟩,⟨(fun _ hq hord => Coverage00024.covered _ hq hord),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq hord => Coverage00004.covered _ hq hord),(fun _ hq hord => Coverage00036.covered _ hq hord)⟩,⟨(fun _ hq hord => Coverage00020.covered _ hq hord),True.intro⟩⟩,⟨⟨(fun _ hq hord => Coverage00012.covered _ hq hord),True.intro⟩,⟨(fun _ hq hord => Coverage00028.covered _ hq hord),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq hord => Coverage00002.covered _ hq hord),(fun _ hq hord => Coverage00034.covered _ hq hord)⟩,⟨(fun _ hq hord => Coverage00018.covered _ hq hord),True.intro⟩⟩,⟨⟨(fun _ hq hord => Coverage00010.covered _ hq hord),(fun _ hq hord => Coverage00042.covered _ hq hord)⟩,⟨(fun _ hq hord => Coverage00026.covered _ hq hord),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq hord => Coverage00006.covered _ hq hord),(fun _ hq hord => Coverage00038.covered _ hq hord)⟩,⟨(fun _ hq hord => Coverage00022.covered _ hq hord),True.intro⟩⟩,⟨⟨(fun _ hq hord => Coverage00014.covered _ hq hord),True.intro⟩,⟨(fun _ hq hord => Coverage00030.covered _ hq hord),True.intro⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨(fun _ hq hord => Coverage00001.covered _ hq hord),(fun _ hq hord => Coverage00033.covered _ hq hord)⟩,⟨(fun _ hq hord => Coverage00017.covered _ hq hord),True.intro⟩⟩,⟨⟨(fun _ hq hord => Coverage00009.covered _ hq hord),(fun _ hq hord => Coverage00041.covered _ hq hord)⟩,⟨(fun _ hq hord => Coverage00025.covered _ hq hord),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq hord => Coverage00005.covered _ hq hord),(fun _ hq hord => Coverage00037.covered _ hq hord)⟩,⟨(fun _ hq hord => Coverage00021.covered _ hq hord),True.intro⟩⟩,⟨⟨(fun _ hq hord => Coverage00013.covered _ hq hord),True.intro⟩,⟨(fun _ hq hord => Coverage00029.covered _ hq hord),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq hord => Coverage00003.covered _ hq hord),(fun _ hq hord => Coverage00035.covered _ hq hord)⟩,⟨(fun _ hq hord => Coverage00019.covered _ hq hord),True.intro⟩⟩,⟨⟨(fun _ hq hord => Coverage00011.covered _ hq hord),True.intro⟩,⟨(fun _ hq hord => Coverage00027.covered _ hq hord),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq hord => Coverage00007.covered _ hq hord),(fun _ hq hord => Coverage00039.covered _ hq hord)⟩,⟨(fun _ hq hord => Coverage00023.covered _ hq hord),True.intro⟩⟩,⟨⟨(fun _ hq hord => Coverage00015.covered _ hq hord),True.intro⟩,⟨(fun _ hq hord => Coverage00031.covered _ hq hord),True.intro⟩⟩⟩⟩⟩⟩
theorem ordered {q : EdgeTriple}
    (hq : q ∈ orderedLogDomain (CoverGeometry.cellQ (CoverGeometry.nonapexCell 25))) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q := by
  have hc := orderedLogDomain_subset_cube _ hq
  apply subdivision.sound_table (chunk_proofs _) valid q ?_ hq
  intro i
  fin_cases i
  · simpa [initialBox,edgeCoordinate,CoverGeometry.cellQ,CoverGeometry.nonapexCell] using hc.1
  · simpa [initialBox,edgeCoordinate,CoverGeometry.cellQ,CoverGeometry.nonapexCell] using hc.2.1
  · simpa [initialBox,edgeCoordinate,CoverGeometry.cellQ,CoverGeometry.nonapexCell] using hc.2.2

end SparseLowerTail.Section05.CoverJobReplay.Job25Full
