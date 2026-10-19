import SparseLowerTail.Section05.ApexRefinedPrimitives
import SparseLowerTail.Section05.CoverCoefficientData
open SparseLowerTail.Section05 SparseLowerTail.Section05.CoverGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
/- One executable proposal loop. Its output is not a trusted proof input. -/
#eval do
  for i in List.finRange 4 do
    for j in List.finRange 4 do
      IO.println (repr ((apexTangencyMatrixExpr i j).dyadicEval apexRefinedPrimitiveIntervals))
  for i in List.finRange 6 do
    for j in List.finRange 4 do
      IO.println (repr ((apexTangencyRhsExpr (fixedCellThetaQ (i.castAdd 6))
        (cellLambdaQ (i.castAdd 6)) j).dyadicEval apexRefinedPrimitiveIntervals))
