import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverNearOne
import Lean

/-! Untrusted search input; the actual job expressions and dyadic constants.
No exported number or search success flag is a formal certificate. -/
open Lean SparseLowerTail SparseLowerTail.Numerics SparseLowerTail.Section05
open SparseLowerTail.Section05.CoverGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def encodeCoverExpr {n : Nat} : PolynomialExpr n → Json
  | .rational q => Json.arr #[toJson "r",toJson q.num,toJson q.den]
  | .var i => Json.arr #[toJson "v",toJson i.val]
  | .add e f => Json.arr #[toJson "+",encodeCoverExpr e,encodeCoverExpr f]
  | .neg e => Json.arr #[toJson "-",encodeCoverExpr e]
  | .mul e f => Json.arr #[toJson "*",encodeCoverExpr e,encodeCoverExpr f]

instance : Inhabited DyadicInterval := ⟨⟨0,0⟩⟩

def encodeCoverInterval (x : DyadicInterval) : Json :=
  Json.arr #[toJson x.lower,toJson x.upper]
def encodeCoverRat (x : Rat) : Json := Json.arr #[toJson x.num,toJson x.den]

-- Normalize the finite coefficient tables before executing the serializer.
-- Evaluating their nested Fin.cases through the interpreter is prohibitively
-- slow at high indices. This macro only prepares UNTRUSTED search input.
open Lean Elab Term Meta
elab "kernel_reduced% " t:term : term => do
  let e ← Term.elabTerm t none
  withTransparency .all <| Meta.reduce e

#eval IO.println (Json.mkObj [("value",encodeCoverExpr apexCertificateExpr)]).compress
#eval IO.println (Json.mkObj [("gradient_index",toJson (0:Nat)), ("expr",encodeCoverExpr (kernel_reduced% (coverGradientExpr 0))) ]).compress
#eval IO.println (Json.mkObj [("gradient_index",toJson (1:Nat)), ("expr",encodeCoverExpr (kernel_reduced% (coverGradientExpr 1))) ]).compress
#eval IO.println (Json.mkObj [("gradient_index",toJson (2:Nat)), ("expr",encodeCoverExpr (kernel_reduced% (coverGradientExpr 2))) ]).compress
#eval IO.println (Json.mkObj [("hessian_indices",toJson ([0,0]:List Nat)), ("expr",encodeCoverExpr (kernel_reduced% (coverHessianExpr 0 0))) ]).compress
#eval IO.println (Json.mkObj [("hessian_indices",toJson ([0,1]:List Nat)), ("expr",encodeCoverExpr (kernel_reduced% (coverHessianExpr 0 1))) ]).compress
#eval IO.println (Json.mkObj [("hessian_indices",toJson ([0,2]:List Nat)), ("expr",encodeCoverExpr (kernel_reduced% (coverHessianExpr 0 2))) ]).compress
#eval IO.println (Json.mkObj [("hessian_indices",toJson ([1,0]:List Nat)), ("expr",encodeCoverExpr (kernel_reduced% (coverHessianExpr 1 0))) ]).compress
#eval IO.println (Json.mkObj [("hessian_indices",toJson ([1,1]:List Nat)), ("expr",encodeCoverExpr (kernel_reduced% (coverHessianExpr 1 1))) ]).compress
#eval IO.println (Json.mkObj [("hessian_indices",toJson ([1,2]:List Nat)), ("expr",encodeCoverExpr (kernel_reduced% (coverHessianExpr 1 2))) ]).compress
#eval IO.println (Json.mkObj [("hessian_indices",toJson ([2,0]:List Nat)), ("expr",encodeCoverExpr (kernel_reduced% (coverHessianExpr 2 0))) ]).compress
#eval IO.println (Json.mkObj [("hessian_indices",toJson ([2,1]:List Nat)), ("expr",encodeCoverExpr (kernel_reduced% (coverHessianExpr 2 1))) ]).compress
#eval IO.println (Json.mkObj [("hessian_indices",toJson ([2,2]:List Nat)), ("expr",encodeCoverExpr (kernel_reduced% (coverHessianExpr 2 2))) ]).compress

def jobEnvironment0 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 0 23)]
#eval let env := jobEnvironment0
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (0:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 0).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 0).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 0).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment1 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 1 23)]
#eval let env := jobEnvironment1
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (1:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 1).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 1).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 1).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment2 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 2 23)]
#eval let env := jobEnvironment2
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (2:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 2).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 2).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 2).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment3 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 3 23)]
#eval let env := jobEnvironment3
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (3:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 3).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 3).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 3).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment4 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 4 23)]
#eval let env := jobEnvironment4
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (4:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 4).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 4).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 4).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment5 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 5 23)]
#eval let env := jobEnvironment5
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (5:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 5).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 5).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 5).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment6 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 6 23)]
#eval let env := jobEnvironment6
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (6:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 6).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 6).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 6).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment7 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 7 23)]
#eval let env := jobEnvironment7
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (7:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 7).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 7).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 7).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment8 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 8 23)]
#eval let env := jobEnvironment8
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (8:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 8).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 8).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 8).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment9 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 9 23)]
#eval let env := jobEnvironment9
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (9:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 9).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 9).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 9).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment10 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 10 23)]
#eval let env := jobEnvironment10
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (10:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 10).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 10).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 10).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment11 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 11 23)]
#eval let env := jobEnvironment11
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (11:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 11).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 11).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 11).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment12 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 12 23)]
#eval let env := jobEnvironment12
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (12:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 12).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 12).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 12).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment13 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 13 23)]
#eval let env := jobEnvironment13
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (13:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 13).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 13).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 13).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment14 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 14 23)]
#eval let env := jobEnvironment14
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (14:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 14).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 14).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 14).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment15 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 15 23)]
#eval let env := jobEnvironment15
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (15:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 15).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 15).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 15).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment16 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 16 23)]
#eval let env := jobEnvironment16
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (16:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 16).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 16).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 16).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment17 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 17 23)]
#eval let env := jobEnvironment17
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (17:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 17).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 17).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 17).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment18 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 18 23)]
#eval let env := jobEnvironment18
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (18:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 18).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 18).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 18).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment19 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 19 23)]
#eval let env := jobEnvironment19
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (19:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 19).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 19).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 19).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment20 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 20 23)]
#eval let env := jobEnvironment20
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (20:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 20).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 20).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 20).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment21 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 21 23)]
#eval let env := jobEnvironment21
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (21:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 21).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 21).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 21).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment22 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 22 23)]
#eval let env := jobEnvironment22
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (22:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 22).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 22).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 22).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment23 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 23 23)]
#eval let env := jobEnvironment23
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (23:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 23).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 23).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 23).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment24 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 24 23)]
#eval let env := jobEnvironment24
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (24:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 24).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 24).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 24).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment25 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 25 23)]
#eval let env := jobEnvironment25
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (25:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 25).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 25).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 25).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment26 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 26 23)]
#eval let env := jobEnvironment26
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (26:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 26).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 26).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 26).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment27 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 27 23)]
#eval let env := jobEnvironment27
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (27:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 27).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 27).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 27).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment28 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 28 23)]
#eval let env := jobEnvironment28
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (28:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 28).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 28).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 28).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment29 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 29 23)]
#eval let env := jobEnvironment29
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (29:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 29).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 29).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 29).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment30 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 30 23)]
#eval let env := jobEnvironment30
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (30:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 30).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 30).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 30).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment31 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 31 23)]
#eval let env := jobEnvironment31
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (31:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 31).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 31).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 31).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment32 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 32 23)]
#eval let env := jobEnvironment32
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (32:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 32).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 32).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 32).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment33 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 33 23)]
#eval let env := jobEnvironment33
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (33:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 33).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 33).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 33).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment34 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 34 23)]
#eval let env := jobEnvironment34
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (34:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 34).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 34).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 34).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress

def jobEnvironment35 : Array DyadicInterval := #[
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 0),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 1),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 2),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 3),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 4),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 5),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 6),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 7),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 8),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 9),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 10),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 11),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 12),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 13),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 14),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 15),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 16),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 17),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 18),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 19),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 20),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 21),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 22),
  kernel_reduced% (RefinedCover.nonapexBoxIntervals CoverNearOne.box 35 23)]
#eval let env := jobEnvironment35
      let value := apexCertificateExpr.dyadicEval (fun i => env[i.val]!)
      IO.println (Json.mkObj [("job",Json.mkObj [
        ("index",toJson (35:Nat)),
        ("cell",toJson (kernel_reduced% (nonapexCell 35).val)),
        ("vertex",Json.arr #[encodeCoverRat (kernel_reduced% (nonapexVertexQ 35).1),
          encodeCoverRat (kernel_reduced% (nonapexVertexQ 35).2)]),
        ("constants",Json.arr ((env.extract 6 11).map encodeCoverInterval)),
        ("coefficients",Json.arr ((env.extract 11 23).map encodeCoverInterval)),
        ("lambda",encodeCoverInterval env[23]!),
        ("near_one_reference",encodeCoverInterval value)])]).compress
