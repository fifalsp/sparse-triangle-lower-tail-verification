import SparseLowerTail.Section08.FamilyExteriorSmoke
import Lean

/-! Untrusted numerical-search input, exported from the actual checked
expression definitions. Acceptance still requires the Lean leaf checker. -/
open Lean SparseLowerTail SparseLowerTail.Numerics SparseLowerTail.Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def encodeRationalExpr {n : Nat} : RationalExpr n → Json
  | .rational q => Json.arr #[toJson "r",toJson q.num,toJson q.den]
  | .var i => Json.arr #[toJson "v",toJson i.val]
  | .add e f => Json.arr #[toJson "+",encodeRationalExpr e,encodeRationalExpr f]
  | .neg e => Json.arr #[toJson "-",encodeRationalExpr e]
  | .mul e f => Json.arr #[toJson "*",encodeRationalExpr e,encodeRationalExpr f]
  | .inv e => Json.arr #[toJson "/",encodeRationalExpr e]

def encodePolynomialExpr {n : Nat} : PolynomialExpr n → Json
  | .rational q => Json.arr #[toJson "r",toJson q.num,toJson q.den]
  | .var i => Json.arr #[toJson "v",toJson i.val]
  | .add e f => Json.arr #[toJson "+",encodePolynomialExpr e,encodePolynomialExpr f]
  | .neg e => Json.arr #[toJson "-",encodePolynomialExpr e]
  | .mul e f => Json.arr #[toJson "*",encodePolynomialExpr e,encodePolynomialExpr f]

def encodeRat (q : Rat) : Json := Json.arr #[toJson q.num,toJson q.den]

#eval IO.println (Json.mkObj [
  ("schema",toJson (1:Nat)),
  ("trust_status",toJson "Untrusted search input; Lean must check accepted leaves and coverage"),
  ("derivatives",Json.arr ((List.range 4).toArray.map fun n => Json.arr
    ((List.finRange 7).toArray.map fun i => encodeRationalExpr (FamilyCoeff.derivativeExpr i n)))),
  ("reference_smoke",Json.mkObj [
    ("value_lower",encodeRat FamilyExteriorSmoke.data.valueLower),
    ("gradient_upper",Json.arr ((List.finRange 3).toArray.map fun i => encodeRat (FamilyExteriorSmoke.data.gradientUpper i))),
    ("gradient_lower",Json.arr ((List.finRange 3).toArray.map fun i => encodeRat (FamilyExteriorSmoke.data.gradientLower i))),
    ("margin",encodeRat FamilyExteriorSmoke.leaf.margin)]),
  ("delta",encodeRationalExpr familyDeltaExpr),
  ("weights",Json.arr ((List.finRange 7).toArray.map fun i =>
    encodePolynomialExpr (FamilyWeightExpr.weights i))),
  ("gradient_weights",Json.arr ((List.finRange 3).toArray.map fun i => Json.arr
    ((List.finRange 7).toArray.map fun j => encodePolynomialExpr (FamilyWeightExpr.gradientWeights i j)))),
  ("hessian",Json.arr ((List.finRange 3).toArray.map fun i => Json.arr
    ((List.finRange 3).toArray.map fun j => encodePolynomialExpr (FamilyHessianExpr.entry i j))))
  ]).compress
