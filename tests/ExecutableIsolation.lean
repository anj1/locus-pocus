import CertifiedTopology.ComputedInput

open CertifiedTopology ExecutableIsolation

def finiteCount : Roots → Option Nat
  | .all => none
  | .finite roots => some roots.length

#guard finiteCount (isolate RealModel.rational []).roots == none
#guard finiteCount (isolate RealModel.rational [1, 0, 1]).roots == some 0
def repeated : List ℚ :=
  DensePolynomial.mul (DensePolynomial.mul [-2, 0, 1] [-2, 0, 1]) [1, -2, 1]

#guard finiteCount (isolate RealModel.rational repeated).roots == some 3
#guard finiteCount (isolate RealModel.rational [0, -1, 0, 1]).roots == some 3

def nested : Option (Bool × Option Nat) := do
  let r ← ComputedInput.selectRoot RealModel.rational ⟨[-2, 0, 1], 1⟩
  let a := AlgebraicField.generator r
  let rs := isolate (AlgebraicField.realModel r) [-a, 0, 1]
  return (decide (a^ (2 : Nat) = 2 ∧ 1 < a ∧ a < 3 / 2), finiteCount rs.roots)

#guard nested == some (true, some 2)

open CADDecision

def halfOpen : Prenex ℚ 1 :=
  .matrix ((rationalCut (K := ℚ) 0 .below).not.and (rationalCut 1 .below))

def halfOpenStrata := stratify RealModel.rational halfOpen

#guard halfOpenStrata.strata.map Stratum.dimension == [1, 0]
#guard (List.finRange halfOpenStrata.strata.length).map
  (fun i => (List.finRange halfOpenStrata.strata.length).map (halfOpenStrata.incidence i)) ==
  [[true, true], [false, true]]
