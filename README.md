# Certified topology of algebraic families

This Lean 4 project constructs sign-invariant cylindrical decompositions for several input classes. It also certifies how the topology of a quadratic zero fiber varies with a polynomial parameter. Parameter coordinates come first in the cylindrical order. Topological statements use the usual Euclidean topology.

| Input | Computation | Lean guarantee |
| --- | --- | --- |
| Boolean combinations of signs of products of affine forms, in any dimension | Exact projection and lifting over an ordered field. Executable over the rationals. | Every point belongs to a unique cell, each cell contains its sample, and all factor signs are constant there. The selected cells describe the formula exactly. Every real output cell is convex and contractible. |
| Finite lists of rational univariate polynomials, arbitrary degree | Exact rational root isolation and sign-table certificate generation | The ordered sections and open intervals partition the real line. Every sign in every row agrees with evaluation everywhere on that row. |
| One equation `a(x)y² + b(x)y + c(x) = 0`, with rational polynomial coefficients of any degree in `x` | Project the three coefficients and their discriminant, then classify each base cell | A fiber-preserving homeomorphism of the cylinder identifies the family on each cell with a fixed model. The model is empty, a point, two points, or the whole line. |
| Finite lists of real bivariate polynomials | Squarefree projection, univariate root isolation over ℝ, and continuous root lifting. | Every point lies in exactly one cell, all input signs are constant on each cell, and the cells project cylindrically. Each cell is homeomorphic to a product of two real intervals or points. |
| Two real quadric equations in three variables | Exact vertical fiber decisions with specialized planar fast paths and the general planar CAD as a fallback. | The cells partition the intersection. Each has a sample and is contractible. Certified closure incidences determine the connected components of the whole intersection. |
| Univariate formulas with arbitrary real coefficients | Lean's mathematical root multiset and a one-dimensional CAD | A total, noncomputable specification with an exact solution-set theorem. |

The general planar and quadric decompositions are total, noncomputable Lean constructions. The checked pipeline accepts root tables and closure incidences from a backend. A standalone executable backend for general real-algebraic root isolation and closure incidence, and automatic refinement to a stratification satisfying the frontier condition, remain open.

## Run

The Lake project uses the supplied Lean 4.36.0 installation and its pinned mathlib checkout. Python 3 uses only its standard library.

```sh
source ~/src/lean/env.sh
lake build
lake env lean examples/Affine.lean
lake env lean examples/Plane.lean
lake env lean examples/QuadricIntersection.lean
python3 scripts/univariate.py examples/shared-roots.json
python3 scripts/univariate.py --quadratic-family examples/cusp.json --lean /tmp/Cusp.lean
lake env lean /tmp/Cusp.lean
python3 tests/test_certificates.py
```

The cusp input is `[[1], [], [0, 0, 0, -1]]`. It represents `y² − x³ = 0`. The command returns three base cells. For negative `x` the fiber is empty, at zero it is a point, and for positive `x` it consists of two points. The generated certificate identifies the exceptional parameter as the unique root of its projection polynomial in the reported rational isolating interval.

For ordinary univariate input, each array gives the coefficients of one polynomial in ascending power order. For example, `[-2, 0, 1]` denotes `x² − 2`. Empty arrays represent zero. Coefficients can be integers, finite decimals, or rational strings such as `"3/7"`. In family mode the arrays give `a`, `b`, and `c`, in that order.

The command emits JSON after Lean checks the generated certificate. Each section has a zero-based root index and an open rational isolating interval. Sector endpoints refer to these indices. A null endpoint denotes infinity in that direction. Sector samples are exact rational numbers. The sign vector follows input order and uses −1, 0, and 1. In family mode the entries correspond to `a`, `b`, `c`, and `b² − 4ac`. Save the certificate with `--lean` to inspect the exact polynomials and theorems corresponding to a report.

## Algorithms and trust boundary

The affine solver recognizes sums, negations, products of affine factors, and scalar multiplication. Projection retains vertical constraints and compares each unordered pair of distinct root functions. It removes duplicates and globally constant projections before recursion. Lifting orders roots at each base sample, merges coincident roots, and alternates sections with open sectors. The projection proof transports the root ordering to every point of the base cell, including lower-dimensional cells. Boolean evaluation then uses one sample per cell.

The univariate search forms a common square-free root polynomial. It certifies the two tails by a change of variable and subdivides bounded intervals using exact Bernstein coefficients. A root box has a sign change and a derivative of fixed strict sign in its interior. Lean checks the polynomial identities, the intermediate-value and monotonicity arguments, the absence of other roots, and each input sign. Shared and even-multiplicity roots receive their own sections. The Python search, JSON parser, and report renderer are outside Lean. Search termination and runtime bounds for the Python program have no Lean proof. The generated Lean certificate exports `CertifiedDiagram.diagram` and the ordered root table `CertifiedDiagram.cutTable`. Family certificates also contain `familyDiagram`, `fibers`, and `reportedKinds`.

## Planar decomposition

`Plane.solve ps` takes a finite list of nested polynomials, with the outer
variable in the second cylindrical coordinate. It constructs a
`Plane.Diagram ps` with a partition proof, sign invariance for every input
polynomial, and a sample and contractibility proof for every cell.
`Plane.solve_cell_model` gives a homeomorphism to a product of two intervals
or points. `Plane.solve_cylindrical` proves that horizontal projections of
any two cells are equal or disjoint. `Plane.solveOver` performs the
algebraic projection in an embedded coefficient field, such as ℚ or the
real algebraic numbers, before lifting over ℝ.

The default projection removes repeated factors from the product of the
nonzero inputs. It projects the leading coefficient and the resultant of
that squarefree polynomial with its vertical derivative. On open base
intervals, Lean proves that simple roots persist, that other roots cannot
enter the local root boxes or escape to infinity, and that the ordered
roots move continuously. Each input polynomial retains a fixed subset
of the root sections on that interval. A vertical homeomorphism matches
the moving roots to the sample fiber. At critical coordinates the
construction specializes every input before isolating its vertical roots,
including when the degree drops or a polynomial vanishes identically.

`Plane.Projection.ofBezout` accepts an alternative root polynomial,
a Bézout identity with a nonzero univariate right-hand side, and
divisibility witnesses for the inputs. `Plane.solveWith` produces the
same guarantees from this data. The example in `examples/Plane.lean`
certifies a repeated shared factor and a nullified vertical fiber.

To use supplied root isolations, construct a `Plane.LiftingData` for the
projection. Its `base` table covers the projection cuts. Its `fibers` table
provides the roots of the specialized input polynomials at the sample of
each base cell, including isolated critical coordinates. Each
`Univariate.CutTable` proves that its roots are strictly ordered and cover
all zeros of the nonzero polynomials. Lean handles zero specializations
and constructs the continuous lifting charts. `Plane.LiftingData.sample_eq`
proves that the samples of the lifted planar cells are the pairs of slice
samples computed directly from these tables.

## Quadric intersections

Use `Quadric.Equation K` with coefficients in the order
`zz, xz, yz, z, xx, xy, yy, x, y, constant`. A point in `Quadric.Space` is
`((x, y), z)`. For example, the sphere and equatorial plane are
`⟨1, 0, 0, 0, 1, 0, 1, 0, 0, -1⟩` and
`⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩`. The examples file proves that the
dispatcher returns a certified decomposition of their intersection.

- `Quadric.roots q r x y` is executable over the rationals. Its two-root result
  gives a center, denominator, and discriminant that specify the ordered pair
  of real heights exactly. `Quadric.roots_correct` verifies interpretation in
  ℝ along an ordered field embedding. `Quadric.fiber_correct` covers every real
  base point, including coincident equations, repeated roots, and full lines.
- `Quadric.decompose q r` gives the total decomposition, verified by
  `Quadric.decompose_correct`. The specialized solver `Quadric.solve?`
  tries the axis-separated, affine, and single-conic routes. Other inputs
  use `Plane.solve`. The examples include a mixed quartic projection
  that exercises the general route.
- `Quadric.decomposeRealAlg q r` takes coefficients in `RealAlg` and
  returns cells in real space. The more general `Quadric.decomposeOver ι q r`
  accepts any field embedded in ℝ. Its general route computes the
  elimination polynomials and the squarefree projection in that field.
- `Quadric.solve` also accepts an explicitly supplied
  `Plane.Diagram (Quadric.program q r).projection`, for example one
  produced by `Plane.solveWith`. The corresponding lifting theorem is
  `Quadric.solve_spec`.
- `Quadric.decomposeWith q r data` lifts checked projection and root
  certificates through to the 3D intersection. Lean verifies cell models
  as products of points, intervals, and full lines. It also verifies
  cylindrical projection onto the plane and onto the first coordinate.
  `checkedNullifiedLine` in the examples uses supplied root lists to
  certify an intersection that is an entire vertical line.
- `Quadric.decomposeComponents q r` labels the cells by their connected
  components using the mathematical closure-incidence relation.
  `Quadric.ClosureIncidence` accepts a Boolean table and a proof for the
  closure intersections it reports, including absence of intersection.
  `computeLabels` runs on the table alone, and `component_correct` proves
  that the union of the cells with a given label is the connected
  component of their samples.

The vertical decision tree first selects a nonzero quadratic coefficient when
one is available. Cancelling the second quadratic term gives a linear equation
in `z`. A nonzero slope fixes one height and reduces the remaining equation to
a polynomial of degree at most four in `x,y`. At a zero slope, the constant
remainder determines whether to test the first quadratic's discriminant. The
linear branch uses the determinant of the two linear equations and handles
vanishing slopes separately. Constant tests are discharged before planar
projection. The implementation describes real loci, including inputs whose
coefficients are embedded real algebraic numbers.

## Lean entry points

- `Predicate.solveAffine?` accepts polynomial-expression predicates over `Fin n`. Its `some` result carries the guarantee of `Predicate.solveAffine_correct`. A `none` result means the recognizer could not compile this expression. An empty solution is represented by `some []`.
- `cad_correct`, `solve_correct`, and `Geometry.contractible_cell` give the affine partition, formula, and topology theorems. `Extension.solve_map` transports a computed decomposition along an order-preserving field embedding. In particular, rational samples certify regions containing irrational real points. `solve_realAlg` specializes the theorem to the real algebraic numbers embedded in ℝ.
- `Predicate.solveLine` dispatches a univariate formula to the affine recognizer or the mathematical arbitrary-degree root partition. `Predicate.solveLine_correct` covers both branches.
- `Quadratic.classify` uses only field arithmetic and comparisons. `Quadratic.locate` partitions universal coefficient space in the order `a,b,c`. `Quadratic.Family.trivialization` gives the parameter-preserving homeomorphism for a checked family diagram, including degree drops, repeated roots, and nullified fibers.
- `Expr.complexEquation` converts a complex equation into real predicates using a supplied coordinate ordering. `Expr.complexEquation_correct` proves equivalence to complex evaluation. This accepts embedded algebraic coefficients and splits products of complex factors before realification. A resulting nonlinear real predicate still needs a supported solver.
