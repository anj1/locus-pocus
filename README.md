# Certified topology of algebraic families

This Lean 4 project computes sign-invariant cylindrical algebraic decompositions over real algebraic coefficients. It also certifies how the topology of a quadratic zero fiber varies with a polynomial parameter. Parameter coordinates come first in cylindrical order. Topological statements use the usual Euclidean topology.

| Input | Computation | Lean guarantee |
| --- | --- | --- |
| Boolean combinations of signs of products of affine forms, in any dimension | Exact projection and lifting over an ordered field. Executable over the rationals. | Every point belongs to a unique cell, each cell contains its sample, and all factor signs are constant there. The selected cells describe the formula exactly. Every real output cell is convex and contractible. |
| Univariate polynomials over an executable ordered field embedded in ℝ | Squarefree reduction and adaptive dyadic isolation in Lean | The algorithm terminates and isolates every distinct real root in order. Zero polynomials and roots on subdivision endpoints are handled explicitly. |
| One equation `a(x)y² + b(x)y + c(x) = 0`, with rational polynomial coefficients of any degree in `x` | Project the three coefficients and their discriminant, then classify each base cell | A fiber-preserving homeomorphism of the cylinder identifies the family on each cell with a fixed model. The model is empty, a point, two points, or the whole line. |
| Finite lists of real bivariate polynomials | Squarefree projection, univariate root isolation over ℝ, and continuous root lifting. | Every point lies in exactly one cell, all input signs are constant on each cell, and the cells project cylindrically. Each cell is homeomorphic to a product of two real intervals or points. |
| Two real quadric equations in three variables | Exact vertical fiber decisions with specialized planar fast paths and the general planar CAD as a fallback. | The cells partition the intersection. Each has a sample and is contractible. Certified closure incidences determine the connected components of the whole intersection. |
| Two polynomial equations with real algebraic coefficients of total degree at most four in three variables | Exact root isolation over finite algebraic extensions, fraction-free projection, lifting from exact samples, and frontier refinement. | A cylindrical partition with Euclidean cell models, exact connected components, and a finite locally closed stratification with a certified closure table. |
| Univariate formulas with arbitrary real coefficients | Lean's mathematical root multiset and a one-dimensional CAD | A total, noncomputable specification with an exact solution-set theorem. |

The executable solver is in `CertifiedTopology.ComputedInput`. Earlier mathematical constructions over arbitrary real coefficients and their certificate interfaces remain available.

## Compute an intersection from input

`scripts/intersection.py` takes two sparse polynomial equations in three
variables. A term is `[x exponent, y exponent, z exponent, coefficient]` and its
total degree must be at most four. Coefficients can be integers, finite decimals,
or rational strings. An algebraic coefficient can be written as
`{"polynomial": [-2, 0, 1], "root": 1}`, which denotes the positive root of
`x² − 2`. The polynomial uses ascending powers and the zero-based index counts
distinct real roots in increasing order. An empty equation list denotes the
zero polynomial.

```sh
source ~/src/lean/env.sh
cat > /tmp/intersection.json <<'EOF'
[
  [[0, 1, 0, 1], [4, 0, 0, -1]],
  [[0, 0, 2, 1], [3, 0, 0, -1], [4, 0, 0, 1]]
]
EOF
python3 scripts/intersection.py /tmp/intersection.json --stratify --lean /tmp/Intersection.lean
lake env lean /tmp/Intersection.lean
```

This input defines a compact cusp on the graph `y = x⁴`. The command derives its
cells, directed closure incidences, and connected components. The report uses
zero-based cell indices. Each `closure` array lists all cells contained in the
closure of its row's cell, including that cell itself. Equal `component` values
identify cells in the same connected component.

- The affine route searches for rational affine factors of the expanded
  equations. Lean verifies the factorization identities and computes the CAD,
  samples, closure table, and labels in exact rational arithmetic.
- The polynomial graph route tries coordinate permutations and eliminates one
  variable using a constant linear coefficient. It can expose the linear
  coefficient by subtracting a rational multiple of the other equation. It
  supports a graph in the remaining height or a shifted second or fourth power
  of the height with constant leading coefficient. The report's `axes` gives
  the original coordinate indices in the order parameter, eliminated
  coordinate, height. The `graph` array is indexed by the height exponent.
  Its entries, `center`, and `radicand` use ascending powers of the parameter.
  Each lifted cell references a base row and a branch of the indicated root.
  Lean checks the elimination identities, the real root isolations, and the
  closure tests against the real intervals, then computes the lifted topology.

For the affine and graph routes, Lean proves that every cell is locally closed
and contractible and that every point of the original locus belongs to exactly
one cell. The generated file exports `CertifiedIntersection.artifact`,
`CertifiedIntersection.locus`, and `CertifiedIntersection.certified`.
`TopologyArtifact.Valid.closure_eq` identifies each cell closure with the
reported union. `TopologyArtifact.Valid.component_correct` identifies each
reported component with the connected component in the original real locus.

The general `cad` route computes directly from the sparse input. Projection
uses degree, squarefree, and pairwise common-root decisions. Lifting isolates
the exact sample fibers, including nullified fibers and degree drops. The
report numbers rows from zero, with sectors at even indices and root sections
at odd indices. Rational reports include the nested ascending coefficients of
each row's root source. The generated Lean artifact retains the exact cell
codes for algebraic inputs as well. Its `inputLocus` interprets coefficients
using the specified root indices. `certifiedCoefficients` checks those indices,
and `certified` identifies the computed cell partition with `inputLocus`.

On the CAD route, `closure_overlap` lists the other cells whose ambient
closures intersect the row's closure. `ComputedTopology.Intersection.closure_correct`
certifies a first-order formula for each entire closure, and
`ComputedTopology.Intersection.component_correct` identifies each label with
the actual connected component.

Use `--stratify` to compute a frontier-compatible refinement of the
cylindrical partition. Its `strata` array gives each stratum's dimension and
the indices of the strata making up its closure. Lean proves that these sets
partition the input locus and that each stratum is locally closed and
homeomorphic to an open subset of the reported Euclidean dimension.
The generated Lean artifact exports `certifiedStrata` and
`certifiedStratumClosure` and retains each stratum's exact formula.
On the affine and power-graph routes, the reported cells already satisfy
the frontier condition.

Refinement computes the boundaries of the CAD cells and recurses on a
residual of strictly smaller dimension. At each stage it respects the
closures of all earlier strata. Closure decisions and general refinement
can dominate runtime, especially for curved cells that require quantified
CAD.

`CADDecision.stratify` accepts a Boolean or quantified semialgebraic formula
over the same exact coefficient fields. Its `relativeClosure_eq` theorem
describes which strata make up the closure inside the input set, including
when the input set is open or locally closed.

## Run

The Lake project uses the supplied Lean 4.36.0 installation and its pinned mathlib checkout. Python 3 uses only its standard library.

```sh
source ~/src/lean/env.sh
lake build
lake env lean examples/Affine.lean
lake env lean examples/Plane.lean
lake env lean examples/QuadricIntersection.lean
lake env lean examples/QuarticIntersection.lean
python3 scripts/univariate.py examples/shared-roots.json
python3 scripts/univariate.py --quadratic-family examples/cusp.json --lean /tmp/Cusp.lean
lake env lean /tmp/Cusp.lean
python3 tests/test_certificates.py
lake env lean tests/ExecutableIsolation.lean
```

The cusp input is `[[1], [], [0, 0, 0, -1]]`. It represents `y² − x³ = 0`. The command returns three base cells. For negative `x` the fiber is empty, at zero it is a point, and for positive `x` it consists of two points. The generated certificate identifies the exceptional parameter as the unique root of its projection polynomial in the reported rational isolating interval.

For ordinary univariate input, each array gives the coefficients of one polynomial in ascending power order. For example, `[-2, 0, 1]` denotes `x² − 2`. Empty arrays represent zero. Coefficients can be integers, finite decimals, or rational strings such as `"3/7"`. In family mode the arrays give `a`, `b`, and `c`, in that order.

The command emits JSON after Lean checks the generated certificate. Each section has a zero-based root index and an open rational isolating interval. Sector endpoints refer to these indices. A null endpoint denotes infinity in that direction. Sector samples are exact rational numbers. The sign vector follows input order and uses −1, 0, and 1. In family mode the entries correspond to `a`, `b`, `c`, and `b² − 4ac`. Save the certificate with `--lean` to inspect the exact polynomials and theorems corresponding to a report.

## Algorithms and trust boundary

The affine solver recognizes sums, negations, products of affine factors, and scalar multiplication. Projection retains vertical constraints and compares each unordered pair of distinct root functions. It removes duplicates and globally constant projections before recursion. Lifting orders roots at each base sample, merges coincident roots, and alternates sections with open sectors. The projection proof transports the root ordering to every point of the base cell, including lower-dimensional cells. Boolean evaluation then uses one sample per cell.

The general intersection solver uses `ExecutableIsolation.isolate`. Lean computes a squarefree part and a rational root bound, then bisects intervals using exact Horner bounds for the polynomial and its derivative. Lean proves that subdivision terminates and that the returned windows contain every distinct real root exactly once in order. This also works in the exact algebraic extensions used during lifting.

The older `scripts/univariate.py` certificate generator uses a common squarefree root polynomial and exact Bernstein coefficients. Lean checks the polynomial identities, the intermediate-value and monotonicity arguments, the absence of other roots, and each input sign. The Python generator computes candidate certificates, parses JSON, and renders reports. Its generated Lean certificate exports `CertifiedDiagram.diagram` and the ordered root table `CertifiedDiagram.cutTable`. Family certificates also contain `familyDiagram`, `fibers`, and `reportedKinds`.

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

### Quadric stress examples

[The 12-panel plot gallery](examples/quadric-stress.pdf) includes a smooth
spatial loop, Viviani’s nodal curve, a circle with an isolated point, crossing
lines and circles, a shared plane, coincident spheres, and a near-tangent
sphere sweep. It also shows a mixed quartic projection and a degree drop
whose neighboring branches escape to infinity.

Run the existing quadric examples and regenerate the gallery with Lean,
NumPy, and Matplotlib.

```bash
source ~/src/lean/env.sh
lake build
lake env lean examples/QuadricIntersection.lean
lake env lean --run examples/QuadricStress.lean > /tmp/quadric-stress-inputs.json
python3 examples/plot_quadric_stress.py /tmp/quadric-stress-inputs.json examples/quadric-stress.pdf
```

`QuadricStress.lean` runs exact rational fiber assertions and checks
whole-locus theorems for the real CAD. It verifies the degree-drop projection
and proves that the disjoint spheres give an empty cell list. The full real
CAD is noncomputable. The renderer samples analytic parametrizations, checks
the samples against the two equation vectors emitted by Lean, and clips
unbounded branches to the plot windows.

## Quartic intersections

Use `Quartic.Equation.ofTerms` to supply sparse monomials. A term stores its
exponents in the order `x, y, z`, then its coefficient and a proof that
the exponents sum to at most four. For example, the term
`⟨2, 0, 2, -2, by decide⟩` denotes `−2x²z²`. A point in the real locus
has the form `((x, y), z)`.

- `Quartic.decomposeOver ι q r` accepts equations over a field embedded in
  ℝ. Use `decomposeRealAlg` for real algebraic coefficients or
  `decompose` for real coefficients. The coverage and uniqueness theorems
  are `decomposeOver_cover` and `decomposeOver_correct`.
- `decomposeOver_cell_model` gives a homeomorphism from each cell to a
  product of three points or intervals. `decomposeOver_cylindrical`
  verifies both lower-dimensional projections.
- `Quartic.solve` accepts a checked planar diagram for the embedded
  `Quartic.projection` polynomials. Build one from a
  `Plane.LiftingData` certificate. An optional `Quartic.SampleTables`
  argument supplies exact vertical root lists. `RootTable.ofCutTable`
  converts a checked univariate covering table by retaining its roots.
- `Quartic.solve_component_correct` checks connected-component labels
  from a supplied closure-incidence matrix. `decomposeComponents`
  defines the mathematical labels from the cell closures.

The decision program computes the common vertical divisor by testing its
leading coefficients and taking pseudo-remainders. It removes multiplicities
from the common divisor, and projects only the distinct nonconstant
coefficient tests that survive constant pruning. Each planar cell chooses
the same branch everywhere. A nonzero constant gives an empty fiber, a
linear root gives a height by division, and higher degrees use ordered
continuous root sections. When both equations vanish as polynomials in
`z`, the solver lifts the entire vertical cylinder.

The examples in this section check crossing lines defined by repeated factors,
an intersection with an entire nullified vertical line, and a degree drop
where the intersection leaves the fiber. These older entry points specify
the real root and closure operations mathematically. The executable entry
points are `ComputedInput.solve` and `ComputedInput.solveStrata`.

### Quartic stress examples

[The eight-panel quartic gallery](examples/quartic-stress.pdf) shows a
tacnode, a compact cusp, a four-height fiber with coalescences, four skew
lines with intersecting projections, three sheets meeting a nullified
vertical line, a branch that escapes at a degree drop, an oval with an
isolated point, and a smooth nonplanar loop.

Lean checks the entire locus and uniqueness of the covering cell for each
pair of equations. The renderer evaluates analytic parametrizations and
checks the sampled coordinates against both equations exported by Lean.
It clips unbounded curves and sheets to the plot windows.

Regenerate the PDF with Lean, NumPy, and Matplotlib.

```sh
source ~/src/lean/env.sh
lake build
lake env lean --run examples/QuarticStress.lean > /tmp/quartic-stress-inputs.json
python3 examples/plot_quartic_stress.py /tmp/quartic-stress-inputs.json examples/quartic-stress.pdf
```

## Lean entry points

- `Predicate.solveAffine?` accepts polynomial-expression predicates over `Fin n`. Its `some` result carries the guarantee of `Predicate.solveAffine_correct`. A `none` result means the recognizer could not compile this expression. An empty solution is represented by `some []`.
- `cad_correct`, `solve_correct`, and `Geometry.contractible_cell` give the affine partition, formula, and topology theorems. `Extension.solve_map` transports a computed decomposition along an order-preserving field embedding. In particular, rational samples certify regions containing irrational real points. `solve_realAlg` specializes the theorem to the real algebraic numbers embedded in ℝ.
- `Predicate.solveLine` dispatches a univariate formula to the affine recognizer or the mathematical arbitrary-degree root partition. `Predicate.solveLine_correct` covers both branches.
- `Quadratic.classify` uses only field arithmetic and comparisons. `Quadratic.locate` partitions universal coefficient space in the order `a,b,c`. `Quadratic.Family.trivialization` gives the parameter-preserving homeomorphism for a checked family diagram, including degree drops, repeated roots, and nullified fibers.
- `Expr.complexEquation` converts a complex equation into real predicates using a supplied coordinate ordering. `Expr.complexEquation_correct` proves equivalence to complex evaluation. This accepts embedded algebraic coefficients and splits products of complex factors before realification. A resulting nonlinear real predicate still needs a supported solver.
