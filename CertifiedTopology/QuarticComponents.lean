module

public import CertifiedTopology.QuarticIntersection
public import CertifiedTopology.ClosureComponents

@[expose] public section

namespace CertifiedTopology.Quartic

open Set

abbrev ClosureIncidence (cs : List Cell) :=
  ClosureComponents.ClosureIncidence (fun i : Fin cs.length => (cs.get i).carrier)

variable {K : Type} [Field K] [DecidableEq K] (ι : K →+* ℝ) (q r : TriPoly K)
variable (d : Plane.Diagram ((projection q r).map (Plane.embedCoefficients ι)))

theorem solve_component_correct (tables : SampleTables ι q r d)
    (cert : ClosureIncidence (solve ι q r d tables))
    (i : Fin (solve ι q r d tables).length) :
    connectedComponentIn (locus ι q r) ((solve ι q r d tables).get i).sample =
      ⋃ j : {j // cert.labels.get i = cert.labels.get j}, ((solve ι q r d tables).get j.val).carrier :=
  cert.component_correct (isClosed_locus ι q r)
    (fun x => (solve_cover ι q r d tables x).trans List.exists_mem_iff_get)
    (fun j => by
      let := ((solve ι q r d tables).get j).contractible
      exact isPreconnected_iff_preconnectedSpace.mpr inferInstance)
    i ((solve ι q r d tables).get i).sample_mem

/-- Label the output cells by their connected components using closure
    incidence. A checked incidence matrix can use the same label algorithm. -/
noncomputable def decomposeComponents [CharZero K] (q r : Equation K) :
    Vector (Fin (decomposeOver ι q r).length) (decomposeOver ι q r).length :=
  (ClosureComponents.ClosureIncidence.fromClosures
    (fun i : Fin (decomposeOver ι q r).length => ((decomposeOver ι q r).get i).carrier)).labels

theorem decomposeComponents_correct [CharZero K] (q r : Equation K)
    (i : Fin (decomposeOver ι q r).length) :
    connectedComponentIn (locus ι q.poly r.poly) ((decomposeOver ι q r).get i).sample =
      ⋃ j : {j // (decomposeComponents ι q r).get i = (decomposeComponents ι q r).get j},
        ((decomposeOver ι q r).get j.val).carrier :=
  solve_component_correct ι q.poly r.poly _ (fun _ _ _ => none)
    (ClosureComponents.ClosureIncidence.fromClosures _) i

end CertifiedTopology.Quartic
