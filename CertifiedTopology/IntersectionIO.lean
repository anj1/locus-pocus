module

public import CertifiedTopology.AffineTopology
public import Lean.Data.Json

@[expose] public section

namespace CertifiedTopology.TopologyArtifact

open Lean

def Layout.toJson {C : Type} (a : Layout C) (describe : C → Json) : Json :=
  let labels := a.labels
  Json.arr <| (List.finRange a.cells.length).toArray.map fun i =>
    Json.mkObj [
      ("cell", describe (a.cells.get i)),
      ("component", Lean.toJson (labels.get i).val),
      ("closure", Lean.toJson ((List.finRange a.cells.length).filterMap fun j =>
        if a.incident i j then some j.val else none))]

def affine3Json (c : Cell ℚ 3) : Json :=
  Json.mkObj [
    ("dimension", toJson c.dimension),
    ("sample", toJson [toString c.sample.1.1.2, toString c.sample.1.2, toString c.sample.2]),
    ("constraints", Json.arr (c.constraints.toArray.map fun (a, s) =>
      Json.mkObj [
        ("coefficients", toJson [toString a.1.1.1, toString a.1.1.2, toString a.1.2, toString a.2]),
        ("sign", toJson (match s with | .below => (-1 : Int) | .on => 0 | .above => 1))]))]

end CertifiedTopology.TopologyArtifact
