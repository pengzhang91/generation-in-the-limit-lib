import GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.Topology
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankSequence
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.Nice

/-!
# Paper 23: proved-claims overview

This facade collects the currently proved numbered claims from
Kleinberg--Wei, *Validity, Sparse Holes, and Breadth in Language Generation:
Banach Density, Topology, and Geometry*.  It intentionally does not expose
aliases named after Theorems 4.1, 4.5, 5.1, 5.5, 5.8, or 5.9, because those
headline theorems are not yet formalized.

Claim 4.11 is exposed in its repaired convergent-proper-tower form.  Claims
4.18 and 4.20 are finite-tree results.  Every declaration below is an alias,
so this overview introduces no duplicate proof.
-/

namespace GenLimit.KleinbergWei.Banach.Results

alias claim_3_3 := GenLimit.KleinbergWei.Banach.claim_3_3
alias claim_3_5 := GenLimit.KleinbergWei.Banach.claim_3_5
alias claim_3_6 := GenLimit.KleinbergWei.Banach.claim_3_6
alias claim_4_4 := GenLimit.KleinbergWei.Banach.claim_4_4
alias claim_4_11_repaired :=
  GenLimit.KleinbergWei.Banach.claim_4_11_of_convergentProperTower
alias claim_4_18 :=
  GenLimit.KleinbergWei.Banach.claim_4_18_change_index_card_bound
alias claim_4_20 :=
  GenLimit.KleinbergWei.Banach.claim_4_20_adjacent_pair_lca
alias claim_7_1 := GenLimit.KleinbergWei.Banach.claim_7_1

end GenLimit.KleinbergWei.Banach.Results
