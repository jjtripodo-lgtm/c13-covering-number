import C13Global.CensusCore
namespace C13.Global
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_symmetry_of_codes (root : List Code) (K : Family Point)
    (binding : decodeSource root = K) (e : Equiv.Perm Point)
    (checked : (root.map (imageCode e)).toFinset = root.toFinset) :
    transport e K = K := by
  have hh := congrArg (fun s : Finset Code => s.image decodeTyped) checked
  have he : decodeSource (root.map (imageCode e)) = decodeSource root := by
    simpa only [decodeSource,list_map_finset] using hh
  rw [decodeSource_image,mapFamily_equiv,binding] at he
  exact he
end C13.Global
