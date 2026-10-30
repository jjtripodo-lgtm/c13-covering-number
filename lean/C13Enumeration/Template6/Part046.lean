import C13Enumeration.Template6.Data
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound736 : ∀ f ∈ assignSearch step finish [] [] table736, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel
end C13.Enumeration.Template6
