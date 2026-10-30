import C13Enumeration.Template8.Part000
namespace C13.Enumeration.Template8
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (8 : Point) = hole)
    (hs : transport e (link link09 8) = link link09 8) : (e : Point → Point) ∈ maps := by
  exact star_template_maps_complete link09 hole 8 [0,1,2,3,4,5,6,7,9,10,11]
    (by decide +kernel) (by decide +kernel) matrix matrix_checked maps bound0 e he hc hs

theorem listed_maps_check : (maps.all fun f => decide (GoodMap link09 link09 hole 8 hole 8 f)) = true := by
  decide +kernel
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link09 link09 hole 8 hole 8 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp listed_maps_check) f hf)
end C13.Enumeration.Template8
