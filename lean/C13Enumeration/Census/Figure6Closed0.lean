import C13Enumeration.Census.Figure6Columns0
import C13Enumeration.Census.Figure6Bridge
namespace C13.Enumeration.Census.Figure6Case0
open C13 C13.SourceData
set_option Elab.async false
set_option maxRecDepth 10000

theorem actual_cover_obstruction
    (hclass : ClassifiesMinimumLinks catalog hole)
    (F : Family Point) (hcover : IsCoverOn Finset.univ F 7 4)
    (hroot : link F hole = figure6)
    (hmin : ∀ q ∈ points, degree F q = 15)
    (houtside : (outside F hole).card ≤ 14) : False :=
  figure6_cover_obstruction points (by decide +kernel) columns witnesses tree
    columns_checked tree_checked hclass F hcover hroot hmin houtside
end C13.Enumeration.Census.Figure6Case0
