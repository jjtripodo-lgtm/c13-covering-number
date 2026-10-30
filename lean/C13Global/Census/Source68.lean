import C13Global.Relative.Source68
import C13Global.Bindings.Source68
import C13Enumeration.Census.Figure6
namespace C13.Global.Source68
open Finset C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hard_actual (Q : Finset Point) (hQ : Q ∈ Relative.Source68.hardQuads) :
    ActualObstruction figure6 Q := by
  have he : Relative.Source68.hardQuads = hardQuadruples := by decide +kernel
  rw [he] at hQ
  intro hclass F hcover hroot hmin hout
  exact five_figure6_cover_obstructions hclass F hcover hroot Q hQ hmin hout

theorem all_foursets (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction figure6 Q :=
  Relative.Source68.all_foursets alphabet_complete hard_actual Q hQ
end C13.Global.Source68
