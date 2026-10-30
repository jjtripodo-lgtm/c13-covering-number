import C13Global.Relative.Source66
import C13Global.Bindings.Source66
namespace C13.Global.Source66
open Finset C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem all_foursets (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link66 Q :=
  Relative.Source66.all_foursets alphabet_complete Q hQ
end C13.Global.Source66
