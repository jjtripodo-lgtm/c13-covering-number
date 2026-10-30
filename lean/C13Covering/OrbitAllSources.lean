import C13Covering.OrbitCertificateChunks.Row00
import C13Covering.OrbitCertificateChunks.Row01
import C13Covering.OrbitCertificateChunks.Row02
import C13Covering.OrbitCertificateChunks.Row03
import C13Covering.OrbitCertificateChunks.Row04
import C13Covering.OrbitCertificateChunks.Row05
import C13Covering.OrbitCertificateChunks.Row06
import C13Covering.OrbitCertificateChunks.Row07
import C13Covering.OrbitCertificateChunks.Row08
import C13Covering.OrbitCertificateChunks.Row09
import C13Covering.OrbitCertificateChunks.Row10
import C13Covering.OrbitCertificateChunks.Row11
import C13Covering.OrbitCertificateChunks.Row12
import C13Covering.OrbitCertificateChunks.Row13
import C13Covering.OrbitCertificateChunks.Row14
import C13Covering.OrbitCertificateChunks.Row15
import C13Covering.OrbitCertificateChunks.Row16
import C13Covering.OrbitCertificateChunks.Row17
import C13Covering.OrbitCertificateChunks.Row18
import C13Covering.OrbitCertificateChunks.Row19
import C13Covering.OrbitCertificateChunks.Row20
import C13Covering.OrbitCertificateChunks.Row21
import C13Covering.OrbitCertificateChunks.Row22
import C13Covering.OrbitCertificateChunks.Row23
import C13Covering.OrbitCertificateChunks.Row24
import C13Covering.OrbitCertificateChunks.Row25
import C13Covering.OrbitCertificateChunks.Row26
import C13Covering.OrbitCertificateChunks.Row27
namespace C13.OrbitPilot.AllSources
open C13.SourceData
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Every input of the complete 28³ universe has a proof-carrying orbit witness.
There is no source-group completeness or full-S12 nonisomorphism hypothesis. -/
theorem all_indices_covered (i : CompletionIndex) : CoveredIndex i := by
  obtain ⟨a,b,c⟩ := i
  fin_cases a
  · exact Certificate.Row00.row_covered b c
  · exact Certificate.Row01.row_covered b c
  · exact Certificate.Row02.row_covered b c
  · exact Certificate.Row03.row_covered b c
  · exact Certificate.Row04.row_covered b c
  · exact Certificate.Row05.row_covered b c
  · exact Certificate.Row06.row_covered b c
  · exact Certificate.Row07.row_covered b c
  · exact Certificate.Row08.row_covered b c
  · exact Certificate.Row09.row_covered b c
  · exact Certificate.Row10.row_covered b c
  · exact Certificate.Row11.row_covered b c
  · exact Certificate.Row12.row_covered b c
  · exact Certificate.Row13.row_covered b c
  · exact Certificate.Row14.row_covered b c
  · exact Certificate.Row15.row_covered b c
  · exact Certificate.Row16.row_covered b c
  · exact Certificate.Row17.row_covered b c
  · exact Certificate.Row18.row_covered b c
  · exact Certificate.Row19.row_covered b c
  · exact Certificate.Row20.row_covered b c
  · exact Certificate.Row21.row_covered b c
  · exact Certificate.Row22.row_covered b c
  · exact Certificate.Row23.row_covered b c
  · exact Certificate.Row24.row_covered b c
  · exact Certificate.Row25.row_covered b c
  · exact Certificate.Row26.row_covered b c
  · exact Certificate.Row27.row_covered b c

/-- Complete internal catalog-coverage theorem for the literal Figure-1 source
family plus separately included Figure 6. This does not prove the published
minimum-link classification, which remains an external theorem parameter. -/
theorem catalog_covers_all_raw_sources : CatalogCoversSources rawSources catalog hole :=
  full_coverage_of_all_index_witnesses all_indices_covered

/-- The source-orbit obligation is now discharged. Executable pencil-domain
completeness and all-fourset checker acceptance remain explicit obligations. -/
theorem exact30_after_domain_and_checker
    (D : Family Point → Point → List Checker.Pencil)
    (hminimum : PublishedMinimumBound Point)
    (hpublished : PublishedClassification1995)
    (hcomplete : ExecutableDomainsComplete catalog hole D)
    (hchecks : AllFourChecksFalse catalog hole D) :
    (∃ F : Family Point, IsCoverOn Finset.univ F 7 4 ∧ F.card = 30) ∧
    (∀ F : Family Point, IsCoverOn Finset.univ F 7 4 → 30 ≤ F.card) :=
  exact30_of_remaining_finite_obligations D hminimum hpublished
    catalog_covers_all_raw_sources hcomplete hchecks

end C13.OrbitPilot.AllSources
