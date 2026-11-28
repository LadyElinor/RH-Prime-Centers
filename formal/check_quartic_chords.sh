#!/bin/sh
# Build and replay the complete local proof, including each imported project module.
set -eu
cd "$(dirname "$0")"
lake env lean --version
lake build QuarticChord
while read -r module target; do
    echo "Replaying $module ($target)"
    lake env lean --run Replay.lean named "QuarticChord.$target" ".lake/build/lib/lean/$module.olean"
done <<'MODULES'
QuarticChord/Elementary chord_deviation_of_right_deriv
QuarticChord/PartialSummation recipMass_error
QuarticChord/PrimeTent finiteSlope_sub
QuarticChord/CountWeight primeCount_eq_primeCounting_sub
QuarticChord/Asymptotic deficit_uniformChordSmall
QuarticChord/Scale shortIntervalPrimeEstimate_of_local
QuarticChord/GuthMaynard GuthMaynardPrimeCount.shortInterval
QuarticChord/Supremum UniformChordSmall.tendsto_sup
QuarticChord/Windows weak_windows_of_anchors
QuarticChord quartic_chord_limit
MODULES
