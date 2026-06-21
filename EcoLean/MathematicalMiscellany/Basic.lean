import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function

/-!
# Convex preliminaries for EconLib

This file gathers the parts of mathlib's convexity API used by EconLib.

## Purpose

The goal of this file is to organise and inspect the existing convex-analysis
infrastructure already available in mathlib before adding any project-specific
lemmas. In particular, EconLib should reuse mathlib's existing notions such as
`Convex` and `ConvexOn` rather than introducing parallel definitions.

## Usage

This file is intentionally lightweight. At the start, it should contain only:

- imports of the relevant mathlib convexity files;
- a namespace for project-local work;
- `#check` commands to inspect the available API.

New lemmas should only be added once it is clear that the required result is not
already present in mathlib, or when a small project-local wrapper substantially
improves usability.

## Notes

The emphasis here is on API discovery and disciplined reuse. This helps keep the
project close to mathlib style and avoids duplicating existing convexity lemmas.
-/

namespace EconLib

section ConvexApiDiscovery

/-!
## Core set-theoretic convexity
-/

#check Convex
#check Convex.combo_mem
#check Convex.add
#check Convex.subset
#check Convex.inter
#check convex_univ
#check convex_empty

/-!
## Convex functions
-/

#check ConvexOn
#check StrictConvexOn
#check ConcaveOn
#check StrictConcaveOn

#check ConvexOn.iff_div
#check ConvexOn.iff_pairwise_pos
#check ConvexOn.smul
#check ConvexOn.add
#check ConvexOn.sub
#check ConvexOn.sup
#check ConvexOn.comp_linearMap
#check ConvexOn.comp_affineMap

/-!
## Strict convexity and related API
-/

#check StrictConvexOn.smul
#check StrictConvexOn.add
#check StrictConvexOn.comp_linearMap
#check StrictConvexOn.comp_affineMap

/-!
## Epigraph-related declarations

Borwein--Lewis makes heavy use of the epigraph viewpoint, so these are natural
targets to inspect early.
-/

#check ConvexOn.convex_epigraph
#check ConvexOn.convex_strict_epigraph
#check StrictConvexOn.convex_epigraph
#check StrictConvexOn.convex_strict_epigraph

/-!
## Order and extremum-flavoured lemmas

These may become relevant later for optimisation arguments.
-/

#check ConvexOn.map_smul
#check ConvexOn.map_add
#check ConvexOn.le_left_of_right_le
#check ConvexOn.le_right_of_left_le

end ConvexApiDiscovery

end EconLib
