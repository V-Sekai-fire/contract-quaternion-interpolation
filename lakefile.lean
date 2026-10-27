import Lake
open Lake DSL

-- Property checks for Godot's spherical cubic and makima quaternion interpolation.
-- QInterp/Model.lean ports core/math/quaternion.cpp, core/math/basis.cpp and the
-- makima code in scene/resources/animation.cpp to Lean Float, once before the
-- "Make Quaternion cubic/makima interpolation more stable" change (old) and once after (new).
package «quaternion_interpolation» where

-- Plausible v4.34.0 of the V-Sekai-fire fork, the commit swing-twist-kusudama pins.
require plausible from git
  "https://github.com/V-Sekai-fire/plausible.git" @ "118aa17ee84656b8bd727fef7c458ee8c833385c"

@[default_target]
lean_lib «QInterp» where

-- Runs every property through Plausible, then sweeps generated cases and writes
-- each failure to out/failures.jsonl and out/test_quaternion_interpolation_lean.cpp. Exits 1 if the
-- fixed model fails anything or a control (old, patch) fails nothing.
@[default_target]
lean_exe «qinterp» where
  root := `Main
