# contract-quaternion-interpolation

Property checks of Godot's quaternion interpolation, in Lean 4 with Plausible.

`QInterp/Model.lean` ports the C++ to Lean `Float`: `Quaternion::spherical_cubic_interpolate`,
`Quaternion::spherical_cubic_interpolate_in_time` and `Animation::spherical_makima_interpolate_in_time`,
with the code they call (`log`, `exp`, `slerp`, `get_nearest_log`, the `Basis` round trip,
`Math::cubic_interpolate`, `Math::cubic_interpolate_in_time` and the makima scalar code).
It has three versions:

| Version | Code |
| --- | --- |
| `old` | before godot PR 124915, "Make Quaternion cubic/makima interpolation more stable" |
| `patch` | the PR as written |
| `fixed` | the PR plus two fixes: normalize the pre-blend `slerp`, and make `cubic_interpolate_in_time` return `from` and `to` at its ends when key times coincide |

`QInterp/Props.lean` generates inputs and states the properties. Most inputs are smooth key
tracks, as an animation holds. The rest are tracks with random signs, fast spins, nearly equal
keys, half turns and random keys. Key times include coincident keys.

| Property | Statement |
| --- | --- |
| finite | no NaN or infinity |
| unit | the result is a unit quaternion |
| endpoint0, endpoint1 | weight 0 gives `from`, weight 1 gives `to` |
| constant | equal keys give that key |
| reversal | swapping the ends, mirroring the times and using `1 - weight` gives the same rotation |
| left_invariance | `f(g * keys) = g * f(keys)` |
| geodesic | evenly spaced keys on one great circle give `slerp(from, to, weight)` |
| continuity | a 1e-4 step in weight moves the result less than 1e-2 |
| time_uniform | the in-time version with times 1, -1, 2 equals the plain version |
| get_nearest_log | `exp` of the result is the input, and no other 720-degree shift is nearer |

## Run

    lake build
    lake exe qinterp          # 20000 sweep cases; pass a number to change it

The run is deterministic. It writes `out/`:

- `plausible.txt`: one Plausible search per function, property and version
- `failures.jsonl`: every failure of the sweep, with its full input
- `failure_counts.tsv`: failures per function, property and version
- `test_quaternion_interpolation_lean.cpp`: a Godot doctest file of the `old` and `patch` failures
  that are large enough to show at float `real_t`, up to 5 per function, property, family and version

It exits 1 if the `fixed` version fails anything, or if a control finds nothing: `old` must fail
reversal, and `patch` must fail unit, endpoint0 and endpoint1.

## Results (20000 cases)

| Property | `old` | `patch` | `fixed` |
| --- | --- | --- | --- |
| reversal | 8856 / 9287 / 9006 (cubic / in time / makima), error up to 1.39 | 0 | 0 |
| geodesic | 20 per function, error up to 5e-6 | 0 | 0 |
| unit | 0 | 276 per function, error up to 2e-6 | 0 |
| endpoint0 / endpoint1 (in time) | 951 / 1001, error up to 1.41 | 951 / 1001 | 0 |

The generated C++ file is `tests/core/math/test_quaternion_interpolation_lean.cpp` on
[V-Sekai-fire/entities-godot `feat/quaternion-stable-cubic-interp`](https://github.com/V-Sekai-fire/entities-godot/tree/feat/quaternion-stable-cubic-interp),
which carries the PR and both fixes. In a Godot build of that branch every row passes. In a build
of the PR alone, the 50 endpoint rows of an earlier unseeded run failed with the same errors as the Lean model, to 5 or 6 digits.
