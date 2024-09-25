# Delta-Q utilities for Rust

the paper: <https://www.preprints.org/manuscript/202112.0132/v3>

The goal of this project is to provide tooling that is easy to use for designers of decentralised systems to model their network and assess communication timeliness and resource usage.
This should be supported by a web UI that allows modelling CDFs (cumulative distribution function), named outcome expressions, and constraints/expectations.
The underlying ΔQ expressions shall be used for export/import of the model, complemented with a library for CDF constructors (like step function etc.).

## Implementation plan

The first step is to provide a library for manipulating CDFs, offering all operations required by the theory; the internal representation will be discrete numerical [DONE], with later optimizations for constant parts at the beginning and end of the vector.

The second step yields an internal DSL for creating ΔQ expressions and printing them. [DONE]

The third step provides evaluation of ΔQ expressions as defined in the paper. [DONE]
This will later be expanded to include some exponentiation-like operator that simplifies expressing a randomly chosen repetition count for some sub-expression (as frequently occurs in gossip protocols).

The fourth step adds a web UI to expose the internal DSL to no-code users. [DONE]
The interaction with a ΔQ expression shall closely resemble the refinement approach for system modelling as defined in the paper. [DONE]
It will allow the system designer to see immediately the result of the current model [DONE] and how its computed attenuation compares to the expectation or constraints.

In addition and in parallel to the above, the theory shall be better understood and where required enhanced to support not only timeliness analysis but also load prediction.
It is expected that while the same system model can be used for both aspects, the inputs for the load analysis need to be somewhat different from CDFs, i.e. they will likely require more information.

## Caveats

Since the timing CDFs don't model load dependence, they are only representative of the unloaded system.
The results of the load analysis will indicate where and under which conditions this assumption will be broken, but it isn't obvious how to feed that information back into a changed CDF to adapt the timeliness analysis to those circumstances.

## Building and Running

The build comprises two steps:

- `trunk build` (i.e. you’ll need to `cargo install --locked trunk` first)
- `cargo run --bin editor`

The first one builds the web app in the `dist/` folder, which the second one then integrates into the single-binary application that will serve HTTP resources on port 8080 when run.

When developing the web UI part you can leave `cargo run --bin editor` running while using `trunk serve` to serve the UI with change detection.
Requests to the `delta_q/*` endpoints will be proxied.

## Known Shortcomings

- not optimised at all, especially regarding memory usage (need to make cloning cheap for CDF, DeltaQ, etc.) and web assembly size
- functional but ugly
- duplicates state management in web app and backend, not yet decided what to put where (currently ΔQ expression evaluation is done in the backend, could easily move to a web worker)
- no editing of CDFs yet
- should have export (probably as JSON) and matching import
- should allow editing the formulas as text, which requires making the syntax more accessible via normal keyboards
- fixed samples and width for CDF, should be changed to support any step function and compute its width dynamically (with upper bound on details to avoid memory explosion)
- should add “exponentiation” operator to wrap an expression in another one with a hole for a specified number of times
