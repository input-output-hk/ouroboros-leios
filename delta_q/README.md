# Delta-Q utilities for Rust

the paper: <https://www.preprints.org/manuscript/202112.0132/v3>

The goal of this project is to provide tooling that is easy to use for designers of decentralised systems to model their network and assess communication timeliness and resource usage.
This should be supported by a web UI that allows modelling CDFs (cumulative distribution function), named outcome expressions, and constraints/expectations.
The underlying ΔQ expressions shall be used for export/import of the model, complemented with a library for CDF constructors (like step function etc.).

## Implementation plan

The first step is to provide a library for manipulating CDFs, offering all operations required by the theory; the internal representation will be discrete numerical [DONE], with later optimizations for constant parts at the beginning and end of the vector. [DONE]

The second step yields an internal DSL for creating ΔQ expressions and printing them. [DONE]

The third step provides evaluation of ΔQ expressions as defined in the paper. [DONE]
This will later be expanded to include some exponentiation-like operator that simplifies expressing a randomly chosen repetition count for some sub-expression (as frequently occurs in gossip protocols). [DONE]

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
- `cargo run --bin editor -F main`

The first one uses [trunk](https://trunkrs.dev) to build the web app in the `dist/` folder, which the second one then integrates into the single-binary application that will serve HTTP resources on port 8080 when run.

When developing the web UI part you can leave `cargo run --bin editor` running while using `trunk serve` to serve the UI with change detection.
Requests to the `delta_q/*` endpoints will be proxied.

### Troubleshooting

Depending on local Rust configuration, building the web app might be less straightforward.

Trunk needs the Wasm bindings generators but they are not installed by default at least on MacOS M1:

```
cargo install --locked wasm-bindgen-cli
```

It also needs a Wasm toolchain:

```
rustup target add wasm32-unknown-unknown
```

## Known Shortcomings

- functional but ugly
- duplicates state management in web app and backend, not yet decided what to put where (currently ΔQ expression evaluation is done in the backend, could easily move to a web worker)
- should have export (probably as JSON) and matching import
