# Delta-Q utilities for Rust

the paper: <https://www.preprints.org/manuscript/202112.0132/v3>

The goal of this project is to provide tooling that is easy to use for designers of decentralised systems to model their network and assess communication timeliness and resource usage.
This should be supported by a web UI that allows modelling CDFs (cumulative distribution function), named outcome expressions, and constraints/expectations.
The underlying ΔQ expressions shall be used for export/import of the model, complemented with a library for CDF constructors (like step function etc.).

## Extensions to the theory

One shortcoming of the published theory is that it doesn't make it obvious how to model not only timeliness but also resource usage a.k.a. perform a load analysis.
To this end, this tool contains an extension of the syntax in two ways:

1. the basic outcome constructor `CDF[...]` accepts a postfix `WITH <metric>[...]` that may be supplied any number of times to register some step functions for resource usage of performing this outcome
2. the sequence operator `->-` accepts a load factor update of the form `->-×X+Y` which means that the right-hand side will have its load metrics scaled up by a factor that is obtained by taking the factor currently in effect, multiplying it by X and then adding Y (both components are optional)

The rules for evaluating the load metrics of outcomes are as follows:

- `a ->- b` will have the load metrics of `a` plus the load metrics of `b` convoluted with the timing CDF of `a` (i.e. the resources are used in a delayed fashion as described by the gradual completion of `a`)
- `a L<>R b` is the choice of `a` with weight `L` or `b` with weight `R`; the load metrics of `a` and `b` are thus averaged using the same weights
- `∀(a | b)` performs both `a` and `b`, therefore the load metrics are added
- `∃(a | b)` also performs both `a` and `b` and thus also sums up their load metrics

If you want to model that `b` can only start after `a` has been done, you should model it as `∀(a | CDF[(<delay>,1)]) ->- b` where `delay` is the duration after which `a` is considered finished.

> Note that in the syntax `->-` binds more closely than `L<>R` and both operators are **right-associative**.
> This is for convenience in modelling choice ladders and reading them from left to right, as well as managing load factors when reading left to right. `(a ->-+1 b) ->- c` only uses the increased load factor for `b` while `a ->-+1 b ->- c` also applies it to `c`.

## Building and Running

The example application is a pure web application that runs in the browser and is built and served using `trunk`.
You'll need to install the WASM toolchain as well:

```sh
rustup target add wasm32-unknown-unknown

cargo install --locked trunk

# it has been reported that the following might be necessary as well
cargo install --locked wasm-bindgen-cli
```

## Known Shortcomings

- functional but ugly
