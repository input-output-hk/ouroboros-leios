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

## Additional syntactic tools

The following extensions do not change the underlying theory but provide syntactic abstractions that simplify the formulation of certain repetitive ΔQ expressions.

### Bounded recursion

Unfolding expressions using name resolution normally rejects names that are currently being expanded: as there are no conditionals or other logic to supply termination conditions, any recursion would be an infinite loop.
Sometimes, ΔQ expressions feature a repeating structure, though, which can be expressed more succinctly as “do this thing five times”.
A simple example is the sequencing of the same outcome for a number of times:

    five := one ->- one ->- one ->- one ->- one

This can be expressed more concisely as

    oneRec := oneRec ->- one
    five := oneRec^5

(recall that `->-` is right-associative)
The precise process is to allow the recursive name to be resolved five levels deep; at the sixth call the ⊤ (top) outcome is returned instead and recursion stops.
The expression may use the recursive name any number of times, but beware of the exponential explosion of the expression size.
The web application should fail gracefully, but computations may take many seconds when constructing expressions of millions of combinators.

### Gossip operator

Since this library is being developed in the context of the Cardano peer-to-peer network, epidemic information diffusion — a.k.a. a gossip protocol — plays a major role.
Typical ΔQ expressions involve terms like

    hopIB 0.6<>99.4 hopIB ->- hopIB 8.58<>90.82 hopIB ->- hopIB ->- hopIB 65.86<>24.96 hopIB ->- hopIB ->- hopIB ->- hopIB

modelling an empirically determined distribution of the diffusion process using a combination of one through four messaging steps (the underlying network is assumed to consist of roughly 2500 nodes with a connection graph of average degree 15).

Very similar expressions can be generated using the `gossip()` operator, where

    gossip(hopIB, 2500, 15, 0.07)

means that information starts out at a single node and is at each step spread to 15 neighbors until all 2500 nodes have been reached.
The fourth parameter is the average local cluster coefficient of the network, which describes which fraction of a node’s neighbors are directly connected to each other — which will lead to duplicate information transfers that are then assumed to not actually perform the `hopIB` outcome via deduplication.

Adding this operator makes it easier to play with different network sizes or suggested peering schemes.

Mathematically, the gossip operator is expanded by computing expectation values for the number of new nodes reached within each diffusion “round”.
You can see the resulting expression by clicking on the syntax element in the graphical representation.
Note how the messaging steps are sequenced using the `->-` combinator which takes into account the probabilistic timing of each outcome; the rounds visible in the ΔQ structure are therefore not synchronised but describe the fully parallel spread of information across the network.

Caveats are that non-scale-free networks exhibit structure that may not be adequately captured by the above parameters, the `gossip()` operator assumes a random small-world network.
In the case of Cardano it may be more accurate to model the diffusion across computing centers using this operator, followed by the much quicker diffusion within a certain location as a second step.

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
