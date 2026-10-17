# Fetch Scheduler Plan

## Trajectory

### Phase 1: Design (`DESIGN.md`)

Explain the problem, motivate the approach, and document design decisions.
This is the "why" and "what" — readable by anyone, no code required.
Iterate until the design is stable enough to specify.

### Phase 2: Specify (`FetchScheduler.py`)

Write the scheduling policy as a pure Python state machine: `(state, event) → (state, [actions])`.
This is both the reference specification and the executable prototype.
Test it with synthetic event traces and property-based tests.

Embed CPython in the C node (`Python.h`) so the policy runs live in the Mininet simulation.
The C node owns networking and the event loop; `FetchScheduler.py` is the policy brain.
This lets us iterate on the policy against real network behavior without touching C.

Phases 1 and 2 overlap — simulation results inform design revisions, and design revisions change the spec.

### Phase 3: Translate (`FetchScheduler.c`)

Once the Python spec is stable, translate it to C.
The C code should be a structural translation — same states, same transitions, same action types.

Verify equivalence by feeding identical event traces to both implementations and diffing the action sequences.
Traces come from two sources:

- **Recorded**: capture `(event, state, actions)` triples during simulation runs with the embedded-Python node. These cover realistic event orderings and timing.
- **Fuzzed**: differential fuzzing with synthetic event streams — arbitrary well-formed events (valid types and field ranges as defined by the event schema), in arbitrary order, including causally nonsensical sequences. The goal is equivalence under all well-formed inputs, not just realistic ones. If the two implementations diverge on a nonsensical trace, that's still a translation bug.

The Python spec remains the source of truth; the C translation is an optimization.
