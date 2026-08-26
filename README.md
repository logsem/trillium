# Trillium fork for wait-freedom

This is a fork of Trillium framework developed for the ["Verifying wait-freedom for concurrent higher-order programs", ECOOP'26](https://doi.org/10.4230/LIPIcs.ECOOP.2026.20) paper. 
It is used in the [up-to-date technical development of Lawyer and wait-freedom](https://github.com/logsem/lawyer), as well as in the artifact for the wait-freedom paper.

It is meant to be used as a dependency; see [Lawyer development](https://github.com/logsem/lawyer) for an example.

## Notable changes compared to upstream Trillium

- Generalization of weakest precondition parameterized with the bit that allows or prohibits forking: `trillium/bi/weakestpre.v`
- Definition of the progress resource and proof of conditional adequacy theorem: `trillium/program_logic/adequacy_cond.v`
- Definition of traces: `trillium/traces/inftraces.v`, definition `trace`.
- Definitions of trace state and label lookups: `trillium/traces/trace_lookup.v`, definitions `state_lookup` and `label_lookup` correspondingly.
- Definition of trace validity: `trillium/traces/inftraces.v`, definition `trace_valid`; also see `trillium/traces/trace_lookup.v`, lemma `trace_valid_steps''`.
