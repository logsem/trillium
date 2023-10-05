# Trillium / Fairis / Aneris

Trillium is a higher-order concurrent separation logic for proving trace
refinements between programs and models. The logic is built using the
[Iris](https://iris-project.org) program logic framework and mechanized in the
[Coq proof assistant](https://coq.inria.fr/).

## Building the development

The project maintains compatibility with Coq 8.17.1 and relies on `coqc` being
available in your shell.

The recommended way to install the Coq is through [opam](https://opam.ocaml.org/doc/Install.html).

1. Install [opam](https://opam.ocaml.org/doc/Install.html) if not already
   installed (a version greater than 2.0 is required).
2. Install a new switch and link it to the project.
```
opam switch create trillium 5.1.0
opam switch link trillium .
```
3. Add the Coq and Iris `opam` repositories.
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
```
4. Install the right version of the dependencies as specified in the
   `coq-trillium.opam` file.
```
opam install . --deps-only
```

Now, make sure that the external git submodule dependencies have been cloned by
invoking
```
git submodule update --init --recursive
```

You should now be able to build the development by running `make -jN` where `N`
is the number of cores available on your machine.

## Directory Structure

- [`trillium/`](trillium/): The Trillium program logic framework

- [`fairis/`](fairis/): The Fairis instantiation of Trillium for reasoning
  about fair termination of concurrent programs.
  + [`heap_lang/`](fairis/heap_lang/): HeapLang instantiation with fuel model
    * [`examples/`](fairis/heap_lang/examples/): Examples and case studies
      - [`yesno/`](fairis/examples/yesno): Yes/No
      - [`even_odd/`](fairis/examples/even_odd): Even/Odd
      - [`choose_nat/`](fairis/examples/choose_nat): Choose nat
  
- [`aneris/`](aneris/): The Aneris instantiation of Trillium for reasoning about
    refinement of distributed systems.
  + [`examples/`](aneris/examples/): Examples and case studies
    * [`consensus/`](aneris/examples/consensus): Single-decree Paxos
    * [`gcounter_convergence/`](aneris/examples/consensus): CRDT, grow-only counter
    * [`transaction_commit/`](aneris/examples/transaction_commit): Two-Phase commit

- [`external/`](external/): External dependencies


## References from the paper to the formalization
| Item                  | File                                                                                                     | Name                                                                                                                    |
|-----------------------|----------------------------------------------------------------------------------------------------------|-------------------------------------------------------------------------------------------------------------------------|
| Definition 1.1        |                                                                                                          |                                                                                                                         |
| Definition 1.2        | [`trillium/program_logic/traces.v`](trillium/program_logic/traces.v)                                     | `continued_simulation`                                                                                                  |
| Lemma 1.3             | [`trillium/program_logic/traces.v`](trillium/program_logic/traces.v)                                     | `produced_inf_aux_trace_valid_inf`                                                                                      |
| Definition 1.4        | [`trillium/program_logic/adequacy.v`](trillium/program_logic/adequacy.v)                                 | `rel_finitary`                                                                                                          |
| Theorem 1.5           | [`trillium/program_logic/adequacy.v`](trillium/program_logic/adequacy.v)                                 | morally `simulation_correspondence_multiple`, otherwise Cleaveland and Sokolsky 2021                                    |
| Language              | [`trillium/program_logic/language.v`](trillium/program_logic/language.v)                                 | `language`                                                                                                              |
| Reduction relation    | [`trillium/program_logic/language.v`](trillium/program_logic/language.v)                                 | `locale_step`                                                                                                           |
| Weakest precondition  | [`trillium/program_logic/weakestpre.v`](trillium/program_logic/weakestpre.v)                             | `wp_def`                                                                                                                |
| Theorem 2.2           | [`trillium/program_logic/language.v`](trillium/program_logic/language.v)                                 | `wp_strong_adequacy`                                                                                                    |
| Fig. 1 and 2          | [`fairis/examples/yesno/yesno.v`](fairis/examples/yesno/yesno.v)                                         | `yes`, `no`, `start`, `the_model`                                                                                       |
| Theorem 3.1           | [`fairis/heap_lang/lifting.v`](fairis/heap_lang/lifting.v)                                               | `simulation_adequacy`                                                                                                   |
| wp e ⟨ Q ⟩            | [`fairis/heap_lang/lifting.v`](fairis/heap_lang/lifting.v)                                               | `sswp`,                                                                                                                 |
| Fig. 3                | [`fairis/heap_lang/lifting.v`](fairis/heap_lang/lifting.v)                                               | `wp_step_fuel`, `wp_role_dealloc`, `wp_step_model`, `wp_role_fork`                                                      |
| Fig. 3, program rules | [`fairis/heap_lang/lifting.v`](fairis/heap_lang/lifting.v)                                               | `wp_alloc`, `wp_store`, `wp_cmpxchg_suc`, `wp_cmpxchg_fail` `sswp_pure_step`                                            |
| Yes-No                | [`fairis/examples/yesno/yesno.v`](fairis/examples/yesno/yesno.v)                                         | `yes_no_inv`, `yes_spec`, `no_spec`                                                                                     |
| Non-deterministic nat | [`fairis/examples/choose_nat/choose_nat.v`](fairis/examples/choose_nat/choose_nat.v)                     | `ξ_cn`, `choose_nat_inv`, `choose_nat_spec`                                                                             |
| Even-Odd              | [`fairis/examples/even_odd/even_odd.v`](fairis/examples/even_odd/even_odd.v)                             | `start`, `the_model`, `evenodd_inv` `start_spec`                                                                        |
| Even-Odd              | [`fairis/examples/even_odd/even_odd_adequacy.v`](fairis/examples/even_odd/even_odd_adequacy.v)           | `evenodd_mdl_progress`, `evenodd_mdl_mono`, `ξ_evenodd_trace`                                                           |
| Fairis resources      |                                                                                                          |                                                                                                                         |
| Aneris-take-step      | [`aneris/aneris_lang/program_logic/aneris_lifting.v`](aneris/aneris_lang/program_logic/aneris_lifting.v) | `aneris_wp_atomic_take_step_model_alt`                                                                                  |
| Paxos, code           | [`aneris/examples/consensus/paxos_code.v`](aneris/examples/consensus/paxos_code.v)                       | `acceptor`, `proposer`, `leaner`, `client`                                                                              |
| Paxos, model          | [`aneris/examples/consensus/paxos_model.v`](aneris/examples/consensus/paxos_model.v)                     | `PNext`, `paxos_correct`                                                                                                |
| Paxos, resources      | [`aneris/examples/consensus/paxos_prelude.v`](aneris/examples/consensus/paxos_prelude.v)                 | `msgs_auth`, `msgs_elem_of`, `maxBal_auth`, `maxBal_frag`, `maxVal_auth`, `maxVal_frag`, `pending`, `shot`, `paxos_inv` |
| Paxos, proposer spec  | [`aneris/examples/consensus/paxos_proposer.v`](aneris/examples/consensus/paxos_proposer.v)               | `proposer_spec`                                                                                                         |
| Paxos, acceptor spec  | [`aneris/examples/consensus/paxos_acceptor.v`](aneris/examples/consensus/paxos_acceptor.v)               | `acceptor_spec`                                                                                                         |
| Paxos, learner spec   | [`aneris/examples/consensus/paxos_learner.v`](aneris/examples/consensus/paxos_learner.v)                 | `learner_spec`                                                                                                          |
| Corollary 4.2         | [`aneris/examples/consensus/paxos_adequacy.v`](aneris/examples/consensus/paxos_adequacy.v)               | `simulates`, `paxos_correct_impl`                                                                                       |

## Git submodule dependencies

This project uses git submodules to manage dependencies with other Coq
libraries. By default, when working with a repository that uses submodules, the
submodules will *not* be populated and updated automatically, and it is often
necessary to invoke `git submodule update --init --recursive` or use the
`--recurse-submodules` flag. However, this can be automated by setting the
`submodule.recurse` setting to `true` in your git config by running

    git config --global submodule.recurse true

This will make `git clone`, `git checkout`, `git pull`, etc. work as you would
expect and it should rarely be necessary to invoke any `git submodule update`
commands.

A git submodule is pinned to a particular commit of an external (remote)
repository. If new commits have been pushed to the remote repository and you
wish to integrate these in to the development, invoke

    git submodule update --remote

to fetch the new commits and apply them to your local repository. This changes
which commit your *local* submodule is pinned to. Remember to commit and push
the submodule update to make it visible to other users of the repository.

Read more about git submodules in [this
tutorial](https://git-scm.com/book/en/v2/Git-Tools-Submodules).
