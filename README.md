# Trillium / Fairis

Trillium is a higher-order concurrent separation logic for proving trace
refinements between programs and models. The logic is
built using the [Iris](https://iris-project.org) program logic framework and
mechanized in the [Coq proof assistant](https://coq.inria.fr/).

## Directory Structure

- [`trillium/`](trillium/): The Trillium program logic framework

- [`fairness/`](fairness/): The Fairis instantiation of Trillium for reasoning
  about fair termination of concurrent programs.
  * [`examples/`](fairness/examples/): examples and case studies

- [`aneris/`](aneris/): The Aneris instantiation of Trillium
  * [`examples/`](aneris/examples/): examples and case studies

- [`external/`](external/): External dependencies

## Compiling

The project maintains compatibility with Coq 8.17 and relies on `coqc` being
available in your shell. Clone the external git submodule dependencies using

    git submodule update --init --recursive

Alternatively, clone the repository using the `--recurse-submodules` flag.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

Note that the compilation of the external dependencies is known to print
a lot of warning messages when compiled with Coq 8.17.

## Directory Structure

- [`trillium/`](trillium/): The Trillium program logic framework

- [`fairness/`](fairness/): The Fairis instantiation of Trillium for reasoning
  about fair termination of concurrent programs.
  * [`examples/`](fairness/examples/): examples and case studies

- [`external/`](external/): External dependencies

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

## Publications

A [preprint](https://iris-project.org/pdfs/2021-submitted-trillium.pdf) is
available describing Trillium, a program logic framework for both proving
partial correctness properties and trace properties; Aneris is now an
instantiation of the Trillium framework.
