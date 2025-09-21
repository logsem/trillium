# Trillium / Fairis

Trillium is a higher-order concurrent separation logic for proving trace
refinements between programs and models. The logic is
built using the [Iris](https://iris-project.org) program logic framework and
mechanized in the [Rocq proof assistant](https://rocq-prover.org/).

## Directory Structure

- [`trillium/`](trillium/): The Trillium program logic framework

- [`heap_lang/`](heap_lang/) - a variation of HeapLang language (most notably - enriched with locales)

- [`fairness/`](fairness/) - a number of various trace and model utilities; most notably - a uniform definition of trace and model fairness.

- [`fairis/`](fairis/) - The Fairis program logic - an instantiation of Trillium for reasoning about fair termination of HeapLang programs.


## Compiling

    # create a new opam environment
    opam switch create trillium_env 5.2.0
    # switch into the new environment
    eval $(opam env --switch=trillium_env)
	
    # set up repository for Rocq packages
    opam repo add rocq-released https://rocq-prover.github.io/opam/released/

    # install all dependencies of Trillium
    opam install . --deps-only
    # build Trillium; adjust the number of jobs as needed
    make -j 5

## Using Trillium in your project

The instruction below applies until Trillium is released as a publicly available opam package.

Your project should be set up as an opam package. 
With that, add the Trillium dependency to its `.opam` file:

    depends: [
      # ...
      "trillium" { (= "2.2.0") }
    ]

Then, clone the Trillium repo at some local path TRILLIUM_PATH.
After that, execute the following in the root of your project:
    
    # create a new opam environment for your project
    opam switch create project-env 5.2.0
    # switch into the new environment
    eval $(opam env --switch=project-env)
	
    # set up repository for Rocq packages
    opam repo add rocq-released https://rocq-prover.github.io/opam/released/
    # set up the local repository for Trillium
    opam pin add trillium TRILLIUM_PATH --no-action

    # install all dependencies of your project; Trillium will be installed as a part of it
    opam install . --deps-only
    # build your project
    make -j 5	
	

## Publications

- Trillium: Higher-Order Concurrent and Distributed Separation Logic for Intensional Refinement.
 
  Amin Timany, Simon Oddershede Gregersen, Léo Stefanesco, Jonas Kastberg Hinrichsen, Léon Gondelman, Abel Nieto, Lars Birkedal.
  
  In POPL 2024: ACM SIGPLAN Symposium on Principles of Programming Languages
