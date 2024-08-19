# Iris-MSWasm

This directory includes the supplementary coq material described the paper *Iris-MSWasm: elucidating and mechanising the security
invariants of Memory-Safe WebAssembly*, a submission to **OOPSLA 2024**.

# Getting Started

## Browsing the Proofs

Once the project has been compiled (see step-by-step instructions), the proofs can be browsed using Emacs and Proof General. For example,

```bash
emacs theories/irismswasm/examples/buffer/buffer_code.v
```
opens the file containing the code and specification of the buffer example from the paper. Other proofs can be browsed similarly. 


## Basic Testings

For some basic testing, the key buffer example described in the paper resides in `theories/irismswasm/examples/buffer/`, separated into three files as described in the proof of Theorem 3.2 in section 3.4. The stack example described in section 5 resides in `theories/irismswasm/examples/segstack/`, with each of its module function implemented and verified in an individual file under `theories/irismswasm/examples/segstack/function/`. We invite the reviewers to run through the code and the fully-proved specifications of each function, which are omitted in the paper due to space constraint. The stack module `stack_module` itself is implemented and verified in `theories/irismswasm/examples/segstack/segstack_instantiation.v`, importing its module functions.

As mentionned in the paper, a similar example that did not use the MSWasm extension existed in the earlier Iris-Wasm logic. This example can be found in `theories/irismswasm/examples/linstack/`. The structure of that file mirrors that of our segment stack example, for easy comparison of the examples with and without MSWasm.


# Step-by-Step Instructions

## Manual Installation and Compilation

The project can be installed using opam.

We recommend creating a new switch to start from a clean environment. The newest versions of ocaml are incompatible with our required version of Coq. We have compiled the project with version 4.13.1. The following code creates a switch with the necessary version:
```bash
opam switch create iris-mswasm-artifact-switch ocaml.4.13.1
```

Depending on the opam configuration, it may be necessary to manually switch to the newly created switch:
```bash
opam switch iris-mswasm-artifact-switch
eval $(opam env --switch iris-mswasm-artifact-switch --set-switch)
```

The following code fetches all necessary dependencies from opam and compiles the development:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam install .
```

If all necessary packages are present in the opam environment, the development can also be compiled by running
```bash
make
```

Compiling the development requires at least 8GB of RAM and may take over 30 minutes.

## Browsing the Proofs

Browsing proofs can be done conveniently in emacs. For example:

```bash
emacs theories/irismswasm/examples/buffer/buffer_code.v
```
This opens the file containing the code and specification for the buffer example using the program logic in Emacs, assuming Emacs and Proof General are installed. Other proofs can be browsed similarly. Emacs can be installed via command line:
```bash
apt install emacs
```

The instruction to install Proof General can be found at https://proofgeneral.github.io.

Although not necessary, we also recommend installing the Company-Coq plugin for pretty printing and easier editing to the proofs. The instruction to install Company-Coq can be found at https://github.com/cpitclaudel/company-coq. Company-Coq is pre-installed in the VM image provided.

### Troubleshooting

If running `make` fails, the issue is likely a missing package in opam, or a package with the wrong version. Check what version of each package opam has registered by running `opam list`. A list of necessary packages and the requirements on their versions can be found in the `dune-project` file; in case of a discrepancy, the correct version can be manually installed.

Missing packages, or packages with the wrong version, can be installed manually using `opam install`. For instance, to get the correct version of `coq-iris` or `mdx`, run:
```bash
opam install coq-iris.dev.2023-06-30.0.7e865892
opam install mdx.2.4.1
```

Some packages are in the `coq-released` repository or in the iris development repository; in order to let opam know where to fetch these, before running `opam install` run:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
```

A shorthand to install all missing dependencies and compile the development is:
```bash
opam install .
```


### Warnings that are Safe to Ignore

When browsing the proofs in Emacs + Proof General, a warning on boolean coercion will pop up in the Coq response prompt when the theorem prover runs past the imports. This is because two of our dependencies, ssreflect and stdpp, each implements its own coercion of Bool into Prop, resulting in ambiguous coercion paths. However, this can be safely ignored since the two implementations are essentially the same.


## Claims Supported and Not Supported by the Artifact

This artifact is a fully-verified implementation in Coq of the program logic proposed in the paper supporting all claims of the paper. Some simplification has been made in the presentation of the paper for space constraints, and we have tried our best to highlight all such differences in the section `Differences with Paper` in the end.

We invite the reviewer to compare the key claims made in the paper against the code for a demonstration of completeness. We suggest starting from the buffer example, which is the main running example in the paper, and the segment stack example, which is detailed in Section 5. Other examples, as well as the implementation of the program logic itself, can also be studied if interested. The detailed locations and an outline of them can be found under the `Structure` section below.

The remaining part of this readme aims to explain the structure of the artifact, and to provide directories and paths to locate the items that have appeared in the paper.


# Directories

For each figure and theorem in the paper, we provide the approximate paths, names, and line numbers (where applicable), under `theories/`, to indicate the location of them in the code. We also provide a general pointer for each subsection in Section 2 and Section 3 for the related files in the codebase. For a detailed breakdown of the code structure, see the `Structure` section later.
The stack example is not discussed in the submitted version of the paper.

| Location in Paper | Location in Code |
|--|--|
| Fig. 1 | `irismswasm/examples/buffer/buffer_code.v` |
| Fig. 2 | `mswasmcert/datatypes.v` | 
| Section 2 | `mswsamcert/opsem.v` |
| Section 2.2 | `mswasmcert/handle.v`, `mswasmcert/segment_list.v` |
| Fig. 3 | `mswasmcert/segment_list.v` (`compatible`, line 72), `mswasmcert/operations.v` (`salloc`, line 182 and `sfree`, line 210) |
| Fig. 4 | `mswasmcert/opsem.v` |
| Section 3.1 | `irismswasm/language/iris/iris.v`, `irismswasm/rules/iris_rules_resources.v` (`wp_load`, line 1833) |
| Fig. 5 | `irismswasm/language/iris_wp_def.v` (Resource ownerships, line 132) |
| Fig. 6 | `irismswasm/rules/iris_rules_segment.v` (`wp_segload`, `wp_segload_xxx`, etc) |
| Fig. 7 | `irismswasm/rules/iris_rules_segment.v`, `irismswasm/rules/iris_rules_pure.v` (`wp_xxx`, etc) |
| Section 3.3 | `irismswasm/examples/buffer/buffer_code.v` (`buffer_spec`, line 60) |
| Theorem 3.1 | *Iris from the ground up, FP18* (section 6.4) |
| Theorem 3.2 | `irismswasm/examples/buffer/buffer_adequacy` (`buffer_adequacy`, line 136) |
| Section 4.2 | `irismswasm/logrel/iris_logrel.v` |
| Fig. 8 | `irismswasm/logrel/iris_logrel.v` (`interp_value_handle_0`, line 111 and `interp_val`, line 174) |
| Fig. 9 | `irismswasm/logrel/iris_logrel.v` (`interp_allocator`, line 152) |
| Fig. 10 | `irismswasm/logrel/iris_logrel.v` (`interp_frame`, line 183 and `interp_expression`, line 596 and `semantic_typing`, line 651) |
| Theorem 4.1 | `irismswasm/logrel/iris_fundamental.v` (`be_fundamental`, line 69) |
| Section 4.3 | `irismswasm/examples/buffer/buffer_code.v` (fundamental theorem applied on line 307) |
| Section 5 | `irismswasm/examples/segstack/` (see `Structure` below for an overview of the files) |
| Fig. 11 | `irismswasm/examples/segstack/segstack_robust.v` (`main`, line 33 and `stack_adv_client_instantiate`, line 559) |
| Theorem 5.1 | `irismswasm/examples/segstack/segstack_robust_adequacy.v` (`segstack_adequacy`, line 212) | 
  

# Structure

In this section, we describe the structure of the implementation.

  
## MSWasmCert

Our work builds on the mechanisation of WebAssembly 1.0 by Watt et al. in *Two Mechanisations of WebAssembly, FM21*. As a result, our work inherits many files from Watt et al's mechanisised proofs, makes small changes to many files, and creates a few novel files. These files are located under `theories/mswasmcert`. We bring up the files most related to our work for completeness:

- `handle.v` defines handles;

- `segment_list.v` defines segments and allocators;

- `datatypes.v` contains all the basic MSWasm data types definitions;

- `opsem.v` defines the operational semantics of MSWasm;

- `typing.v` defines the type system for MSWasm instructions, closures, and stores, and configurations.

- `instantiation.v` contains the definition of the module instantiation predicate in the official specification, as well as all the sub-predicates it depends on.


## Defining the MSWasm Language in Iris

Under `theories/irismswasm/language`, we instantiate the Iris Language framework with the MSWasm language, and prepare the preambles for our program logic and logical relation.


- `iris/iris.v`: instantiates Iris Language by defining the logical values, expressions, and proving the necessary properties for them etc.;

- `iris/iris_locations.v`: sets up the necessary details to express and manipulate the memory model of the language;

- `iris_wp.v`, `iris_wp_def.v`: sets up a custom weakest precondition to be used for our language, which differs slightly from the standard construct that Iris provides; defines the memory model of the language;

- `iris_atomicity.v`: contains a definition of which expressions are considered atomic in Iris, and proves the definition is sound.

  

## Helper Properties for the Language

  
Under `theories/irismswasm/helpers`, we establish a lot of auxiliary properties about either the MSWasm Semantics itself, or the plugging-in version of the semantics in Iris.

  

## Proof Rules for MSWasm
  

Under `theories/irismswasm/rules`, we proved a vast number of proof rules that can be used to reason about WebAssembly programs. Most of these rules are inherited directly from the earlier Iris-Wasm logic for plain WebAssembly. Our main contribution is in:

- `theories/irismswasm/rules/iris_rules_segment.v`: contains proof rules for the MSWasm-specific instructions.

The other files in the folder are mostly unchanged from Iris-Wasm, and are:

- `theories/irismswasm/rules/iris_rules_pure.v`: contains proof rules for *pure* instructions, i.e. those whose reduction semantics are independent from the state (for example, the `wp_binop` rule in Line 260);

- `theories/irismswasm/rules/iris_rules_control.v`: contains proof rules for control instructions;

- `theories/irismswasm/rules/iris_rules_resources.v`: contains proof rules that directly access the state, such as memory instructions;

- `theories/irismswasm/rules/iris_rules_call.v`: contains proof rules related to function calls;

- `theories/irismswasm/rules/iris_rules_structural.v`: contains structural proof rules to deal with sequencing of instruction sequences, possibly within evaluation contexts;

- `theories/irismswasm/rules/iris_rules_trap.v`: contains structural proof rules that allow reasoning when a part of the expression produce traps;

- `theories/irismswasm/rules/iris_rules_bind.v`: contains several bind rules for binding into evaluation contexts;

- `theories/irismswasm/rules/iris_rules.v`: imports everything above, allowing users to import all proof rules at the same time more easily.

  

## Host Language and Instantiation Lemma

Like plain WebAssembly code, MSWasm code runs embedded in a host language. The earlier Iris-Wasm program logic for plain WebAssembly defined a custom host language that is able to instantiate WebAssembly modules and perform a few other operations. We have made minor modifications to these files to accomodate for MSWasm.

- `theories/irismswasm/instantiation/iris_instantiation.v` and `theories/irismswasm/instantiation/instantiation_properties.v`: contains the module instantiation resource update lemma and other properties pertaining to module instantiation

- `theories/irismswasm/host/iris_host.v`: defines a custom-made host language and establishes a set of proof rules for the host language required for reasoning about examples.


## Logical Relation

  

Under `theories/irismswasm/logrel/`, we build a logical relation on top of the program logic we've established. This logical relation extends the one defined by the Iris-Wasm program logic for plain WebAssembly. 
  

- `iris_logrel.v`: contains the definition of all logical interpretations, including the interpretation for values (Figure 8) and allocators (Figure 9), as well as the excerpts from Figure 10. This file is the base of the logical relation.

- `iris_fundamental_(xxx).v`: each of these files contains the proof to a case of the Fundamental Theorem for one single instruction. The files associated to instructions introduced by MSWasm are ours, the rest is largely unchanged from the previous Iris-Wasm work.

- `iris_fundamental.v`: imports all the case files above and derive the Fundamental Theorem (Theorem 4.1) in the paper, and its corollaries.

- `iris_interp_instance_alloc.v`: proves the module instantiation allocates the correct Iris invariants as expected, which is used for the robust safety examples later.

  

## Examples

Under `theories/irismswasm/examples/`, we formulated the examples for our project, some of which were discussed in the paper. We bring up the key files below:

### Buffer example

Fold `buffer/` contains the buffer example presented in the paper.

- `buffer_code.v`: contains the MSWasm code for the buffer example, and a proof of its specification

- `buffer_instantiation.v`: defines the buffer module and proves its instantiation specification

- `buffer_adequacy.v`: contains a proof for a statement that only mentions the operational semantics of MSWasm (not Iris), using the adequacy lemma of Iris. This showcases that Iris need not to be in our trusted computing base.

### Stack example

Folder `segstack/` contains the stack example from Section 5.

- `function/segstack_common.v`: includes some useful definitions and properties that are shared across the stack example.

- `function/(function_name).v`: provides the body of the functions declared in the stack module and proves a specification for them within our program logic;

- `segstack_instantiation.v`: defines the stack module and proves its instantiation specification.

- `segstack_client.v`: defines a client module that can use imports from the stack module and proves its instantiation specification.

- `segstack_with_reentrancy.v`: defines a more sophisticated client module that features a reentrant host call to demonstrate interoperation between the WebAssembly the host weakest precondition.

- `segstack_robust.v`: defines yet another client module that imports an unknown module in addition to the stack module, and demonstrates the encapsulation property that can be obtained (discussed in Section 5).

- `segstack_robust_adequacy.v`: applies adequacy on the above example.

The similar example defined by the earlier Iris-Wasm work can be found in the `linstack/` folder. This folder's structure is similar to `segstack/`. One key difference that showcases the difference of plain WebAssembly and MSWasm is found in `linstack/stack_robust.v`, where the result in plain WebAssembly is contingent on the adversary module not having access to the stack functions, as explained in Section 5.


### Plain WebAssembly examples

Folder `plainWasm/` contains examples that do not use the new instructions from MSWasm. This showcases that Iris-MSWasm still allows to reason about the same examples Iris-Wasm could reason about. These examples are not discussed in the paper.

- `iris_examples.v`: contains several simpler preliminary examples to help understand the program logic without involving modules and the host language.

- `iris_examples_factorial.v`: contains an examples that uses Landin's Knot to implement a factorial function through store recursion.

- `iris_robust_examples.v`: a simpler robust safety example, containing an example host program which instantiates an adversary module followed by a trusted module. The trusted module calls an imported function from the unknown adversary module. We then demonstrate the robust safety property, where we have local state encapsulation in the presence of unknown code.

- `iris_robust_example_host.v`: contains a variation of the above example, in which the adversary module imports a host function. The example demonstrates the integration between the logical relation and the host language.

- `iris_robust_examples_adequacy.v`: applies adequacy on the above example.

### Basic MSWasm examples

Folder `segment/` contains a number of basic examples that highlight some properties of the MSWasm handles. These examples are not discussed in the paper.


# Differences with Paper
  

## Definitions

The definitions within our work were designed in a way that would fit best in an interactive proof environment, to facilitate sustainable engineering in the long term. Therefore, some definitions, especially the constructors of inductive and records, are either named or designed in a verbose way.
  

There are two major categories of differences:
  

### Removing naming prefixes

In the code, we exercise a naming convention for most constructors of inductive definitions and record by adding prefixes to them, so that it is possible to deduce the source of these constructors by looking at the prefix. Oftentimes these prefixes are in acronyms of the source definition (for example, `BI_` for each constructor of basic instructions).

  

### Removing trivial constructors

  

The large records in WebAssembly often involve fields of the same type (for example, in the `instance` definition, the addresses of `functions`, `tables`, `memories`, and `globals` are all immediate (isomorphic to naturals). In the code, we sometimes add another layer of constructor for each of them when unintended uses are possible (for example, looking up in `tables` by using a `memory` export reference).

  

### Other differences in names


Some other name differences include:

- We use the word 'instruction' a lot. As we illustrate in Fig. 2, these are actually separated into *basic instructions* and *administrative instructions*. Hence in our code, these are called `basic_instruction` and `administrative_instruction`, both of which are defined in `theories/mswasmcert/datatypes.v`

- In Section 3.1, we introduce 'logical values'. In the code, these are simply called `val` and are defined in `theories/irismswasm/language/iris/iris.v` (line 16).

  

## Names of Predicates

There are some differences in the names used in the paper and the code for the components of our logical relation (Section 4). Unless specified otherwise, all the code is in `theories/irismswasm/logrel/iris_logrel.v`.

- `V[[ts]]` (Fig. 8) is called `interp_val` in the code (line 174)
- `V0[[t]]` (Fig. 8) is called `interp_value` in the code (line 163)
- `A` (Fig. 9) is called `interp_allocator` in the code (line 152)
- `cinvOpt` (Fig. 9) is introduced for readability, the code simply inlines the definition of the predicate in the definition of `interp_allocator`
- `Frame[[ts]]` (Fig. 10) is called `interp_frame` in the code (line 183)
- `E[[ts]]` (Fig. 10) is called `interp_expression` in the code (line 596)
- The double turnstile `|=` (Fig. 10, Theorem 4.1) is called `semantic_typing` in the code (line 651)
- The single turnstile `|-` (Theorem 4.1) is called `be_typing` in the code (`theories/mswasmcert/typing.v`, line 67)

  

## Differences in WP rules and lemmas

- WP rules and frame resource: in the code, the frame resource is occasionally put under a magic wand rather than in postcondition as is presented in the paper; the two presentations are equivalent. Putting the frame resource in the postcondition is more readable, but putting it under a magic wand is more useful when conducting a mechanised proof.

- WP vs Hoare Triple: the paper often prefers using hoare triples (say, in section 3.3 or the proof of Theorem 3.2) as this is more readable. The code often uses weakest precondition statements instead as this is easier to manipulate in practice.




