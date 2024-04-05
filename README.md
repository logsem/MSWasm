# Usage

## Installation and Compilation

The project comes with an `esy` packaging.

The following programs are assumed to be installed: `git`, `curl`, `m4`, `autoconf`, and `automake`.
These programs are used to fetch and compile dependencies.

Installing `esy` itself can be done through `npm`.
It should then look like something like that:
```bash
sudo apt install npm git curl m4 autoconf
sudo npm install --global esy@latest # Tested with version 0.7.2 of esy.
```
Note that despite using `npm` to be installed, `esy` is not JavaScript-based.
If you prefer to avoid `npm` altogether, there are other ways to install `esy`: see <https://esy.sh/> for more information.

Once `esy` is installed, simply type `esy` to download and install the dependencies and compile everything.
```bash
esy
```

Compiling the dependencies may require at least 16GB of RAM.

## Troubleshooting

- On MacOS Monterey, it is required to use at least esy >=0.6.12 as there is a sandboxing bug for versions below that.

- Due to compatibility issues of several dependencies, the codebase currently fails to build on any OS using glibc >= 2.34.

## Editing the Project

Type `esy shell` to open a shell with the right compilation environment.
You can also type `esy emacs theories/wasm.v` to open Emacs with the right environment (assuming that Emacs is installed with Proof General in your system).
Note that `emacs theories/wasm.v` (without the `esy` prefix) will open Emacs without setting the local dependencies: doing so will likely prevent `coq` from finding the needed dependencies.

To use CoqIDE in this developpment, you first need to install its system dependencies (these are probably already installed on your system if you are using CoqIDE):
```bash
sudo apt install libcairo2-dev libexpat1-dev libgtk-3-dev libgtksourceview-3.0-dev
```
Then, replace the line `devDependencies: {},` by `devDependencies: {"@opam/coqide": "*"}` in [package.json](./package.json), and run `esy` again.
Typing `esy coqide theories/wasm.v` should now work.

To use VSCode in this development, a [.vscode/settings.json](.vscode/settings.json) needs to be generated first: this file enables VSCode to know where the dependencies are stored in your system.
It can be generated with `esy vscode`.

The [tests](./tests) folder contains Markdown files checked by `mdx` during the continuous integration.


# Organization

Here is a lookup table for the definitions in the paper.

| *paper* | *file* or *folder* | *name* |
| --- | --- | --- |
| Code for the buffer example (Fig 1) | theories/iris/examples/buffer/buffer\_code.v | `buffer\_program` |
| MSWasm abstract syntax tree (Fig 2) | theories/datatypes.v | |
| Helper rules for the allocator (Fig 3) | theories/operations.v | `sfree` and `salloc` |
| Operational semantics of MSWasm (Fig 4) | theories/opsem.v | |
| Points-to resources (Fig 5) | theories/iris/language/iris\_wp\_def.v | |
| WP-rules for segload, segstore, segalloc and segfree (Fig 6 and 7) | theories/iris/rules/iris\_rules\_segment.v | e.g. `wp\_segload` or `wp\_segfree\_failure3` |
| WP-rules for slice and handle.add (Fig 7) | theories/iris/rules/iris\_rules\_pure.v | e.g. `wp\_handleadd` or `wp\_slice\_failure` |
| Specifying the buffer example (Sections 3.3 and 4.3) | theories/iris/examples/buffer/buffer\_code.v | `buffer\_spec` |
| Adequacy theorem (Theorem 3.1) | theories/iris/language/iris\_adequacy.v | `wp\_adequacy` |
| Adequacy of the buffer example (Theorem 3.2) | theories/iris/examples/buffer/buffer\_adequacy.v | `buffer\_adequacy` |
| Logical relation and semantic typing (Fig 8 and 9 and 10) | theories/iris/logrel/iris\_logrel.v | e.g. `interp\_value\_handle` or `semantic\_typing` |
| Fundamental theorem (Theorem 4.1) | theories/iris/logrel/iris\_fundamental.v | `be_fundamental` |
