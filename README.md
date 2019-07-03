# Virtualization of HOL4 in Isabelle

This is the implementation accompanying the ITP 2019 paper "Virtualization of HOL4 in Isabelle" by Fabian Immler, Jonas
Rädle, and Makarius Wenzel.

This file describes how to set up Poly/ML, HOL4, and Isabelle for hol4isabelle on Linux.
It shall set up a hierarchy of directories like this.
HOL must be a subdirectory of hol4isabelle, the location of isabelle and polyml is not too relevant.
```
hol4isabelle
|
|__ HOL
|
|__ isabelle
|
|__ polyml
```

## Installation (Linux)

### Poly/ML

In order to build HOL, download and install [Poly/ML (5.8)](https://polyml.org/download.html)


### HOL4
Clone HOL (the version below is tested to work) and build the kernel
(this generates a couple of SML files that are required to run hol4isabelle,
e.g., `src/postkernel/TheoryDatTokens.sml`)

```
git clone https://github.com/HOL-Theorem-Prover/HOL.git
cd HOL
git checkout 7e03303e51f

poly < tools/smart-configure.sml
bin/build --seq=tools/sequences/kernel
cd ..
```

### Isabelle

Download Isabelle2019 from ``https://isabelle.in.tum.de/website-Isabelle2019/``.
From here on we refer to the main Isabelle executable `Isabelle2019/bin/isabelle` as simply `isabelle`

Alternatively (in order to work with the repository):
```
hg clone http://isabelle.in.tum.de/repos/isabelle/rev/Isabelle2019
isabelle components -I
isabelle components -a
isabelle build -b HOL
```

## Run

### Explore transfer of theorems between HOL4 and Isabelle/HOL:
```
isabelle jedit -d . -l HOL4_Core_Isabelle Transfer_Example.thy
```

### Explore build of the Isabelle HOL4-Core (and all of its dependencies):
```
isabelle jedit -d . -l HOL HOL4_Core_Isabelle.thy
```

### Explore build of the Original HOL4-Core (and all of its dependencies):
```
isabelle jedit -d . -l Pure HOL4_Core_Original.thy
```

## OpenTheory import

* Theory ``OpenTheoryImport`` requires the Isabelle-OpenTheory importer as a subdirectory in
``hol4isabelle``:

```
git clone https://github.com/xrchz/isabelle-opentheory.git
cd isabelle-opentheory
git checkout f04496c
cd ..
```

* build OpenTheory .art files with HOL4's loggingKernel:

```
cd HOL
bin/build cleanAll
bin/build --otknl
```


## Notes for Installation on Windows

This requires
* The [Windows Subsystem for Linux](https://docs.microsoft.com/en-us/windows/wsl/install-win10), with Ubuntu 18.04
* An installation of the [Isabelle2019 application](http://isabelle.in.tum.de/dist/Isabelle2019.exe)

Most of the installation is just like under Linux, with the following exceptions:
* especially for polyml, make sure that everything is installed in a directory under the WSL home directory
* all commands involving that involve "./isabelle/bin/isabelle" must be executed in the Cygwin-Terminal (in the
  Isabelle2019) folder
* before building HOL, do
    ```
    echo 'val HOLDIR = "c:/path/to/hol4isabelle/HOL"' > tools-poly/poly-includes.sml
    ```
  because otherwise (due to WSL) `HOLDIR = "/mnt/c/path/to/hol4isabelle/HOL"` and this will confuse hol4isabelle.
