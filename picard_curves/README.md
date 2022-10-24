# picard\_curves: Picard curves and databases

Description
--

This repository gives a set of algorithms for calculating with Picard curves, as well as furnishing a small database of Picard curves having good reduction outside two primes in { 2, 3, 5, 7 }.

Prerequisites
--
An installation of both Magma and SageMath is required to run all of the code. You will also benefit from installing a recent version of [`MCLF/mclf`](https://github.com/MCLF/mclf), but this is not mandatory.

Magma installation 
--

The subdirectory `picard_curves/magma/` includes code that can be run purely within Magma. You can load all the Magma specific files by attaching the ``picard_curves/magma/spec`` file with ``AttachSpec``. For example, if you start your session of Magma inside the git directory, you can do this by typing
```
AttachSpec("picard_curves/magma/spec");
```

SageMath installation
--

To install the package in SageMath, first clone the repository via
```
git clone https://github.com/jrsijsling/picard_curves.git
```
then go to the newly created directory and type
```
sage -pip install --user --upgrade .
```
Once the package is updated on GitHub, pulling the new changes and running the same command will update your installation. After this, a new package called `picard_curves` will be available for import in SageMath, and the functions in the packages can be loaded with
```
sage: from picard_curves import *
```

Usage
--

Examples, both in Magma and in SageMath, are given in the directories starting with `examples`. We refer to the files in these directories for more details. In particular, try starting with `examples_magma/curves.m` and `examples_sage/curves.sage`.

The creation of database files in SageMath and the interaction with them is described in the directory `database/`. Reading and using these databases is described in the file `examples_sage/inspect_database.sage`.

Finally, some files confirming results in the database are given in the directory `paper/`.

Credits
--

This package uses code from the Magma package [`echidna`](http://iml.univ-mrs.fr/~kohel/alg/index.html) by David Kohel for an implementation of the Dixmier--Ohno invariants.

References
--

This implementation is based on the following work. When using this package, please be aware of the work that you are indirectly applying and please cite it.

* Irene Bouw, Angelos Koutsianas, Jeroen Sijsling, and Stefan Wewers, [Conductor and discriminant of Picard curves](https://arxiv.org/abs/1902.09624)
