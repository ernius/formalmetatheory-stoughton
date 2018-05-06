# Formal Meta Theory of Lambda Calculus based on Stoughton's multiple substitutions operation.

We develop metatheory of the Lambda calculus in Constructive Type Theory, using the presentation of the former with one sort of names for both free and bound variables and without identifying terms up to &#945;-conversion. We prove three substitution lemmas: for &#945;-conversion, parallel &#946;-reduction, and for the system of simple type assignment. This work prove  the main results of the metatheory; subject reduction of the Type System, and Church-Rosser confluence theorem. This results are possible by the use of an appropriate notion of substitution, due to A. Stoughton. The whole development has been machine-checked using the system Agda. The whole source code is web browsable [here](http://ernius.github.io/formalmetatheory-stoughton/html/index.html).

# Documented in the following papers:
* [Formal metatheory of the Lambda calculus using Stoughton's substitution.](https://www.sciencedirect.com/science/article/pii/S0304397516304820?via%3Dihub) Theor. Comput. Sci. 685: 65-82 (2017)
* [Formalisation in Constructive Type Theory of Stoughton's Substitution for the Lambda Calculus.](https://www.sciencedirect.com/science/article/pii/S1571066115000171?via%3Dihub). Electr. Notes Theor. Comput. Sci. 312: 215-230 (2015)

# Authors

* Álvaro Tasistro (Universidad ORT Uruguay)
* Nora Szasz (Universidad ORT Uruguay)
* Ernesto Copello (Universidad ORT Uruguay)

# Build Status in Travis CI : [![Build Status](https://travis-ci.org/ernius/formalmetatheory-stoughton.svg?branch=master)](https://travis-ci.org/ernius/formalmetatheory-stoughton)

Agda compiler version 2.4.2.5 and standard library version 0.11.

