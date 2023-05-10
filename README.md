# NormRelations

A Julia package for working with norm relations in abelian fields. This package contains the tools to reproduce many of the computations from [[1]](#1) and [[3]](#3).

Special thanks to Aurel Page for providing *abelianbnf* [[4]](#4), a [GP](https://pari.math.u-bordeaux.fr/) script licensed under [GPL V3+](https://www.gnu.org/licenses/gpl-3.0.html) 
that computes the class group of certain Galois number fields by exploiting the existence of norm relations, using the algorithm described in [[2]](#2). 
This is also being used to produce a database of invariants of cyclotomic fields, [CycloDB](https://www.cyclodb.org/).

## Usage

1. Install [Julia](https://julialang.org/) if it is not already installed. 
2. Download/clone this repository and navigate to the top-level directory.
3. Run `julia --project=.`
4. Inside the Julia REPL, run `import Pkg; Pkg.instantiate()`. This configures dependencies and is only needed on the first run.
5. Inside the REPL, run `using NormRelations` to load the package.

Now the NormRelations package is available. [Hecke](https://github.com/thofma/Hecke.jl) is also reexported by NormRelations so all Hecke functions will be available as well.
Instructions on running specific examples soon to come.

## Tests

Repeat steps 1-3 above then do `import Pkg; Pkg.test()`. This doesn't test much at the moment but should be a decent indicator that things are configured properly.

## References

<a id="1">[1]</a>
Biasse, J.-F., Erukulangara, M. R., Fieker, C., Hofmann, T., and Youmans, W. (2022),
Mildly Short Vectors in Ideals of Cyclotomic Fields Without Quantum Computers.
In: Mathematical Cryptology, 2(1), 84–107. 
URL: [https://journals.flvc.org/mathcryptology/article/view/132573](https://journals.flvc.org/mathcryptology/article/view/132573)

<a id="2">[2]</a>
Biasse, J.-F., Fieker, C., Hofmann, T. and Page, A. (2022), 
Norm relations and computational problems in number fields. 
In: J. London Math. Soc., 105: 2373-2414. 
URL: [https://doi.org/10.1112/jlms.12563](https://doi.org/10.1112/jlms.12563)

<a id="3">[3]</a>
Biasse, J.-F., Fieker, C., Hofmann, T., and Youmans, W. (2023), 
An algorithm for solving the principal ideal problem with subfields. 
In: Advances in Mathematics of Communications (to appear).

<a id="4">[4]</a>
Page, A. (2021), abelianbnf. [http://www.normalesup.org/~page/Recherche/Logiciels/logiciels-en.html](http://www.normalesup.org/~page/Recherche/Logiciels/logiciels-en.html)
