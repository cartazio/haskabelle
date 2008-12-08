theory Haskabelle
imports Complex_Main Setup
begin

chapter {* Haskabelle -- importing Haskell source files into
  Isabelle/HOL theories *}

section {* Introduction *}

subsection {* What is Haskabelle? *}

text {* 
  Haskabelle is an importer from Haskell source files to
  Isabelle/HOL \cite{isa-tutorial} theories
*}

subsection {* Installation hints *}

text {*
  To get Haskabelle run, install the following:

  \begin{description}

    \item[GHC] \url{http://www.haskell.org/ghc/}

    \item[mtl]
       \url{http://hackage.haskell.org/cgi-bin/hackage-scripts/package/mtl-1.1.0.1}

    \item[Happy] \url{http://www.haskell.org/happy/}

    \item[HSX]
       \url{http://www.cs.chalmers.se/~d00nibro/haskell-src-exts/} \\
       \shell{darcs get http://code.haskell.org/HSP/haskell-src-exts}

    \item[Uniplate]
       \shell{darcs get --partial http://www.cs.york.ac.uk/fp/darcs/uniplate}

  \end{description}

  \noindent It is assumed that you have a suitable version of Isabelle
  installed to really use the theories generated from Haskabelle.
*}

subsection {* Basic usage *}

text {*
  Haskabelle is invoked using the following command line:
*}

text {*
  \shell{bin/import\_file SRC.hs DST}
*}

subsection {* Examples *}

text {*

Examples:

    ex/src\_hs

Importing all examples (to ex/dst\_thy):

    bin/import\_all

*}

end
