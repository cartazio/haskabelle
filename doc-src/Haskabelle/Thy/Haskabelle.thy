theory Haskabelle
imports Complex_Main Setup
begin

chapter {* Haskabelle *}

section {* Introduction *}

subsection {* What is Haskabelle? *}

text {* 
  Haskabelle is an importer from Haskell source files to
  Isabelle/HOL \cite{isa-tutorial} theories implemented
  in Haskell itself.
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

  \noindent Throughout this documentation, qualified paths
  of executables on the shell prompt are relative to the
  root directory of the Haskabelle distribution.
*}

subsection {* Basic usage *}

text {*
  Haskabelle is invoked using the following command line:
*}

text %quote {*
  \shell{bin/haskabelle <SRC1> .. <SRCn> <DST>}
*}

text {*
  \noindent where \shell{<SRC1>} \ldots \shell{<SRCn>} is
  a list of Haskell source files to imports and \shell{<DST>}
  is a directory to put the generated Isabelle/HOL theory
  files inside.
*}

subsection {* Examples *}

text {*
  Examples for Haskabelle can be found in the
  \shell{ex/src\_hs} directory in the distribution.
  They can be imported at a glance using the following command:
*}

text %quote {*
  \shell{bin/import\_all}
*}

end
