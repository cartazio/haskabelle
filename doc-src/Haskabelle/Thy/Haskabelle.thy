theory Haskabelle
imports Main Setup
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

    \item[xml]
        \url{http://hackage.haskell.org/cgi-bin/hackage-scripts/package/xml}

    \item[QuickCheck]
        \url{http://hackage.haskell.org/packages/archive/QuickCheck/2.1.0.1/QuickCheck-2.1.0.1.tar.gz}

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

section {* Haskabelle *}

subsection {* The concept behind *}

text {*
  \begin{itemize}

    \item ``dumb tool'', works on Abstract Syntax Trees only.

    \item e.g.~no type inference

    \item we delegate the hard work to Isabelle

    \item Conclusion: Only because the conversion succeeded, does not
      mean that Isabelle won't choke\ldots

  \end{itemize}
*}

subsection {* Facilities and limits *}

text {*

  What we can:

  \begin{itemize}
\item Module Resolution
\end{itemize}
~

\begin{itemize}
\item Declarations: %
\begin{itemize}
\item functions (\texttt{\small fun})
\item constants (\texttt{\small definition})
\item algebraic data types (\texttt{\small datatype})
\item classes \& instances (\texttt{\small class}, \texttt{\small instantiation})
\end{itemize}
\end{itemize}
~

\begin{itemize}
\item Linearization of declarations
\end{itemize}

\begin{itemize}
\item Expressions: %
\begin{itemize}
\item literals (integers, strings, characters)
\item applications, incl. infix applications and sections
\item lambda abstractions
\item if, let, case
\item pattern guards
\item list comprehensions
\end{itemize}
\end{itemize}

  What we can't:

  \ldots

5 Phases:

\begin{itemize}
\item Parsing
\item Preprocessing
\item Converting
\item Adapting
\item Printing
\end{itemize}

*}

section {* Configuring and adapting *}

section {* Examples *}

text {*
  Examples for Haskabelle can be found in the
  \shell{ex/src\_hs} directory in the distribution.
  They can be imported at a glance using the following command:
*}

text %quote {*
  \shell{bin/regression}
*}

end