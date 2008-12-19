theory Haskabelle
imports Main Setup
begin

chapter {* Haskabelle *}

section {* Introduction *}

subsection {* What is Haskabelle? *}

text {* @{text Haskabelle} is an importer from @{text Haskell} source
  files to @{text "Isabelle/HOL"} \cite{isa-tutorial} theories
  implemented in @{text Haskell} itself.
*}

subsection {* Installation hints *}

text {*
  We give here some hints which software you have to install
  to get @{text Haskabelle} run.  Some familiarity with
  the usual @{text Haskell} deployment facilities is assumed.
  For @{text UNIX} users with some experience the
  @{text README} files shipped with the tarballs should provide
  all necessary clues to succeed.  The given version just
  indicate which constellation has been tested -- others may
  work, too.

  \begin{description}

    \item[GHC] Glasgow Haskell Compiler \url{http://www.haskell.org/ghc/}
       (version 6.10.1)

  \end{description}

  \begin{description}

    \item[mtl] Monad transformer library. \\
       \url{http://hackage.haskell.org/cgi-bin/hackage-scripts/package/mtl-1.1.0.1}

    \item[xml] A simple XML library. \\
       \url{http://hackage.haskell.org/cgi-bin/hackage-scripts/package/xml-1.3.3}

    \item[uniplate] Uniform type generic traversals. \\
       \url{http://hackage.haskell.org/cgi-bin/hackage-scripts/package/uniplate-1.2.0.3}

    \item[cpphs] A liberalised re-implementation of cpp, the C pre-processor. \\
       \url{http://hackage.haskell.org/cgi-bin/hackage-scripts/package/cpphs-1.6}

    \item[Happy] Happy is a parser generator for Haskell. \\
       \url{http://hackage.haskell.org/cgi-bin/hackage-scripts/package/happy-1.18.2}

       The installation process provides a binary \shell{happy}
       which must be accessible on your \shell{PATH} to
       proceed!

    \item[haskell-src-ext] Manipulating Haskell source: abstract syntax, lexer, parser, and pretty-printer. \\
       \url{http://hackage.haskell.org/cgi-bin/hackage-scripts/package/haskell-src-exts-0.4.6}

  \end{description}

  \noindent It is assumed that you have a suitable version of @{text Isabelle}
  running to really use the theories generated from @{text Haskabelle}.

  \noindent Throughout this tutorial, qualified paths
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
\item Hs.ModuleName Resolution
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
