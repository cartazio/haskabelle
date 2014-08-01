theory Haskabelle
imports Main Setup
begin

chapter {* Haskabelle *}

section {* Introduction *}

subsection {* What is Haskabelle? *}

text {*
  @{text Haskabelle} is a converter from @{text Haskell} source
  files to @{text "Isabelle/HOL"} \cite{isa-tutorial} theories
  implemented in @{text Haskell} itself.
*}

subsection {* Motivation *}

text {* 

  @{text "Isabelle/HOL"} can be regarded as a combination of a
  functional programming language and logic. Just like functional
  programming languages, it has its foundation in the typed lambda
  calculus, but is additionally crafted to allow the user to write
  arbitrary mathematical theorems in a structured and convenient way.

  @{text Haskell} is a functional programming language that has
  succeeded in getting more and more momentum, not only in academia
  but increasingly also in industry. It is used for all kinds of
  programming tasks despite (or, perhaps, rather because) of its
  pureness, that is its complete lack of side-effects.

  This pureness makes @{text Haskell} relate to @{text "Isabelle/HOL"}
  more closely than other functional languages. In fact, @{text
  "Isabelle/HOL"} can be considered a subset of @{text Haskell}.

  Writing a converter from the convertible subset of @{text Haskell}
  to @{text "Isabelle/HOL"} seems thus like the obvious next step to
  facilitate machine-aided verification of @{text Haskell}
  programs.  @{text Haskabelle} is exactly such a converter.

*}

subsection {* Implementation *}

text {*

  There is one major design decision which users have to keep in
  mind. @{text Haskabelle} works on the Abstract Syntax Tree (AST)
  representation of @{text Haskell} programs exclusively. As a result,
  it is very restricted on what it knows about the validity of the
  program; for example, it does not perform type inference.

  In fact, input source files are not checked at all beyond syntactic
  validity that is performed by the parser. Users are supposed to
  first run their @{text Haskell} implementation of choice on the
  files to catch programming mistakes.  In practice, this is not an
  impediment as it matches the putative workflow: @{text Haskabelle}
  is supposed to help the verification of already-written, or
  just-written programs.

  Also, no proof checking is involved; that work is delegated to
  @{text Isabelle}.  This means that only because the conversion
  seemingly succeeded, does not necessarily mean that @{text Isabelle}
  won't complain. A common example is that a @{text Haskell} function
  could be syntactically transformed to a corresponding @{text
  "Isabelle/HOL"} function, but @{text Isabelle} will refuse to accept
  it as it's not able to determine termination by itself.
  
*}

text {*

  @{text Haskabelle} performs its work in the following 5 phases.

*}


subsubsection {* Parsing *}

text {* 

  Each @{text Haskell} input file is parsed into an @{text Haskell}
  Abstract Syntax Tree representation. Additionally, module resolution
  is performed, i.e. the source files of the modules that the input
  files depend on are also read and parsed. So the actual output of
  this phase is a forest of @{text Haskell} ASTs.

*}


subsubsection {* Preprocessing *}

text {* 

  Each @{text Haskell} AST is normalised to a semantically equivalent
  but canonicalised form to simplify the subsequent converting
  phase. At the moment, the following transformations are performed:

  \begin{itemize}

  \item{ identifiers that would clash with reserved keywords or
    constants in @{text "Isabelle/HOL"} are renamed.  }

  \item{ pattern guards are transformed into nested \code{if}
    expressions.  }

  \item{ \code{where} clauses are transformed into \code{let}
    expressions.  }

  \item{ local function definitions are made global by renaming then
    uniquely.  }

  \end{itemize}

*}


subsubsection {* Converting *}

text {* 

  After preprocessing, each @{text Haskell} AST consists entirely of
  toplevel definitions. Before the actual conversion, a dependency
  graph is generated for these toplevel definitions for two purposes:
  first to ensure that definitions appear textually before their uses;
  second to group mutually-recursive function together. Both points
  are necessary to comply with requirements imposed by @{text
  "Isabelle/HOL"}.

*}

text {* 

  Furthermore, a global environment is built in this phase that
  contains information about all identifiers, e.g. what they
  represent, in which module they belong to, whether they're exported,
  etc.

*}


text {* 

  What @{text Haskell} language features are translated to which
  @{text "Isabelle/HOL"} constructs, is explained in section
  \ref{sec:Haskabelle-what-is-supported}.
 
*}

text {*

  The output of this phase is a forest of @{text "Isabelle/HOL"} ASTs.

*}


subsubsection {* Adapting *}

text {* 

  While the previous phase converted the @{text Haskell} ASTs into
  their syntactically equivalent @{text "Isabelle/HOL"} ASTs, it has
  not attempted to map functions, operators, or algebraic data types,
  that preexist in Haskell, to their pedants in @{text
  "Isabelle/HOL"}. Such a mapping (or adaption) is performed in this
  phase.

*}


subsubsection {* Printing *}

text {*

  The @{text "Isabelle/HOL"} ASTs are pretty-printed into an human-readable format so
  users can subsequently work with the resulting definitions, supply additional
  theorems, and verify their work.

*}

section {* Setup and usage *}

subsection {* Prerequisites *}

text {*

  We assume that the reader of this tutorial has some basic experience
  with @{text UNIX}, @{text Haskell}, and @{text "Isabelle/HOL"}.

  @{text Haskabelle} is shipped in source code; this means you have to
  provide a working @{text Haskell} environment yourself, including
  some libraries.  In order to make use of the theories generated by
  @{text Haskabelle}, you will also need an @{text Isabelle} release.

*}

subsubsection {* @{text Haskell} environment *}

text {*

  The given version numbers just indicate which constellation has been
  tested -- others might work, too.

  \noindent First, the @{text Haskell} suite itself:

  \begin{description}

    \item[GHC] Glasgow Haskell Compiler \url{http://www.haskell.org/ghc/}
       (version 7.6.3)

  \end{description}
  
  \noindent The following libraries are required:

  \begin{description}

    \item[mtl] Monad transformer library. \\
       \url{http://hackage.haskell.org/cgi-bin/hackage-scripts/package/mtl-2.1.1}

    \item[xml] A simple XML library. \\
       \url{http://hackage.haskell.org/cgi-bin/hackage-scripts/package/xml-1.3.12}

    \item[uniplate] Uniform type generic traversals. \\
       \url{http://hackage.haskell.org/cgi-bin/hackage-scripts/package/uniplate-1.6.7}

    \item[cpphs] A liberalised re-implementation of cpp, the C pre-processor. \\
       \url{http://hackage.haskell.org/cgi-bin/hackage-scripts/package/cpphs-1.13.3}

    \item[Happy] Happy is a parser generator for Haskell. \\
       \url{http://hackage.haskell.org/cgi-bin/hackage-scripts/package/happy-1.18.9}

       The installation process provides a binary \shell{happy}
       which must be accessible on your \shell{PATH} to
       proceed!

    \item[haskell-src-exts] Manipulating Haskell source: abstract syntax, lexer, parser, and pretty-printer. \\
       \url{http://hackage.haskell.org/cgi-bin/hackage-scripts/package/haskell-src-exts-0.4.8}
       (newer versions won't work)

  \end{description}
*}

subsubsection {* @{text Isabelle} release *}

text {*

  The latest @{text Isabelle} release is available from
  \url{http://isabelle.in.tum.de/download.html}.

*}

subsubsection {* @{text Haskabelle} distribution *}

text {*

  The current @{text Haskabelle} release as available from
  \url{http://isabelle.in.tum.de/haskabelle.html} is tailored to the
  latest @{text Isabelle} release.

*}


subsection {* Basic usage *}

subsubsection {* Understanding the distribution structure *}

text {*

  Throughout this manual, qualified paths of executables on the shell
  prompt are relative to the root directory of the @{text Haskabelle}
  distribution.

  Therein, among others, the following directories can be found:

*}

text %quote {*
  \begin{description}

    \item [\shell{doc/}]  Documentation

    \item [\shell{default/}]  Default adaption files (see
      \secref{sec:adaption})

    \item [\shell{ex/}]  Examples (see \secref{sec:examples})

  \end{description}
*}

subsubsection {* Installing and configuring Haskabelle *}

text {*
  If you are using the Haskabelle component shipping with Isabelle,
  you only need to make sure that \shell{ISABELLE_GHC} is set in
  your Isabelle settings file and points to your GHC binary. Also
  the right GHC libraries must be installed.
*}

subsubsection {* Converting theories *}

text {*
  @{text Haskabelle} is invoked using the following command line
  (\shell{isabelle} is the binary of your isabelle distribution):
*}

text %quote {*
  \shell{isabelle haskabelle <SRC1> .. <SRCn> <DST>}
*}

text {*

  \noindent where \shell{<SRC1>} \ldots \shell{<SRCn>} is a list of
  @{text Haskell} source files to convert and \shell{<DST>} is a
  directory to put the generated @{text "Isabelle/HOL"} theory files
  inside.

  The @{text Prelude} theory the generated theory files depend on can
  be found in \shell{default/Prelude.thy}.

*}



section {* A bluffer's glance at Haskabelle \label{sec:Haskabelle-what-is-supported}*}

text {*
  
  In this section we want to provide a few examples to give the reader
  an impression of @{text Haskabelle}'s capabilities.

*}

text {*

  The following @{text Haskell} code represents a very simple
  interpreter:

*}

text %quotetypewriter {* 
module Example where
\\
\\
evalExp :: Exp -> Int

evalExp (Plus e1 e2) ~= evalExp e1 + evalExp e2 \\
evalExp (Times e1 e2) = evalExp e1 * evalExp e2 \\
evalExp (Cond b e1 e2) \\
\hspace*{0pt}  ~~| evalBexp b = evalExp e1 \\ 
\hspace*{0pt}  ~~| otherwise ~= evalExp e2 \\
evalExp (Val i) = i
\\
\\
evalBexp :: Bexp -> Bool

evalBexp (Equal e1 e2) ~~= evalExp e1 == evalExp e2\\
evalBexp (Greater e1 e2) = evalExp e1 > evalExp e2
\\
\\
data Exp ~= Plus Exp Exp\\
\hspace*{0pt}  ~~~~~~~~~| Times Exp Exp\\
\hspace*{0pt}  ~~~~~~~~~| Cond Bexp Exp Exp\\
\hspace*{0pt}  ~~~~~~~~~| Val Int\\

data Bexp = Equal Exp Exp\\
\hspace*{0pt}  ~~~~~~~~~| Greater Exp Exp
 
*}

text {*

  \noindent @{text Haskabelle} will transform the above into the following:

*}

text %quotetypewriter {*
theory Example\\
imports Prelude\\
begin\\
\\
datatype Exp = Plus Exp Exp\\
\hspace*{0pt}  ~~~~~~~~~| Times Exp Exp\\
\hspace*{0pt}  ~~~~~~~~~| Cond Bexp Exp Exp\\
\hspace*{0pt}  ~~~~~~~~~| Val int\\
and      Bexp = Equal Exp Exp\\
\hspace*{0pt}  ~~~~~~~~~| Greater Exp Exp\\
\\
\\
\\
\\
\\
fun evalExp ~:: "Exp => int" and\\
\hspace*{0pt}  ~~~evalBexp :: "Bexp => bool"\\
where\\
\hspace*{0pt}  ~"evalExp (Plus e1 e2) = (evalExp e1 + evalExp e2)"\\
| "evalExp (Times e1 e2) = (evalExp e1 * evalExp e2)"\\
| "evalExp (Cond b e1 e2) = (if evalBexp b then evalExp e1\\
\hspace*{0pt}  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~else evalExp e2)"\\
| "evalExp (Val i) = i"\\
| "evalBexp (Equal e1 e2) = heq (evalExp e1) (evalExp e2)"\\
| "evalBexp (Greater e1 e2) = (evalExp e1 > evalExp e2)"\\
\\
end
*}

text {*

  \noindent We can note a couple of things at this point:

  \begin{itemize}

  \item{ The data type definitions have been moved before their uses.
    }

  \item{ The two data type definitions have been chained together by
    an explicit {\tt and} keyword. Likewise the function
    definitions have been grouped together. This stems from the mutual
    recursion inherent in the definitions.  }

  \item We use @{text Isabelle}'s function package.
    % (FIXME: Add reference.)

  \item{ The pattern guards in {\tt evalExp} have been
    transformed to an {\tt if} expression.  }

  \item{ Preexisting @{text Haskell} functions and operators have been mapped
    to @{text "Isabelle/HOL"} counterparts.  }

  \item{ @{text Haskell} modules inherit from an implicit module
    {\tt Prelude}; @{text Haskabelle} comes with a
    {\tt Prelude.thy} which provides necessary context to
    cope with some @{text Haskell} features. We can see that an import of
    this the {\tt Prelude} module is explicitly added by
    @{text Haskabelle}.  }

  \item{ The @{text Haskell} comparison operator {\tt ==} has been
    transformed to {isatypewriter heq} which is not defined by with
    @{text "Isabelle/HOL"} itself but within the {\tt
    Prelude.thy} file. It names both an operator and a type class
    which has been constructed to match {\tt ==}, and
    @{text Haskell}'s type class {\tt Eq}.  }

  \end{itemize}

*}

text {*

  \noindent The next example illustrates a simple use of type classes.
 
*}

text %quotetypewriter {*
module Classes where

class Monoid a where\\
\hspace*{0pt}  ~~nothing :: a\\
\hspace*{0pt}  ~~plus :: a -> a -> a
\\
\\  
instance Monoid Integer where\\
\hspace*{0pt}  ~~nothing = 0\\
\hspace*{0pt}  ~~plus    = (+)
\\
\\
-- prevent name clash with Prelude.sum\\
summ :: (Monoid a) => [a] -> a\\
summ [] = nothing\\
summ (x:xs) = plus x (summ xs)
\\
\\
class (Monoid a) => Group a where\\
\hspace*{0pt}  ~~inverse :: a -> a
\\
\\
instance Group Integer where\\
\hspace*{0pt}  ~~inverse = negate
\\
\\
sub :: (Group a) => a -> a -> a\\
sub a b = plus a (inverse b)  

*}

text {*

  @{text Haskabelle} will transform this into the following:

*}

text %quotetypewriter {*
theory Classes\\
imports Nats Prelude\\
begin
\\ 
class Monoid = type +\\
\hspace*{0pt}  ~~fixes nothing :: 'a\\
\hspace*{0pt}  ~~fixes plus :: "'a => 'a => 'a"
\\
\\
instantiation int :: Monoid\\
begin\\
\hspace*{0pt}  ~~definition nothing\_int :: "int"\\
\hspace*{0pt}  ~~where\\
\hspace*{0pt}  ~~~~"nothing\_int = 0"     \\
\hspace*{0pt}  ~~definition plus\_int :: "int => int => int"\\
\hspace*{0pt}  ~~where\\
\hspace*{0pt}  ~~~~"plus\_int = (op +)"   \\
instance ..\\
end
\\
\\
fun summ :: "('a :: Monoid) list => ('a :: Monoid)"\\
where\\
\hspace*{0pt}  ~~"summ Nil = nothing"\\
|~~"summ (x \# xs) = plus x (summ xs)"
\\
\\
class Group = Monoid +\\
\hspace*{0pt}  ~~fixes inverse :: "'a => 'a"
\\
\\
instantiation int :: Group\\
begin     \\
\hspace*{0pt}  ~~definition inverse\_int :: "int => int"\\
\hspace*{0pt}  ~~where\\
\hspace*{0pt}  ~~~~"inverse\_int = uminus"   \\
instance ..\\
end
\\
\\
fun sub :: "('a :: Group) => ('a :: Group) => ('a :: Group)"\\
where\\
\hspace*{0pt}  ~~"sub a b = plus a (inverse b)"\\
\\
end
*}

text {*
*}

(*  FIXME: Add reference to class paper

  FIXME: Describe insertion of class annotations.

  FIXME: Explain constraints. *)


section {* Adaption \label{sec:adaption} *}

subsection {* The concept *}

text {*
      
  Adaption allows to identify functions, types etc. from the @{text Haskell}
  source files with pre-existing counterparts in @{text
  "Isabelle/HOL"} by means of two mechanisms:

  \begin{itemize}

    \item An \emph{adaption table} in a simple domain-specific
      language which specifies a table between identifiers of classes,
      types and functions in @{text Haskell} to their corresponding
      identifiers in @{text "Isabelle/HOL"}.

    \item A prelude theory containing a @{text "Isabelle/HOL"} base
      environment where @{text Haskabelle}'s output is supposed to be
      run implicitly within.  By extending this, it is possible to
      adapt even more complex features of the @{text Haskell}
      programming language.

  \end{itemize}

*}


subsection {* Setting up your own adaption *}

text {*

  @{text Haskabelle} provides some default adaptions already in
  directory \shell{default}.  You can setup your own adaption
  according to the following steps:

*}

subsubsection {* Copy \shell{default} *}

text {*

  Typically you will want to use the default adaption as a starting
  point, so copy the \shell{default} directory to a directory of
  your choice (which we will refer to as \shell{<ADAPT>}).

*}

subsubsection {* Adapt the prelude theory *}

text {*

  If desired, adapt the prelude theory \shell{<ADAPT>/Prelude.thy}.

*}

subsubsection {* Edit adaption table *}

text {*

  The adaptions themselves reside in \shell{<ADAPT>/adapt.txt} and can
  be edited there.

*}

subsubsection {* Process adaptions *}

text {*

  To make the adaptions accessible to @{text Haskabelle}, execute the
  following:

*}

text %quote {*
  \shell{isabelle haskabelle -r  -a <ADAPT>}
*}

text {*

  \noindent This also includes some basic consistency checking.
*}

subsubsection {* Use this adaption during conversion *}

text {*

  A particular adaption other than default is selected using the
  \shell{-a} command line switch:

*}

text %quote {*
  \shell{isabelle haskabelle -a <ADAPT> <SRC1> .. <SRCn> <DST>}
*}


section {* Examples \label{sec:examples} *}

text {*

  Examples for @{text Haskabelle} can be found in the
  \shell{ex/src\_hs} directory in the distribution.  They can be
  converted at a glance using the following command:

*}

text %quote {*
  \shell{isabelle haskabelle -e}
*}

text {*

  \noindent Each generated theory then is re-imported into @{text
  Isabelle}.

*}

end

