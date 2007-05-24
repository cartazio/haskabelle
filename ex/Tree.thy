theory Tree
imports Main
begin

text {*
  A small theory of search trees:
*}

class ordered =
  fixes below :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<^loc>\<preceq>" 50)
  assumes refl [iff]: "x \<^loc>\<preceq> x"
  and antisym: "x \<^loc>\<preceq> y \<Longrightarrow> y \<^loc>\<preceq> x \<Longrightarrow> x = y"
  and trans: "x \<^loc>\<preceq> y \<Longrightarrow> y \<^loc>\<preceq> z \<Longrightarrow> x \<^loc>\<preceq> z"
  and linear: "x \<^loc>\<preceq> y \<or> y \<^loc>\<preceq> x"

instance nat :: ordered
  "op \<preceq> \<equiv> op \<le>" by default (auto simp add: below_nat_def)

datatype ('a, 'b) searchtree = Leaf "'a\<Colon>ordered" 'b
  | Branch "('a\<Colon>ordered, 'b) searchtree" "'a\<Colon>ordered" "('a\<Colon>ordered, 'b) searchtree"

fun
  find :: "('a\<Colon>ordered, 'b) searchtree \<Rightarrow> 'a\<Colon>ordered \<Rightarrow> 'b option" where
  "find (Leaf key val) it = (if it = key then Some val else None)"
  | "find (Branch t1 key t2) it = (if it \<preceq> key then find t1 it else find t2 it)"

fun
  update :: "'a\<Colon>ordered \<times> 'b \<Rightarrow> ('a\<Colon>ordered, 'b) searchtree \<Rightarrow> ('a\<Colon>ordered, 'b) searchtree" where
  "update (it, entry) (Leaf key val) = (
    if it = key then Leaf key entry
      else if it \<preceq> key
      then Branch (Leaf it entry) it (Leaf key val)
      else Branch (Leaf key val) it (Leaf it entry)
   )"
  | "update (it, entry) (Branch t1 key t2) = (
    if it \<preceq> key
      then (Branch (update (it, entry) t1) key t2)
      else (Branch t1 key (update (it, entry) t2))
   )"

fun
  example :: "nat \<Rightarrow> (nat, string) searchtree" where
  "example n = update (n, ''bar'') (Leaf 0 ''foo'')"

code_gen find update example (Haskell -)  -- {* replace "-" by directory name *}

end
