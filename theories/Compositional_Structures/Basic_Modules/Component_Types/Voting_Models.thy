section \<open>Definition and Comparison of Voting Models\<close>

theory Voting_Models
  imports Electoral_Module
          "Games/Simple_Voting_Game"

begin

subsection \<open>Voting Models\<close>

locale voting_model = 
  fixes 
    voters :: "'v set" and
    instances :: "'x set"
  (* No assumptions on this abstraction level? *)
  (* TODO using the term voting model both for single instances and sets thereof... *)

locale voting_rule = voting_model voters rules
  for voters :: "'v set" and rules :: "('a, 'v, 'r) Electoral_Module set" +
  fixes 
    domain :: "('a, 'v) Election set"
  (* TODO like this, all voting rules in the voting rule model have the same domain
          \<rightarrow> build the domain into the Electoral_Module type instead? *)

sublocale voting_rule \<subseteq> voting_model 
proof - qed

locale svg = voting_model voters svgs 
  for voters :: "'v set" and svgs :: "'v Simple_Voting_Game set"
  (* TODO add assumptions or definitions? *)

sublocale svg \<subseteq> voting_model 
proof - qed

subsection \<open>Voting Model "Isomorphism" Definitions\<close>
text \<open>Comparable sets (of models) and isomorphic functions and predicates on them.\<close>

text \<open>if two models are isomorphic, they are either contained in both sets or in none\<close>
fun only_iso_elts :: "('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> 's set \<Rightarrow> 't set \<Rightarrow> bool" where
  "only_iso_elts iso_models S T = (\<forall> s :: 's. \<forall> t :: 't. iso_models s t \<longrightarrow> (s \<in> S \<longleftrightarrow> t \<in> T))"

text \<open>any model from the first set has a corresponding (isomorphic) model in the second set\<close>
fun ex_iso_elts :: "('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> 's set \<Rightarrow> 't set \<Rightarrow> bool" where
  "ex_iso_elts iso_models S T = (\<forall> s \<in> S. \<exists> t \<in> T. iso_models s t)"

fun swap_args :: "('s \<Rightarrow> 't \<Rightarrow> 'r) \<Rightarrow> ('t \<Rightarrow> 's \<Rightarrow> 'r)" where
  "swap_args f = (\<lambda>t s. f s t)"

text 
\<open>
two models are isomorphic if:
  - isomorphic models can be found either in both or none of the sets
  - for every element of the first set, there is an iso. element of the second set and vice versa  
\<close>  
locale model_isomorphism = m1: voting_model \<V> \<M> + m2: voting_model \<V> \<M>'
  for \<V> :: "'v set" and \<M> :: "'x set" and \<M>' :: "'y set" +
  fixes
    isomorphic :: "'x \<Rightarrow> 'y \<Rightarrow> bool"
  assumes
    iso_occurrence: "only_iso_elts isomorphic \<M> \<M>'" and
    correspondence: "ex_iso_elts isomorphic \<M> \<M>' \<and> ex_iso_elts (swap_args isomorphic) \<M>' \<M>"

begin

text 
\<open>
two functions with the same codomain coincide if, 
for every pair of isomorphic inputs, their values are identical 
\<close>
fun equiv_funs :: "('x \<Rightarrow> 'z) \<Rightarrow> ('y \<Rightarrow> 'z) \<Rightarrow> bool" where
  "equiv_funs f g = (\<forall> x \<in> \<M>. \<forall> y \<in> \<M>'. isomorphic x y \<longrightarrow> f x = g y)"

end

locale identical_isomorphism = model_isomorphism \<V> \<M> \<M> isomorphic
  for \<V> :: "'v set" and \<M> :: "'x set" and isomorphic :: "'x \<Rightarrow> 'x \<Rightarrow> bool" +
  assumes
    "\<forall>x \<in> \<M>. isomorphic x x"

sublocale identical_isomorphism \<subseteq> model_isomorphism \<V> \<M> \<M> isomorphic
  by (simp add: model_isomorphism_axioms)

locale rule_svg_isomorphism = 
  model_isomorphism \<V> \<F> \<G> isomorphic + rules: voting_rule \<V> \<F> domain + games: svg \<V> \<G>
  (* TODO can I avoid the latter two requirements by merging them into 
          the instantiation of model_isomorphism, i.e. sth. like
          "model_isomorphism (voting_rule ...) (svg ...)"? *)
  for  \<V> :: "'v set" 
    and \<F> :: "('a,'v,'r) Electoral_Module set" 
    and \<G> :: "'v Simple_Voting_Game set"
    and isomorphic :: "('a,'v,'r) Electoral_Module \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> bool"
    and domain :: "('a, 'v) Election set" +
  assumes
    (* Sensibly specify "isomorphic" without completely defining it *)
    two_alts: 
      "\<forall> f g. isomorphic f g \<longrightarrow> (\<forall> e \<in> domain. card (alternatives_\<E> e) = 2)" and
    todo: "True" (* add more sensible assumptions about isomorphic voting rules and SVGs *)

sublocale rule_svg_isomorphism \<subseteq> model_isomorphism \<V> \<F> \<G> isomorphic
  by (simp add: model_isomorphism_axioms)

sublocale rule_svg_isomorphism \<subseteq> voting_rule
proof - qed

sublocale rule_svg_isomorphism \<subseteq> svg
proof - qed

end