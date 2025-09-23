section \<open>Definition of (Voting Power) Extensions\<close>

theory Extension
  imports Voting_Power
          "Games/Simple_Voting_Game"

begin

locale model_isomorphism =
  fixes
    iso_models :: "'s \<Rightarrow> 't \<Rightarrow> bool" 
    (* embodies the definition of "m1 ~ m2 iff they can be interpreted as the same voting system *)

begin

subsection \<open>"Isomorphism" Definitions\<close>
text \<open>Comparable sets (of models) and isomorphic functions and predicates on them.\<close>

text \<open>if two models are isomorphic, they are either contained in both sets or in none\<close>
definition only_iso_elts :: "'s set \<Rightarrow> 't set \<Rightarrow> bool" where
  "only_iso_elts S T = (\<forall> s :: 's. \<forall> t :: 't. iso_models s t \<longrightarrow> (s \<in> S \<longleftrightarrow> t \<in> T))"

text \<open>any model from the first set has a corresponding (isomorphic) model in the second set\<close>
definition ex_iso_elts_S :: "'s set \<Rightarrow> 't set \<Rightarrow> bool" where
  "ex_iso_elts_S S T = (\<forall> s \<in> S. \<exists> t \<in> T. iso_models s t)"

definition ex_iso_elts_T :: "'t set \<Rightarrow> 's set \<Rightarrow> bool" where
  "ex_iso_elts_T T S = (\<forall> t \<in> T. \<exists> s \<in> S. iso_models s t)"

text 
\<open>
two sets (or function domains) are isomorphic if:
  - isomorphic models can be found either in both or none of the sets
  - for every element of the first set, there is an iso. element of the second set and vice versa  
\<close>
definition iso_sets :: "'s set \<Rightarrow> 't set \<Rightarrow> bool" where
  "iso_sets S T = (only_iso_elts S T \<and> ex_iso_elts_S S T \<and> ex_iso_elts_T T S)"

text 
\<open>
two functions with the same codomain coincide on isomorphic input if, 
for every pair of isomorphic inputs, their values are identical 
\<close>
definition coincide_on_iso_input :: 
  "('s \<Rightarrow> 'r) \<Rightarrow> ('s set) \<Rightarrow> ('t \<Rightarrow> 'r) \<Rightarrow> ('t set) \<Rightarrow> bool" where
  "coincide_on_iso_input f S g T = (\<forall> s \<in> S. \<forall> t \<in> T. iso_models s t \<longrightarrow> f s = g t)"

text 
\<open>
two functions with the same codomain are isomorphic if 
their domains are isomorphic and they coincide on isomorphic inputs

one function extends another if its restriction to a subdomain is isomorphic to the other
\<close>
definition iso_functions :: 
  "('s \<Rightarrow> 'r) \<Rightarrow> ('s set) \<Rightarrow> ('t \<Rightarrow> 'r) \<Rightarrow> ('t set) \<Rightarrow> bool" where
  "iso_functions f S g T = (iso_sets S T \<and> coincide_on_iso_input f S g T)"

definition ext_function ::
  "('s \<Rightarrow> 'r) \<Rightarrow> ('s set) \<Rightarrow> ('t \<Rightarrow> 'r) \<Rightarrow> ('t set) \<Rightarrow> bool" where
  "ext_function f S g T = (\<exists> S' \<subseteq> S. iso_functions f S' g T)"

text 
\<open>
predicates on functions with the same codomain are isomorphic if
they are equivalent for isomorphic functions
\<close>
definition iso_predicates ::
  "(('s \<Rightarrow> ereal) \<Rightarrow> ('s set) \<Rightarrow> bool) \<Rightarrow> (('t \<Rightarrow> ereal) \<Rightarrow> ('t set) \<Rightarrow> bool) \<Rightarrow> bool" where
  "iso_predicates \<phi> \<psi> = (\<forall> f S g T. iso_functions f S g T \<longrightarrow> (\<phi> f S \<longleftrightarrow> \<psi> g T))"

(* TODO add domains for predicates or keep assuming they are defined on the whole type universe? *)

subsection \<open>"Intuitive Extension"\<close>

(* TODO (but how to?) *)

end

subsection \<open>Isomorphism Proofs\<close>

locale voting_model_isomorphism = model_isomorphism iso_models
  for iso_models :: "('a, 'v, 'r) Voting_Power_Domain \<Rightarrow> 'v SVG_Voting_Power_Domain \<Rightarrow> bool" +
  assumes
    eq_voters: "\<forall> F G. iso_models F G \<longrightarrow> voter F = snd G" and
    two_alts: 
      "\<forall> F G. iso_models F G \<longrightarrow> (\<forall> e \<in> counting_domain F. card (alternatives_\<E> e) = 2)" and
    todo: "True" (* add more sensible assumptions about isomorphic voting rules and SVGs *)

begin

lemma iso_null_player:
  "iso_predicates Voting_Power.null_player Simple_Voting_Game.null_player"
  sorry (* TODO needs more assumptions about iso. models *)

end


end