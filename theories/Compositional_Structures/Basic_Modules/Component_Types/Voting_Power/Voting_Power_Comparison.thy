chapter \<open>Voting Power Comparison\<close>
theory Voting_Power_Comparison
  imports Voting_Power
          Voting_Model_Comparison

begin

section \<open>Voting Power Comparison Definition\<close>

locale voting_power_comparison = 
  pow1: voting_power domain1 semantics1 \<delta>1 +
  pow2: voting_power domain2 semantics2 \<delta>2 +
  comp: 
    voting_model_comparison domain1 domain2 semantics1 semantics2 model_equivalence
      for model_equivalence :: "'\<alpha> \<Rightarrow> '\<beta> \<Rightarrow> bool" and
          domain1 and semantics1 :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<delta>1 and
          domain2 and semantics2 :: "('\<beta>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<delta>2

section \<open>Voting Power Comparison Properties\<close>

text \<open>
The two power indices are equivalent w.r.t. their domains 
if they yield identical power values for equivalent inputs.

Note that model equivalence implies voters1 m1 = voters2 m2, 
so choosing a v from the first set should be sane.
\<close>
definition (in voting_power_comparison) power_equality :: bool where
  "power_equality = (\<forall>m1 \<in> domain1. \<forall>m2 \<in> domain2. model_equivalence m1 m2
    \<longrightarrow> (\<forall>v \<in> rule_voters (semantics1 m1). \<delta>1 m1 v = \<delta>2 m2 v))"

section \<open>Voting Power Axiom Comparison Second Try\<close>

(* 
Problem with defining this as on paper: 
- power comparison locale has fixed indices so we can also just put in booleans rather than 
    predicates but that feels weird to use...
- model comparison locale has no notion of voting power index so we would need to use the voting
    power locale as a predicate in the universal quantifier of the definition there...
*)
fun (in voting_power_comparison) axiom_equivalence :: 
  "(('\<alpha>, 'v) Voting_Power \<Rightarrow> bool) \<Rightarrow> (('\<beta>, 'v) Voting_Power \<Rightarrow> bool) \<Rightarrow> bool" where 
  "axiom_equivalence \<phi>1 \<phi>2 = ((comp.domain_equivalence \<and> power_equality) \<longrightarrow> \<phi>1 \<delta>1 = \<phi>2 \<delta>2)"


section \<open>Voting Power Axiom Comparison First Try\<close>

locale voting_power_axiom = voting_power domain semantics \<delta> 
  for domain :: "'\<alpha> set" and semantics :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<delta> +
  fixes
    axiom :: "('\<alpha>, 'v) Voting_Power_Axiom"

sublocale voting_power_axiom \<subseteq> voting_power by (rule local.voting_power_axioms)

locale voting_power_axiom_comparison = 
  axiom1: voting_power_axiom domain1 semantics1 \<delta>1 \<phi>1 +
  axiom2: voting_power_axiom domain2 semantics2 \<delta>2 \<phi>2 +
  comp: 
    voting_model_comparison domain1 domain2 semantics1 semantics2 model_equivalence
      for model_equivalence :: "'\<alpha> \<Rightarrow> '\<beta> \<Rightarrow> bool" and \<phi>1 and \<phi>2 and
          domain1 and semantics1 :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<delta>1 and
          domain2 and semantics2 :: "('\<beta>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<delta>2

sublocale voting_power_axiom_comparison \<subseteq> 
  voting_power_comparison model_equivalence domain1 semantics1 \<delta>1 domain2 semantics2 \<delta>2
  by (unfold_locales)

text \<open>
  Two voting power axioms are equivalent if they behave the same given equal voting power indices 
  on equivalent domains.
  Note that proving this inside the locale context without further assumptions gives a universally 
  quantified statement. 
\<close>
(* 
TODO:
  - Does the universal quantification really do what I want?
  - Technically, since the domains and power indices are fixed, 
      we do not need phi1 and phi2 to be functions...
      But making them bools is weird since we, conceptually, 
      want them to be functions that take power indices...
*)
definition (in voting_power_axiom_comparison) axiom_equivalence2 :: "bool" where 
  "axiom_equivalence2 \<equiv> 
    (power_equality \<longrightarrow> comp.domain_equivalence \<longrightarrow> (\<phi>1 domain1 \<delta>1 = \<phi>2 domain2 \<delta>2))"

section \<open>Concrete Voting Power Axioms\<close>

sublocale block_axiom \<subseteq> 
  voting_power_axiom domain semantics \<delta> "\<lambda>X \<gamma>. block_axiom_axioms X semantics \<gamma> block_model"
  by (unfold_locales)

sublocale null_player_axiom \<subseteq> 
  voting_power_axiom domain semantics \<delta> "\<lambda>X \<gamma>. null_player_axiom_axioms X semantics \<gamma>"
  by (unfold_locales)

end