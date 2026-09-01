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
  "power_equality = (\<forall>m1 \<in> domain1. \<forall>m2 \<in> domain2. 
    model_equivalence m1 m2 \<longrightarrow> (\<forall>v \<in> rule_voters (semantics1 m1). \<delta>1 m1 v = \<delta>2 m2 v))"

section \<open>Voting Power Axiom Comparison Second Try\<close>

text \<open>
  We call two voting power axioms equivalent if they are defined on equivalent domains
  and they coincide for equivalent voting power indices.
  Since, inside the voting_power_comparison locale, the indices and their domains are fixed,
  we lose the quantifiers that this definition contains on paper.
  To use the quantified version of the definition, use it outside the locale context.
\<close>
fun (in voting_power_comparison) axiom_equivalence :: 
  "(('\<alpha>, 'v) Voting_Power_Axiom) \<Rightarrow> (('\<beta>, 'v) Voting_Power_Axiom) \<Rightarrow> bool" where 
  "axiom_equivalence \<phi>1 \<phi>2 = (comp.domain_equivalence \<and> (power_equality \<longrightarrow> \<phi>1 \<delta>1 = \<phi>2 \<delta>2))"

end