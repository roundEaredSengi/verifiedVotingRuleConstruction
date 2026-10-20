chapter \<open>Voting Power Comparison\<close>
theory Voting_Power_Comparison
  imports Voting_Power
          Voting_Model_Comparison

begin

section \<open>Auxiliary Definitions\<close>

fun rev_rel :: "('x \<Rightarrow> 'y \<Rightarrow> 'z) \<Rightarrow> ('y \<Rightarrow> 'x \<Rightarrow> 'z)" where
  "rev_rel f y x = f x y"

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

section \<open>Voting Power Axiom Comparison\<close>

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

section \<open>Voting Power Axiom Comparison\<close>

subsection \<open>Null Player Axiom\<close>

theorem (in voting_power_comparison) null_player_extension_helper:
  assumes
    equiv_pow: "power_equality" and 
    sw1: "pow1.swing_vote_predicate swing1" and
    sw2: "pow2.swing_vote_predicate swing2" and
    np1: "null_player_axiom domain1 semantics1 \<delta>1 swing1" and
    equiv_domains: comp.domain_equivalence and
    equiv_swings: "\<forall>m \<in> domain1. \<forall>n \<in> domain2. model_equivalence m n \<longrightarrow> swing1 m = swing2 n"
  shows 
    "null_player_axiom domain2 semantics2 \<delta>2 swing2"
proof 
  (unfold null_player_axiom_def null_player_axiom_axioms_def, safe)
  show "voting_power domain2 semantics2"
    by (rule local.pow2.voting_power_axioms)
next
  show "pow2.swing_vote_predicate swing2"
    by (rule sw2)
next
  fix n :: '\<beta> and v :: 'v
  assume 
    n_in: "n \<in> domain2" and 
    v_vot: "v \<in> pow2.voters n" and 
    null_player: "swing2 n v = (\<lambda>p. False)"
  then obtain m :: '\<alpha> where m_in: "m \<in> domain1" and equiv_mod: "model_equivalence m n"
    using equiv_domains
    unfolding comp.domain_equivalence_def
    by metis
  moreover with this have eq_vot: "pow1.voters m = pow2.voters n"
    using comp.voting_model_comparison_axioms n_in
    unfolding voting_model_comparison_def voting_model_comparison_axioms_def 
    by metis
  ultimately have eq_pow: "\<delta>2 n v = \<delta>1 m v"
    using equiv_pow v_vot n_in
    unfolding power_equality_def
    by metis
  moreover have "swing1 m v = (\<lambda>p. False)"
    using equiv_swings v_vot eq_vot n_in m_in equiv_mod null_player
    by metis
  ultimately show "\<delta>2 n v = 0"
    using np1 m_in v_vot eq_vot
    unfolding null_player_axiom_def null_player_axiom_axioms_def
    by metis
qed  

theorem (in voting_power_comparison) null_player_extension:
  assumes
    equiv_domains: comp.domain_equivalence and
    sw1: "pow1.swing_vote_predicate swing1" and
    sw2: "pow2.swing_vote_predicate swing2" and
    equiv_swings: "\<forall>m \<in> domain1. \<forall>n \<in> domain2. model_equivalence m n \<longrightarrow> swing1 m = swing2 n"
  shows 
    "axiom_equivalence
      (\<lambda>\<delta>. null_player_axiom domain1 semantics1 \<delta>1 swing1) 
      (\<lambda>\<delta>. null_player_axiom domain2 semantics2 \<delta>2 swing2)"
proof (unfold axiom_equivalence.simps, safe)
  show "comp.domain_equivalence" by (rule local.equiv_domains)
next
  assume "power_equality" and "null_player_axiom domain1 semantics1 \<delta>1 swing1"
  thus "null_player_axiom domain2 semantics2 \<delta>2 swing2"
    using assms null_player_extension_helper[of swing1 swing2]
    by satx
next
  assume equiv_pow: "power_equality" and np2: "null_player_axiom domain2 semantics2 \<delta>2 swing2"
  interpret role_swap:
    voting_power_comparison "rev_rel model_equivalence" domain2 semantics2 \<delta>2 domain1 semantics1 \<delta>1
    using voting_power_comparison_axioms
    unfolding 
      voting_power_comparison_def voting_model_comparison_def voting_model_comparison_axioms_def
    by simp
  have "role_swap.power_equality"
    using equiv_pow comp.equivalence_relation
    unfolding power_equality_def role_swap.power_equality_def rev_rel.simps
    by presburger
  moreover have "role_swap.comp.domain_equivalence"
    using equiv_domains
    unfolding comp.domain_equivalence_def role_swap.comp.domain_equivalence_def
    by simp
  ultimately show "null_player_axiom domain1 semantics1 \<delta>1 swing1"
    using np2 sw1 sw2 equiv_swings role_swap.null_player_extension_helper[of swing2 swing1]
    by simp
qed

subsection \<open>Total Power Axiom\<close>

subsection \<open>Symmetry Axiom\<close>

subsection \<open>Transfer Axiom\<close>

end