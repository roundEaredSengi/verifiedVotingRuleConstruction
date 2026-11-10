chapter \<open>Voting Power Comparison\<close>
theory Voting_Power_Comparison
  imports Voting_Power
          Voting_Model_Comparison

begin

section \<open>Auxiliary Definitions\<close>

fun rev_rel :: "('x \<Rightarrow> 'y \<Rightarrow> 'z) \<Rightarrow> ('y \<Rightarrow> 'x \<Rightarrow> 'z)" where
  "rev_rel f y x = f x y"

section \<open>Voting Power Comparison Properties\<close>

text \<open>
Two power indices are equivalent w.r.t. their domains 
if they yield identical power values for equivalent inputs.

Note that model equivalence implies voters1 m1 = voters2 m2, 
so choosing a v from the first set for both indices is fine.
\<close>
fun (in voting_model_comparison) power_equality :: 
  "('\<alpha>, 'v) Voting_Power \<Rightarrow> ('\<beta>, 'v) Voting_Power \<Rightarrow> bool" where
  "power_equality \<delta>1 \<delta>2 = (\<forall>m1 \<in> X1. \<forall>m2 \<in> X2. 
    model_equivalence m1 m2 \<longrightarrow> (\<forall>v \<in> rule_voters (semantics1 m1). \<delta>1 m1 v = \<delta>2 m2 v))"

section \<open>Voting Power Axiom Comparison\<close>

text \<open>
  We call two voting power axioms equivalent if they are defined on equivalent domains
  and they coincide for equivalent voting power indices.
  Since, inside the voting_power_comparison locale, the indices and their domains are fixed,
  we lose the quantifiers that this definition contains on paper.
  To use the quantified version of the definition, use it outside the locale context.
\<close>
locale voting_power_axiom_comparison = 
  comp: voting_model_comparison domain1 domain2 semantics1 semantics2 model_equivalence +
  axm1: voting_power_axiom domain1 semantics1 \<Phi>1 + axm2: voting_power_axiom domain2 semantics2 \<Phi>2
  for model_equivalence :: "'\<alpha> \<Rightarrow> '\<beta> \<Rightarrow> bool" and
      semantics1 :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and
      domain1 domain2 semantics2 \<Phi>1 \<Phi>2
  
definition (in voting_power_axiom_comparison) axiom_equivalence :: "bool" where 
  "axiom_equivalence = 
    (comp.domain_equivalence \<and> 
      (\<forall>\<delta>1 \<delta>2. comp.power_equality \<delta>1 \<delta>2 \<longrightarrow> axm1.satisfies \<delta>1 = axm2.satisfies \<delta>2))"

section \<open>Voting Power Axiom Comparison\<close>

subsection \<open>Null Player Axiom\<close>

locale null_player_comparison = 
  comp: voting_model_comparison domain1 domain2 semantics1 semantics2 model_equivalence +
  axm1: null_player_axiom domain1 semantics1 \<Phi>1 sv1 + 
  axm2: null_player_axiom domain2 semantics2 \<Phi>2 sv2
    for model_equivalence :: "'\<alpha> \<Rightarrow> '\<beta> \<Rightarrow> bool" and 
        semantics1 :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and 
        semantics2 domain1 domain2 \<Phi>1 \<Phi>2 sv1 sv2

sublocale null_player_comparison \<subseteq> voting_power_axiom_comparison
  unfolding voting_power_axiom_comparison_def
  by (metis comp.voting_model_comparison_axioms 
        axm2.voting_power_axiom_axioms axm1.voting_power_axiom_axioms)

theorem (in null_player_comparison) null_player_extension_helper:
  fixes 
    \<delta>1 :: "('\<alpha>, 'v) Voting_Power" and
    \<delta>2 :: "('\<beta>, 'v) Voting_Power"
  assumes
    equiv_pow: "comp.power_equality \<delta>1 \<delta>2" and
    np1: "axm1.satisfies \<delta>1" and
    equiv_domains: "comp.domain_equivalence" and
    equiv_swings: "\<forall>m \<in> domain1. \<forall>n \<in> domain2. model_equivalence m n \<longrightarrow> sv1 m = sv2 n"
  shows                    
    "axm2.satisfies \<delta>2"
proof (simp, safe)
  fix \<phi> :: "('\<beta>, 'v) Voting_Power_Axiom"
  assume "\<phi> \<in> \<Phi>2"
  hence "\<phi> = comp.mod2.null_player_ax sv2"
    using axm2.null_player_axiom_axioms
    unfolding null_player_axiom_def null_player_axiom_axioms_def
    by simp
  moreover have "comp.mod2.null_player_ax sv2 \<delta>2"
  proof (simp, safe)
    fix n :: '\<beta> and v :: 'v
    assume 
      n_in: "n \<in> domain2" and 
      v_vot: "v \<in> comp.mod2.voters n" and 
      null_player: "sv2 n v = (\<lambda>p. False)"
    then obtain m :: '\<alpha> where m_in: "m \<in> domain1" and equiv_mod: "model_equivalence m n"
      using equiv_domains
      unfolding comp.domain_equivalence_def
      by metis
    moreover with this have eq_vot: "comp.mod1.voters m = comp.mod2.voters n"
      using comp.voting_model_comparison_axioms n_in
      unfolding voting_model_comparison_def voting_model_comparison_axioms_def 
      by metis
    ultimately have eq_pow: "\<delta>2 n v = \<delta>1 m v"
      using equiv_pow v_vot n_in
      by simp
    moreover have "sv1 m v = (\<lambda>p. False)"
      using equiv_swings v_vot eq_vot n_in m_in equiv_mod null_player
      by metis
    moreover have "comp.mod1.null_player_ax sv1 \<delta>1"
      using np1 axm1.\<Phi>_np_def
      unfolding axm1.satisfies.simps
      by simp
    ultimately show "\<delta>2 n v = 0"
      using np1 m_in v_vot eq_vot
      by simp
  qed
  ultimately show "\<phi> \<delta>2"
    by meson
qed

theorem (in null_player_comparison) null_player_extension:
  assumes
    equiv_domains: comp.domain_equivalence and
    sw1: "comp.mod1.swing_vote_predicate sv1" and
    sw2: "comp.mod2.swing_vote_predicate sv2" and
    equiv_swings: "\<forall>m \<in> domain1. \<forall>n \<in> domain2. model_equivalence m n \<longrightarrow> sv1 m = sv2 n"
  shows 
    "axiom_equivalence"
proof (unfold axiom_equivalence_def, safe)
  show "comp.domain_equivalence" by (rule local.equiv_domains)
next
  fix 
    \<delta>1 :: "('\<alpha>, 'v) Voting_Power" and
    \<delta>2 :: "('\<beta>, 'v) Voting_Power"
  assume "comp.power_equality \<delta>1 \<delta>2" and "axm1.satisfies \<delta>1"
  thus "axm2.satisfies \<delta>2"
    using assms null_player_extension_helper[of \<delta>1 \<delta>2]
    by satx
next
  fix 
    \<delta>1 :: "('\<alpha>, 'v) Voting_Power" and
    \<delta>2 :: "('\<beta>, 'v) Voting_Power"
  assume equiv_pow: "comp.power_equality \<delta>1 \<delta>2" and np2: "axm2.satisfies \<delta>2"
  interpret role_swap:
    null_player_comparison 
      "rev_rel model_equivalence" semantics2 semantics1 domain2 domain1 \<Phi>2 \<Phi>1 sv2 sv1
    using null_player_comparison_axioms
    unfolding 
      null_player_comparison_def voting_model_comparison_def voting_model_comparison_axioms_def
    by simp
  have "role_swap.comp.power_equality \<delta>2 \<delta>1"
    using equiv_pow comp.equivalence_relation
    unfolding comp.power_equality.simps role_swap.comp.power_equality.simps rev_rel.simps
    by metis
  moreover have "role_swap.comp.domain_equivalence"
    using equiv_domains
    unfolding comp.domain_equivalence_def role_swap.comp.domain_equivalence_def
    by simp
  ultimately show "axm1.satisfies \<delta>1"
    using np2 sw1 sw2 equiv_swings role_swap.null_player_extension_helper[of \<delta>2 \<delta>1]
    by simp
qed

subsection \<open>Total Power Axiom\<close>

subsection \<open>Symmetry Axiom\<close>

subsection \<open>Transfer Axiom\<close>

locale transfer_comparison = 
  comp: voting_model_comparison domain1 domain2 semantics1 semantics2 model_equivalence +
  axm1: transfer_axiom domain1 semantics1 \<Phi>1 result_transform1 reachability1 + 
  axm2: transfer_axiom domain2 semantics2 \<Phi>2 result_transform2 reachability2
    for model_equivalence :: "'\<alpha> \<Rightarrow> '\<beta> \<Rightarrow> bool" and 
        semantics1 :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and 
        semantics2 domain1 domain2 \<Phi>1 \<Phi>2 
        result_transform1 result_transform2 reachability1 reachability2

sublocale transfer_comparison \<subseteq> voting_power_axiom_comparison
  unfolding voting_power_axiom_comparison_def
  by (metis comp.voting_model_comparison_axioms 
        axm2.voting_power_axiom_axioms axm1.voting_power_axiom_axioms)

theorem (in transfer_comparison) transfer_extension:
  assumes
    equiv_domains: comp.domain_equivalence and
    equiv_transform: 
      "\<forall>m \<in> domain1. \<forall>n \<in> domain2. \<forall>p \<in> comp.mod1.profiles m. \<forall>r \<in> comp.mod1.results m. 
        model_equivalence m n \<longrightarrow>
          model_equivalence (result_transform1 p r m) (result_transform2 p r n)"
  shows
    "axiom_equivalence"
proof (unfold axiom_equivalence_def, simp only: axm2.satisfies.simps, safe)
  show "comp.domain_equivalence" by (rule local.equiv_domains)
next
  fix 
    \<delta>1 :: "('\<alpha>, 'v) Voting_Power" and
    \<delta>2 :: "('\<beta>, 'v) Voting_Power" and
    \<phi> :: "('\<beta>, 'v) Voting_Power_Axiom"
  assume 
    eq_pow: "comp.power_equality \<delta>1 \<delta>2" and 
    "axm1.satisfies \<delta>1" and "\<phi> \<in> \<Phi>2"
  hence "\<phi> \<delta>2 = comp.mod2.transfer_ax result_transform2 reachability2 \<delta>2"
    using axm2.transfer_axiom_axioms 
    unfolding transfer_axiom_def transfer_axiom_axioms_def
    by simp
  moreover have "comp.mod2.transfer_ax result_transform2 reachability2 \<delta>2"
  proof (simp, safe)
    fix m :: '\<beta> and n :: '\<beta> and p :: "('v, 'b) Profile" and v :: 'v and r :: 'r
    assume "m \<in> domain2" and "n \<in> domain2" and 
      prof: "p \<in> comp.mod2.voters n \<rightarrow> comp.mod2.ballots n" and
      vot_v: "v \<in> comp.mod2.voters n" and 
      res: "r \<in> comp.mod2.results n" and
      eq_m_n_vot: "comp.mod2.voters m = comp.mod2.voters n" and
      eq_m_n_ball: "comp.mod2.ballots m = comp.mod2.ballots n" and
      eq_m_n_res: "comp.mod2.results m = comp.mod2.results n" and
      eq_m_n_aggr: "\<forall> q \<in> reachability2 p v. comp.mod2.aggregation m q = comp.mod2.aggregation n q"
    (* TODO pairwise equality of domain components/profile sets *)
    then obtain m' :: '\<alpha> and n' :: '\<alpha> 
      where m_in: "m' \<in> domain1" and equiv_mod_m: "model_equivalence m' m" and
        n_in: "n' \<in> domain1" and equiv_mod_n: "model_equivalence n' n"
      using equiv_domains
      unfolding comp.domain_equivalence_def
      by metis
    hence eq_vot: 
      "comp.mod1.voters m' = comp.mod2.voters m \<and> comp.mod1.voters n' = comp.mod2.voters n"
      using comp.voting_model_comparison_axioms n_in m_in \<open>m \<in> domain2\<close> \<open>n \<in> domain2\<close>
      unfolding voting_model_comparison_def voting_model_comparison_axioms_def 
      by presburger
    moreover have eq_res: 
      "comp.mod1.results m' = comp.mod2.results m \<and> comp.mod1.results n' = comp.mod2.results n"
      using equiv_mod_m equiv_mod_n comp.voting_model_comparison_axioms 
              n_in m_in \<open>m \<in> domain2\<close> \<open>n \<in> domain2\<close>
      unfolding voting_model_comparison_def voting_model_comparison_axioms_def
      by metis
    ultimately have eq_domains:
      "p \<in> comp.mod1.profiles m' \<and> r \<in> comp.mod1.results m' \<and>
        p \<in> comp.mod1.profiles n' \<and> r \<in> comp.mod1.results n'"
      using prof res eq_m_n_vot eq_m_n_ball eq_m_n_res
      sorry
    hence
      "model_equivalence (result_transform1 p r m') (result_transform2 p r m)" and
      "model_equivalence (result_transform1 p r n') (result_transform2 p r n)"
      using assms equiv_mod_m equiv_mod_n \<open>m \<in> domain2\<close> \<open>n \<in> domain2\<close> m_in n_in 
      by (blast, blast)
    moreover with this have 
      "v \<in> comp.mod1.voters (result_transform1 p r m')" and 
      "v \<in> comp.mod1.voters (result_transform1 p r n')"
      sorry
    moreover have "result_transform2 p r m \<in> domain2" and "result_transform2 p r n \<in> domain2"
      using \<open>m \<in> domain2\<close> \<open>n \<in> domain2\<close>
            axm1.transfer_axiom_axioms axm2.transfer_axiom_axioms 
      unfolding transfer_axiom_def transfer_axiom_axioms_def
                comp.mod2.result_based_transformation.simps
      sorry
    ultimately have 
      "\<delta>2 (result_transform2 p r m) v = \<delta>1 (result_transform1 p r m') v" and
      "\<delta>2 (result_transform2 p r n) v = \<delta>1 (result_transform1 p r n') v"
      using eq_pow \<open>m \<in> domain2\<close> \<open>n \<in> domain2\<close> m_in n_in
      unfolding comp.power_equality.simps
      sorry
    thus "\<delta>2 (result_transform2 p r m) v - \<delta>2 m v = \<delta>2 (result_transform2 p r n) v - \<delta>2 n v"
      sorry
  qed
  ultimately show "\<phi> \<delta>2"
    by metis
next
  (* TODO make lemma out of one direction, then apply it for both *)
  show "\<And>\<delta>1 \<delta>2. comp.power_equality \<delta>1 \<delta>2 \<Longrightarrow> \<forall>\<phi>\<in>\<Phi>2. \<phi> \<delta>2 \<Longrightarrow> axm1.satisfies \<delta>1"
    sorry
qed

end