section \<open>Voting Power\<close>

theory Voting_Power
  imports Electoral_Module
          Distance                     
          "HOL-Probability.Probability_Measure"

begin

subsection \<open>Definitions\<close>

type_synonym ('a, 'v, 'r) Swing_Weight =
  "('a, 'v, 'r) Electoral_Module \<Rightarrow> ('a, 'v) Election \<Rightarrow> 'v \<Rightarrow> ereal"

type_synonym ('a, 'v, 'r) Voting_Power =
  "('a, 'v, 'r) Electoral_Module \<Rightarrow> ('a, 'v) Election set \<Rightarrow> 'v \<Rightarrow> ereal"

text \<open>Voting power as weighted sum over swing elections.\<close>
fun voting_power :: 
  "('a, 'v, 'r) Electoral_Module \<Rightarrow> ('a, 'v) Election set \<Rightarrow>
  ('a, 'v, 'r) Swing_Weight \<Rightarrow> 'v \<Rightarrow> ereal" where
  "voting_power f E weight v = (\<Sum> e \<in> E. weight f e v)"

fun coincide_except :: "('a, 'v) Election \<Rightarrow> ('a, 'v) Election \<Rightarrow> 'v \<Rightarrow> bool" where
  "coincide_except e1 e2 v = 
      (\<forall> w \<in> (voters_\<E> e1) - {v}. profile_\<E> e1 w = profile_\<E> e2 w)"

fun swing_votes :: 
  "('a, 'v, 'r) Electoral_Module \<Rightarrow> ('a, 'v) Election set \<Rightarrow> 'v \<Rightarrow> (('a, 'v) Election) rel" where
  "swing_votes f E v = {(e1, e2) \<in> E \<times> E. 
      fun\<^sub>\<E> f e1 \<noteq> fun\<^sub>\<E> f e2 \<and> voters_\<E> e1 = voters_\<E> e2 \<and> coincide_except e1 e2 v}"

fun discrete_dist :: "'x Distance" where
  "discrete_dist x y = (if (x = y) then 0 else 1)"

fun raw_weight :: 
  "'r Distance \<Rightarrow> ('a, 'v) Election set \<Rightarrow> ('a, 'v, 'r) Swing_Weight" where
  "raw_weight d E f e v = (\<Sum> (e1, e2) \<in> swing_votes f E v. 
    (discrete_dist e e1) * (d (fun\<^sub>\<E> f e1) (fun\<^sub>\<E> f e2)))"

text \<open>
  Raw power defines the weights of swing elections as the 
  total result distance achievable via swing voting.\<close>
fun raw_power :: "'r Distance \<Rightarrow> ('a, 'v, 'r) Voting_Power" where
  "raw_power d f E v = voting_power f E (raw_weight d E) v"

subsection \<open>Specific Power Indices\<close>

text \<open>
  A generalized Banzhaf can be taken to count the profiles where
  a voter has at least one swing vote, but also the swing votes.
  We count the profiles where v has at least one swing vote,
  aiming at a probabilistic interpretation as 
  "probability of having a swing vote".
\<close>
fun banzhaf_prob :: "('a, 'v, 'r) Voting_Power" where
  "banzhaf_prob f E v = 0" (* TODO!1!!111 *)

(* TODO this counts each swing vote separately, so the normalization doesn't make sense... *)
fun banzhaf\<^sub>r\<^sub>a\<^sub>w :: "('a, 'v, 'r) Voting_Power" where
  "banzhaf\<^sub>r\<^sub>a\<^sub>w f E v = (1/(ereal (card E))) * (raw_power discrete_dist f E v)"

text \<open>Identically distributed probability space.\<close>
locale idd_prob_space = prob_space +                   
  assumes "\<forall> S \<subseteq> space M. emeasure M S = (card S)/(card (space M))"

(* global_interpretation banzhaf_probability_space:
  prob_space "(\<Omega>::'a set, A, \<mu>)" *)

theorem banzhaf_is_probability:
  "True"
  sorry

lemma (in idd_prob_space) invar_func_imp_invar_prob:
   fixes
    f :: "'a \<Rightarrow> 'b" and
    S :: "'a set" and
    T :: "'c set" and
    \<phi> :: "('c, 'a) binary_fun"
  assumes "is_symmetry f (Invariance (action_induced_rel T S \<phi>))"
  shows "is_symmetry (emeasure M) 
          (Invariance (action_induced_rel UNIV UNIV (set_action \<phi>)))"
  (* TODO: Replace the UNIV's by sensible sets *)
  sorry

end