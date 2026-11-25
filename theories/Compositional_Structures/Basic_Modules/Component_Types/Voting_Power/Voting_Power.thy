chapter \<open>Voting Power Definitions\<close>
theory Voting_Power
  imports Voting_Model
          "HOL-Probability.Probability_Measure"

begin

section \<open>Voting Power Definition\<close>

type_synonym ('x, 'v) Voting_Power = "'x \<Rightarrow> 'v \<Rightarrow> ereal"
type_synonym ('x, 'v) Voting_Power_Axiom = "('x, 'v) Voting_Power \<Rightarrow> bool"

section \<open>Voting Power Axioms\<close>

locale voting_power_axiom = voting_model domain semantics
  for domain :: "'\<tau> set" and semantics :: "('\<tau>, 'v, 'b, 'r) Voting_Rule_Transformation" +
  fixes \<Phi> :: "('\<tau>, 'v) Voting_Power_Axiom set"

sublocale voting_power_axiom \<subseteq> voting_model domain semantics
  by (rule local.voting_model_axioms)

fun (in voting_power_axiom) satisfies :: "('\<tau>, 'v) Voting_Power \<Rightarrow> bool" where
  "satisfies \<delta> = (\<forall>\<phi> \<in> \<Phi>. \<phi> \<delta>)"

fun (in voting_power_axiom) uniqueness_in :: "('\<tau>, 'v) Voting_Power set \<Rightarrow> bool" where
  "uniqueness_in X = 
    (\<forall>\<delta>1 \<in> X. \<forall> \<delta>2 \<in> X. satisfies \<delta>1 \<longrightarrow> satisfies \<delta>2 \<longrightarrow> (\<forall>m \<in> domain. \<delta>1 m = \<delta>2 m))"
  (* TODO require equality of the indices only on eligible voters? *)

section \<open>Concrete Axioms\<close>

fun diff :: "('x \<Rightarrow> 'y) \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> 'x set" where
  "diff f g = {x::'x |x. f x \<noteq> g x}"

type_synonym ('\<tau>, 'v, 'b) Swing_Vote = "'\<tau> \<Rightarrow> 'v \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool"

fun (in voting_model) swing_vote_predicate :: 
  "('\<tau>, 'v, 'b) Swing_Vote \<Rightarrow> bool" where
  "swing_vote_predicate sv = 
    (\<forall>a \<in> voting_structures. \<forall>v \<in> voters a. \<forall>p \<in> profiles a. sv a v p \<longrightarrow> 
      (\<exists>q \<in> profiles a. v \<in> diff p q \<and> aggregation a p \<noteq> aggregation a q))"

fun (in voting_model) swings :: "('\<tau>, 'v, 'b) Swing_Vote \<Rightarrow> '\<tau> \<Rightarrow> 'v \<Rightarrow> ('v, 'b) Profile set" where
  "swings sv m v = {p | p. p \<in> profiles m \<and> sv m v p}"

fun (in voting_model) null_player_ax :: "('\<tau>, 'v, 'b) Swing_Vote \<Rightarrow> ('\<tau>, 'v) Voting_Power_Axiom" 
  where "null_player_ax sv \<delta> = 
    (\<forall>m \<in> voting_structures. \<forall>v \<in> voters m. (sv m v = (\<lambda>p. False)) \<longrightarrow> \<delta> m v = 0)"

(* TODO why does this work, but directly inserting this 
    into the total_power_axiom function doesn't? *)
(* TODO require well-formedness of sv (profiles that coincide on V are mapped to the same value)  *)
fun (in voting_model) power_sum :: "('\<tau>, 'v) Voting_Power \<Rightarrow> '\<tau> \<Rightarrow> ereal" where
  "power_sum \<delta> m = (\<Sum>v \<in> voters m. \<delta> m v)"

locale null_player_axiom = voting_power_axiom domain semantics \<Phi>
  for domain :: "'\<tau> set" and semantics :: "('\<tau>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<Phi> +
  fixes
    sv :: "('\<tau>, 'v, 'b) Swing_Vote"
  assumes
    \<Phi>_np_def: "\<Phi> = {local.null_player_ax sv}" and
    swing_vote_predicate: "local.swing_vote_predicate sv"

sublocale null_player_axiom \<subseteq> voting_power_axiom
  by (rule local.voting_power_axiom_axioms)

fun (in voting_model) total_power_ax :: "('\<tau>, 'v, 'b) Swing_Vote \<Rightarrow> ('\<tau>, 'v) Voting_Power_Axiom"
  where "total_power_ax sv \<delta> =
    (\<forall>m \<in> voting_structures.
      power_sum \<delta> m =
      (\<Sum>v \<in> voters m. ereal (card (swings sv m v))) / (power (card_ball m) (card_vot m)))"

locale total_power_axiom = voting_power_axiom domain semantics \<Phi>
  for domain :: "'\<tau> set" and semantics :: "('\<tau>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<Phi> +
  fixes
    sv :: "('\<tau>, 'v, 'b) Swing_Vote"
  assumes
    \<Phi>_tp_def: "\<Phi> = {total_power_ax sv}" and
    swing_vote_predicate: "swing_vote_predicate sv"

type_synonym ('\<tau>, 'v) Voter_Renaming_Transform = "(('v \<Rightarrow> 'v) \<Rightarrow> '\<tau> \<Rightarrow> '\<tau>)"

fun (in voting_model) voter_renaming_transformation :: "('\<tau>, 'v) Voter_Renaming_Transform \<Rightarrow> bool" 
  where "voter_renaming_transformation \<Phi> = 
    (\<forall>m \<in> voting_structures. \<forall>\<sigma> :: 'v \<Rightarrow> 'v. bij \<sigma> \<longrightarrow> 
      \<Phi> \<sigma> m \<in> voting_structures \<longrightarrow> semantics (\<Phi> \<sigma> m) = rename_rule (semantics m) \<sigma>)"

fun (in voting_model) symmetry_ax :: 
  "('\<tau>, 'v) Voter_Renaming_Transform \<Rightarrow> ('\<tau>, 'v) Voting_Power_Axiom" where
  "symmetry_ax \<Phi> \<delta> = 
    (\<forall>m \<in> voting_structures. \<forall>\<sigma> :: 'v \<Rightarrow> 'v. 
      bij \<sigma> \<longrightarrow> \<Phi> \<sigma> m \<in> voting_structures \<longrightarrow> (\<forall>v \<in> voters m. \<delta> m v = \<delta> (\<Phi> \<sigma> m) (\<sigma> v)))"

locale symmetry_axiom = voting_power_axiom domain semantics \<Phi>
  for domain :: "'\<tau> set" and semantics :: "('\<tau>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<Phi> +
  fixes
    \<psi> :: "('\<tau>, 'v) Voter_Renaming_Transform" 
  assumes
    \<Phi>_sym_def: "\<Phi> = {symmetry_ax \<psi>}" and
    isomorphism_sane: "voter_renaming_transformation \<psi>"

fun rule_transform :: 
  "('v, 'b, 'r) Voting_Rule \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'r \<Rightarrow> ('v, 'b, 'r) Voting_Rule" where
  "rule_transform (V, B, R, f) p r = (V, B, R, (\<lambda>q. if (\<forall>v \<in> V. q v = p v) then r else f q))" 

lemma rule_transform_transforms: 
  fixes f :: "('v, 'b, 'r) Voting_Rule" and p :: "('v, 'b) Profile" and r :: 'r
  shows "rule (rule_transform f p r) p = r"
proof -
  have "f = (rule_voters f, rule_ballots f, rule_results f, rule f)"
    by simp
  hence 
    "rule (rule_transform f p r) p = (if (\<forall>v \<in> rule_voters f. p v = p v) then r else (rule f) p)"
    using rule_transform.simps[of "rule_voters f" "rule_ballots f" "rule_results f" "rule f" p r]
    by simp
  thus ?thesis
    by simp
qed

type_synonym ('\<tau>, 'v, 'b, 'r) Result_Transform = "('v, 'b) Profile \<Rightarrow> 'r \<Rightarrow> '\<tau> \<Rightarrow> '\<tau>"
type_synonym ('\<tau>, 'v, 'b) Profile_Reachability = "('v, 'b) Profile \<Rightarrow> 'v \<Rightarrow> ('v, 'b) Profile set"

text \<open>
  The voting rule of the result-transformed model must equal 
  the result-transformed voting rule of the original model.
  Note that a voting rule is only defined on its domain of profiles from V to B, 
  so we only consider its behaviour on that domain. This allows more flexible 
  definitions of transformations without changing the intended meaning.
\<close>
fun (in voting_model) result_based_transformation :: "('\<tau>, 'v, 'b, 'r) Result_Transform \<Rightarrow> bool" 
  where "result_based_transformation \<alpha> =
    (\<forall>m \<in> voting_structures. \<forall>p \<in> profiles m. \<forall>r \<in> results m.
        (let (V, B, R, f) = semantics (\<alpha> p r m) in
          (let (V', B', R', f') = rule_transform (semantics m) p r in
          V = V' \<and> B = B' \<and> R = R' \<and> (\<forall>q \<in> profiles m. f q = f' q)))
    )"

text \<open>
  The profiles impacted by changing p's result must be valid profiles and contain p.
\<close>
fun (in voting_model) profile_reachability :: "('\<tau>, 'v, 'b) Profile_Reachability \<Rightarrow> bool" where
  "profile_reachability \<beta> = 
    (\<forall>m \<in> voting_structures. \<forall>p \<in> profiles m. \<forall>v \<in> voters m. p \<in> \<beta> p v \<and> \<beta> p v \<subseteq> profiles m)"

text \<open>
  Whenever two models behave the same on profiles impacted by p, 
  the power shift caused by result-transforming p into r should be 
  equal for both models as well.
  When they do not behave the same, we make no requirements.
\<close>
fun (in voting_model) transfer_ax :: 
  "('\<tau>, 'v, 'b, 'r) Result_Transform \<Rightarrow> ('\<tau>, 'v, 'b) Profile_Reachability \<Rightarrow> 
    ('\<tau>, 'v) Voting_Power_Axiom" where
  "transfer_ax \<alpha> \<beta> \<delta> = 
    (\<forall>m \<in> voting_structures. \<forall>n \<in> voting_structures. 
      (voters m = voters n \<and> ballots m = ballots n \<and> results m = results n) \<longrightarrow> 
      (\<forall>p \<in> profiles m. \<forall>v \<in> voters m. \<forall>r \<in> results m.
        \<alpha> p r m \<in> voting_structures \<longrightarrow> \<alpha> p r n \<in> voting_structures \<longrightarrow>
        (\<forall>q \<in> \<beta> p v. rule (semantics m) q = rule (semantics n) q) \<longrightarrow> 
        \<delta> (\<alpha> p r m) v - \<delta> m v = \<delta> (\<alpha> p r n) v - \<delta> n v)
    )"

(* TODO require \<alpha> p r m \<in> voting_structures here or in result_transform predicate? *)

locale transfer_axiom = voting_power_axiom domain semantics \<Phi>
  for domain :: "'\<tau> set" and semantics :: "('\<tau>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<Phi> +
  fixes
    result_transform :: "('\<tau>, 'v, 'b, 'r) Result_Transform" and
    reachability :: "('\<tau>, 'v, 'b) Profile_Reachability" 
  assumes
    \<Phi>_tf_def: "\<Phi> = {transfer_ax result_transform reachability}" and
    result_transform: "result_based_transformation result_transform" and
    reachability: "profile_reachability reachability"

type_synonym ('\<tau>, 'v, 'x) Prob_Space = "'\<tau> \<Rightarrow> 'v \<Rightarrow> 'x measure"
type_synonym ('\<tau>, 'v, 'x) Event = "'\<tau> \<Rightarrow> 'v \<Rightarrow> 'x set"

fun (in voting_model) is_ipower :: 
  "('\<tau>, 'v, 'x) Prob_Space \<Rightarrow> ('\<tau>, 'v, 'x) Event \<Rightarrow> ('\<tau>, 'v) Voting_Power_Axiom" where
    "is_ipower \<Omega> \<A> \<delta> = (\<forall>m \<in> voting_structures. \<forall>v \<in> voters m. 
        \<delta> m v \<ge> 0 \<and> \<delta> m v = enn2ereal (emeasure (\<Omega> m v) (\<A> m v)))"

locale ipower_axiom = voting_power_axiom domain semantics \<Phi>
  for domain :: "'\<tau> set" and semantics :: "('\<tau>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<Phi> +
  fixes
    space :: "('\<tau>, 'v, 'x) Prob_Space" and
    event :: "('\<tau>, 'v, 'x) Event"
  assumes
    \<Phi>_ipow_def: "\<Phi> = {is_ipower space event}" and
    prob_space: "\<forall>m \<in> domain. \<forall>v \<in> voters m. prob_space (space m v)" and
    measurable_event: "\<forall>m \<in> domain. \<forall>v \<in> voters m. event m v \<in> sets (space m v)"

end