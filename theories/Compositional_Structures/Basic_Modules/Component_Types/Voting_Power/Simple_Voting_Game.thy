chapter \<open>Simple Voting Games\<close>

theory Simple_Voting_Game
  imports Voting_Model
          Voting_Power

begin                           

section \<open>Simple Voting Game Definition\<close>

text \<open>
A simple voting game is a tuple consisting of a set (of voters) 
and a set family (of voter coalitions).
\<close>
type_synonym 'v Simple_Voting_Game = "'v set \<times> ('v set set)"

abbreviation coalitions :: "'v Simple_Voting_Game \<Rightarrow> 'v set set" where
  "coalitions G \<equiv> snd G"  

fun aggregation_method :: 
  "'b \<Rightarrow> 'b \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> (('v \<Rightarrow> 'b) \<Rightarrow> 'r)" where
  "aggregation_method ball1 ball2 res1 res2 (V, \<F>) p = 
    (if (preimg_in V p {ball1} \<in> \<F>) then res1 else res2)" (* TODO require p to be valid *)

definition valid_simple_voting_games :: "'v Simple_Voting_Game set" where
  "valid_simple_voting_games = {G | G. snd G \<subseteq> Pow (fst G)}"

fun monotone_SVG :: "'v Simple_Voting_Game \<Rightarrow> bool" where
  "monotone_SVG (V, \<F>) = (\<forall>S \<in> Pow V. \<forall>T \<in> Pow V. S \<subseteq> T \<longrightarrow> S \<in> \<F> \<longrightarrow> T \<in> \<F>)"

definition monotone_SVGs :: "'v Simple_Voting_Game set" where
  "monotone_SVGs \<equiv> {G | G. G \<in> valid_simple_voting_games \<and> monotone_SVG G}"

section \<open>Simple Voting Games as a Voting Model\<close> 

fun svg_rule :: 
  "'b \<Rightarrow> 'b \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> ('v Simple_Voting_Game, 'v, 'b, 'r) Voting_Rule_Transformation" where
  "svg_rule b1 b2 r1 r2 (V, \<F>) = (V, {b1, b2}, {r1, r2}, aggregation_method b1 b2 r1 r2 (V, \<F>))"

\<comment> \<open>
  The simple voting game model represents voting systems via objects of type Simple_Voting_Game.
  Simple voting games represent binary decisions on two ballots and two results.
\<close>
locale simple_voting_game_model = 
  mod: voting_model S "svg_rule ballot1 ballot2 result1 result2"
    for S :: "'v Simple_Voting_Game set" and
      ballot1 :: 'a and ballot2 :: 'a and result1 :: 'b and result2 :: 'b +
    assumes "result1 \<noteq> result2" and "ballot1 \<noteq> ballot2" and "\<forall>G \<in> S. snd G \<subseteq> Pow (mod.voters G)"

sublocale simple_voting_game_model \<subseteq> 
  voting_model S "svg_rule ballot1 ballot2 result1 result2"
  by unfold_locales

context simple_voting_game_model
begin

abbreviation "svg_voters \<equiv> rule_voters \<circ> (svg_rule ballot1 ballot2 result1 result2)"
lemma svg_voters_fst [simp]: "svg_voters = fst"
  by auto

abbreviation "svg_ballots \<equiv> rule_ballots \<circ> (svg_rule ballot1 ballot2 result1 result2)"
abbreviation "svg_results \<equiv> rule_results \<circ> (svg_rule ballot1 ballot2 result1 result2)"
abbreviation "svg_aggregation \<equiv> rule \<circ> (svg_rule ballot1 ballot2 result1 result2)"

fun svg_profile :: "'v Simple_Voting_Game \<Rightarrow> 'v set \<Rightarrow> ('v, 'a) Profile" where
  "svg_profile (V, \<F>) X = (\<lambda>v. (if v \<in> X then ballot1 else ballot2))"

end

\<comment> \<open>
Models yes-no-decisions: 
Voters choose one out of True (= yes) and False (= no) and the result is True (= yes) iff
a winning coalition of voters chose yes, otherwise the result is False (= no).
\<close>
interpretation boolean_svg:
  simple_voting_game_model valid_simple_voting_games True False True False
proof (unfold_locales, simp_all, safe)
  fix V :: "'a set" and \<F> :: "'a set set" and p :: "('a, bool) Profile"
  assume "p \<in> rule_voters (svg_rule True False True False (V, \<F>)) 
                \<rightarrow> rule_ballots (svg_rule True False True False (V, \<F>))"
  hence "rule (svg_rule True False True False (V, \<F>)) p \<in> {True, False}"
    by simp
  thus "rule (svg_rule True False True False (V, \<F>)) p
          \<in> rule_results (svg_rule True False True False (V, \<F>))"
    by simp
next
  fix V :: "'a set" and \<F> :: "'a set set" and X :: "'a set" and v :: 'a
  assume "(V, \<F>) \<in> valid_simple_voting_games" and "X \<in> coalitions (V, \<F>)" and "v \<in> X"
  thus "v \<in> rule_voters (svg_rule True False True False (V, \<F>))"
    unfolding valid_simple_voting_games_def
    by auto
qed

section \<open>Simple Voting Game Parameters\<close>

fun svg_isomorphism :: "('v \<Rightarrow> 'v) \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "svg_isomorphism \<pi> (V, \<F>) = (\<pi> ` V, (image \<pi>) ` \<F>)"

fun svg_meet :: "'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "svg_meet G1 G2 = (fst G1, coalitions G1 \<union> coalitions G2)"

fun (in simple_voting_game_model) svg_join :: 
  "'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "svg_join G1 G2 = (fst G1, coalitions G1 \<inter> coalitions G2)"

fun (in simple_voting_game_model) svg_swings :: 
  "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'a) set" where
  "svg_swings (V, \<F>) v = {svg_profile (V, \<F>) X | X. X \<subseteq> V \<and> ((X \<union> {v}) \<in> \<F>) \<noteq> ((X - {v}) \<in> \<F>)}"

fun (in simple_voting_game_model) svg_swing :: 
  "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> bool" where
  "svg_swing G v p = (p \<in> svg_swings G v)"

fun (in simple_voting_game_model) \<Phi>_svg :: 
  "('v \<Rightarrow> 'v) \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "\<Phi>_svg \<sigma> (V, \<F>) = (\<sigma> ` V, {\<sigma> ` C |C. C \<in> \<F>})"

fun (in simple_voting_game_model) alpha_svg :: 
  "('v \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "alpha_svg p r (V, \<F>) = (let C = preimg_in V p {ballot1} in 
    (
      (if r = ballot1 \<and> C \<in> \<F> then (V, \<F> - {C}) else (V, \<F>)) 
    ))" (* TODO the other cases *)

section \<open>Simple Voting Game Voting Power\<close>

locale svg_power = svg: simple_voting_game_model S b1 b2 r1 r2
  for S :: "'v Simple_Voting_Game set" and b1 :: 'b and b2 and r1 :: 'r and r2 +
  fixes
    \<delta> :: "('v Simple_Voting_Game, 'v) Voting_Power"

sublocale svg_power \<subseteq> voting_power S "svg_rule b1 b2 r1 r2" \<delta>
  using svg.mod.voting_model_axioms voting_power_def 
  by blast

(* TODO: make case distinction less repetitive, close "sorry"s *)
theorem (in svg_power) svg_swing_is_predicate:
  "swing_vote_predicate svg.svg_swing"
proof (simp, safe)
  fix V :: "'v set" and \<F> :: "'v set set" and v :: 'v and p :: "'v \<Rightarrow> 'b"
  assume 
    valid: "(V, \<F>) \<in> S" and 
    vot_v: "v \<in> svg.mod.voters (V, \<F>)" and 
    valid_prof: "p \<in> svg.mod.voters (V, \<F>) \<rightarrow> svg.mod.ballots (V, \<F>)" and
    swing: "p \<in> svg.svg_swings (V, \<F>) v"
  then obtain C :: "'v set" where 
    coal_p: "p = svg.svg_profile (V, \<F>) C"
    by auto
  hence preimg_p: "preimg_in V p {b1} = C"
    sorry
  let ?thesis = 
    "\<exists>q\<in>svg.mod.voters (V, \<F>) \<rightarrow> svg.mod.ballots (V, \<F>).
          p v \<noteq> q v \<and> svg.mod.aggregation (V, \<F>) p \<noteq> svg.mod.aggregation (V, \<F>) q"
  show ?thesis
  proof (cases "p v = b1")
    case True
    hence "v \<in> C"
      using coal_p
      unfolding svg.svg_profile.simps
      by (metis simple_voting_game_model_axioms_def simple_voting_game_model_def
          svg.simple_voting_game_model_axioms)
    hence "C = C \<union> {v}"
      by auto
    moreover have "\<forall>C' \<subseteq> V. C' \<noteq> C \<longrightarrow> p \<noteq> svg.svg_profile (V, \<F>) C'"
      using coal_p
      unfolding svg.svg_profile.simps
      by (metis simple_voting_game_model_axioms_def simple_voting_game_model_def 
          subsetI subset_antisym svg.simple_voting_game_model_axioms)
    moreover have "\<exists>C' \<subseteq> V. p = svg.svg_profile (V, \<F>) C' \<and> (C' \<union> {v} \<in> \<F>) \<noteq> (C' - {v} \<in> \<F>)"
      using swing
      by auto
    ultimately have swing_minus_v: "(C \<in> \<F>) \<noteq> (C - {v} \<in> \<F>)"
      using swing coal_p
      by metis
    let ?q = "svg.svg_profile (V, \<F>) (C - {v})"
    have preimg_q: "preimg_in V ?q {b1} = C - {v}"
      using preimg_p True
      sorry
    have neq: "?q v = b2"
      by simp
        have "svg.mod.aggregation (V, \<F>) p = rule (svg_rule b1 b2 r1 r2 (V, \<F>)) p"
      by simp
    moreover have "svg.mod.aggregation (V, \<F>) ?q = rule (svg_rule b1 b2 r1 r2 (V, \<F>)) ?q"
      by simp
    moreover have "(if C \<in> \<F> then r1 else r2) \<noteq> (if C - {v} \<in> \<F> then r1 else r2)"
      using swing_minus_v
      by (metis simple_voting_game_model_axioms_def simple_voting_game_model_def
          svg.simple_voting_game_model_axioms)
    moreover with this have 
      "rule (svg_rule b1 b2 r1 r2 (V, \<F>)) p \<noteq> rule (svg_rule b1 b2 r1 r2 (V, \<F>)) ?q"
      using preimg_p preimg_q
      unfolding svg_rule.simps aggregation_method.simps
      by simp
    ultimately have "svg.mod.aggregation (V, \<F>) p \<noteq> svg.mod.aggregation (V, \<F>) ?q"
      by satx
    moreover have "?q \<in> svg.mod.voters (V, \<F>) \<rightarrow> svg.mod.ballots (V, \<F>)"
      by simp
    moreover have "p v \<noteq> ?q v"
      using neq True
      by (metis simple_voting_game_model_axioms_def simple_voting_game_model_def
          svg.simple_voting_game_model_axioms)
    ultimately show ?thesis by metis
  next
    case False
    moreover have "p v \<in> {b1, b2}"
      using valid_prof
      unfolding Pi_def
      by (metis coal_p insertCI svg.svg_profile.simps)
    ultimately have "p v = b2"
      by simp
    hence "v \<notin> C"
      using coal_p
      unfolding svg.svg_profile.simps
      by (metis simple_voting_game_model_axioms_def simple_voting_game_model_def
          svg.simple_voting_game_model_axioms)
    hence "C = C - {v}"
      by auto
    moreover have "\<forall>C' \<subseteq> V. C' \<noteq> C \<longrightarrow> p \<noteq> svg.svg_profile (V, \<F>) C'"
      using coal_p
      unfolding svg.svg_profile.simps
      by (metis simple_voting_game_model_axioms_def simple_voting_game_model_def 
          subsetI subset_antisym svg.simple_voting_game_model_axioms)
    moreover have "\<exists>C' \<subseteq> V. p = svg.svg_profile (V, \<F>) C' \<and> (C' \<union> {v} \<in> \<F>) \<noteq> (C' - {v} \<in> \<F>)"
      using swing
      by auto
    ultimately have swing_plus_v: "(C \<union> {v} \<in> \<F>) \<noteq> (C \<in> \<F>)"
      using swing coal_p
      by metis
    let ?q = "svg.svg_profile (V, \<F>) (C \<union> {v})"
    have preimg_q: "preimg_in V ?q {b1} = C \<union> {v}"
      using preimg_p False
      sorry
    have neq: "?q v = b1"
      by simp
        have "svg.mod.aggregation (V, \<F>) p = rule (svg_rule b1 b2 r1 r2 (V, \<F>)) p"
      by simp
    moreover have "svg.mod.aggregation (V, \<F>) ?q = rule (svg_rule b1 b2 r1 r2 (V, \<F>)) ?q"
      by simp
    moreover have "(if C \<union> {v} \<in> \<F> then r1 else r2) \<noteq> (if C \<in> \<F> then r1 else r2)"
      using swing_plus_v
      by (metis simple_voting_game_model_axioms_def simple_voting_game_model_def
          svg.simple_voting_game_model_axioms)
    moreover with this have 
      "rule (svg_rule b1 b2 r1 r2 (V, \<F>)) p \<noteq> rule (svg_rule b1 b2 r1 r2 (V, \<F>)) ?q"
      using preimg_p preimg_q
      unfolding svg_rule.simps aggregation_method.simps
      by simp
    ultimately have "svg.mod.aggregation (V, \<F>) p \<noteq> svg.mod.aggregation (V, \<F>) ?q"
      by satx
    moreover have "?q \<in> svg.mod.voters (V, \<F>) \<rightarrow> svg.mod.ballots (V, \<F>)"
      by simp
    moreover have "p v \<noteq> ?q v"
      using neq False
      by metis
    ultimately show ?thesis by metis
  qed
qed

end